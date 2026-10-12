(* Bytes, and the encoding that carries a byte sequence into a Rocq source file
   (stage 6; Json.v's crjoin/string chunks are kept beside it).

   A represented text is a list of chunks, a chunk a list of pieces:
     PS s   a run of plain bytes written as a string literal s.  A byte b is plain
            when 32 <= b <= 126, b <> 34 (quote) and b <> 92 (backslash): such a
            literal holds no quote, no backslash, no CR, no LF and no other control
            byte, so nothing in it is translated by the Rocq lexer;
     PB b   one byte given by its constructor x00 .. xff of Init.Byte.  CR is PB x0d,
            LF is PB x0a, the quote PB x22, the backslash PB x5c, the tab PB x09.
   dec t          the bytes of t: the chunks in order, the pieces of each chunk in
                  order; nothing is inserted at a chunk boundary or between pieces,
                  so a CR ending one chunk and an LF starting the next are the pair
                  CR LF of the text.
   enc K bs       the canonical encoding: chunks of exactly K bytes except the last
                  (1 .. K bytes), in each chunk the maximal runs of plain bytes as PS
                  and every other byte as PB.
   dec_enc        0 < K -> dec (enc K bs) = bs, and size (dec (enc K bs)) = size bs.
   chunks_chunked / chunked_chunks   the chunk boundaries are exactly every K bytes;
   encc_runs / runs_encc             the pieces of a chunk are determined by its bytes;
   canon K t      enc K (dec t) == t, decided by computation: t is the canonical
                  encoding of the bytes it represents.
   dlen t         the number of represented bytes as a binary number (dlenE).
   digest bs      a fold of the bytes modulo 2^61 - 1.  The kernel computes it on the
                  represented bytes and pmp/vcheck2.pmp on the disk file; equal values
                  are a cross-check, not a proof that the two byte sequences agree. *)
From Stdlib Require Import String Ascii NArith.
From Stdlib Require Import Init.Byte.
From Stdlib Require Strings.Byte.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- bytes ---- *)
Lemma byte_eqP : Equality.axiom Strings.Byte.eqb.
Proof.
move=> a b; apply: (iffP idP) => [|->]; first exact: Strings.Byte.byte_dec_bl.
exact: Strings.Byte.byte_dec_lb.
Qed.
HB.instance Definition _ := hasDecEq.Build byte byte_eqP.

Definition bnat (b : byte) : nat := Strings.Byte.to_nat b.

(* the size of a list, tail-recursively (the machine evaluating the kernel's vm_compute
   keeps no stack frame per element) *)
Fixpoint count_from (T : Type) (a : nat) (s : seq T) : nat :=
  if s is _ :: r then count_from a.+1 r else a.

Lemma count_fromE (T : Type) a (s : seq T) : count_from a s = a + size s.
Proof. by elim: s a => [|x s ih] a /=; rewrite ?addn0 // ih addSnnS. Qed.

Fixpoint bytes_of_str (s : string) : seq byte :=
  if s is String a r then byte_of_ascii a :: bytes_of_str r else [::].
Fixpoint str_of_bytes (bs : seq byte) : string :=
  if bs is b :: r then String (ascii_of_byte b) (str_of_bytes r) else EmptyString.

Lemma str_of_bytesK : cancel str_of_bytes bytes_of_str.
Proof. by elim=> [|b r ih] //=; rewrite byte_of_ascii_of_byte ih. Qed.

Lemma bytes_of_strK : cancel bytes_of_str str_of_bytes.
Proof. by elim=> [|a r ih] //=; rewrite ascii_of_byte_of_ascii ih. Qed.

Lemma size_bytes_of_str s : size (bytes_of_str s) = String.length s.
Proof. by elim: s => [|a s ih] //=; rewrite ih. Qed.

Definition plain (b : byte) : bool :=
  [&& 32 <= bnat b, bnat b <= 126, b != x22 & b != x5c].

(* ---- pieces, chunks, texts ---- *)
Inductive piece : Type := PS of string | PB of byte.

Definition piece_eqb (p q : piece) : bool :=
  match p, q with
  | PS s, PS s' => String.eqb s s'
  | PB b, PB b' => b == b'
  | _, _ => false
  end.

Lemma piece_eqP : Equality.axiom piece_eqb.
Proof.
case=> [s|b] [s'|b'] /=; try by constructor.
- by apply: (iffP idP) => [/String.eqb_eq -> | [->]] //; apply/String.eqb_eq.
- by apply: (iffP eqP) => [-> | [->]].
Qed.
HB.instance Definition _ := hasDecEq.Build piece piece_eqP.

Definition pbytes (p : piece) : seq byte :=
  match p with PS s => bytes_of_str s | PB b => [:: b] end.
Definition cbytes (c : seq piece) : seq byte := flatten (map pbytes c).
Definition dec (t : seq (seq piece)) : seq byte := flatten (map cbytes t).

(* ---- the canonical encoding of one chunk ---- *)
Fixpoint encc (bs : seq byte) : seq piece :=
  if bs is b :: r then
    (if plain b then
       (match encc r with
        | PS s :: ps => PS (String (ascii_of_byte b) s) :: ps
        | ps => PS (String (ascii_of_byte b) EmptyString) :: ps
        end)
     else PB b :: encc r)
  else [::].

Lemma cbytes_cons p c : cbytes (p :: c) = pbytes p ++ cbytes c.
Proof. by []. Qed.

Lemma cbytes_encc bs : cbytes (encc bs) = bs.
Proof.
elim: bs => [|b r ih] //=; case: ifP => pb; last by rewrite cbytes_cons ih.
move: ih; case: (encc r) => [|[s|b'] ps] ih.
- by rewrite cbytes_cons /= byte_of_ascii_of_byte -ih.
- by rewrite cbytes_cons /= byte_of_ascii_of_byte -ih.
- by rewrite cbytes_cons /= byte_of_ascii_of_byte -ih.
Qed.

(* the pieces of a chunk are determined by its bytes *)
Definition headPS (ps : seq piece) : bool := if ps is PS _ :: _ then true else false.

Fixpoint runs_ok (ps : seq piece) : bool :=
  if ps is p :: ps' then
    (match p with
     | PS s => [&& 0 < String.length s, all plain (bytes_of_str s) & ~~ headPS ps']
     | PB b => ~~ plain b
     end) && runs_ok ps'
  else true.

Lemma encc_runs bs : runs_ok (encc bs).
Proof.
elim: bs => [|b r ih] //=; case: ifP => pb /=; last by rewrite pb ih.
move: ih; case: (encc r) => [|[s|b'] ps] //=.
- by rewrite byte_of_ascii_of_byte pb.
- by case/andP=> /and3P [_ -> ->] ->; rewrite byte_of_ascii_of_byte pb.
- by move=> /andP [-> ->]; rewrite byte_of_ascii_of_byte pb.
Qed.

Lemma runs_encc ps : runs_ok ps -> encc (cbytes ps) = ps.
Proof.
elim: ps => [|p ps ih] // /andP [hp hr]; have {}ih := ih hr.
rewrite cbytes_cons; case: p hp => [s|b] hp; last first.
  by move: hp => /= hp; rewrite (negbTE hp) ih.
case/and3P: hp => ls pls nh; rewrite [pbytes _]/=.
elim: s ls pls => [|a s ihs] // _ /andP [pa pls].
rewrite [bytes_of_str _]/= cat_cons [encc _]/= pa ascii_of_byte_of_ascii.
case: s ihs pls => [|a' s'] ihs pls.
  by rewrite [bytes_of_str _]/= cat0s ih; case: ps nh {ih hr ihs} => [|[s0|b0] l].
by rewrite ihs.
Qed.

(* ---- chunk boundaries ---- *)
Fixpoint chunkf (f K : nat) (bs : seq byte) : seq (seq byte) :=
  if f is f'.+1 then
    (if bs is [::] then [::] else take K bs :: chunkf f' K (drop K bs))
  else [::].
Definition chunks (K : nat) (bs : seq byte) : seq (seq byte) := chunkf (count_from 0 bs) K bs.
Definition enc (K : nat) (bs : seq byte) : seq (seq piece) := map encc (chunks K bs).

(* every chunk has exactly K bytes except the last, which has 1 .. K bytes *)
Fixpoint chunked (K : nat) (cs : seq (seq byte)) : bool :=
  match cs with
  | [::] => true
  | [:: c] => (0 < size c) && (size c <= K)
  | c :: cs' => (size c == K) && chunked K cs'
  end.

Lemma chunked1 K (x : seq byte) : chunked K [:: x] = (0 < size x) && (size x <= K).
Proof. by []. Qed.

Lemma chunked_cons2 K (x c : seq byte) cs :
  chunked K [:: x, c & cs] = (size x == K) && chunked K (c :: cs).
Proof. by []. Qed.

Lemma flatten_cons1 (T : Type) (x : seq T) xs : flatten (x :: xs) = x ++ flatten xs.
Proof. by []. Qed.

Lemma chunkf_nil_arg f K : chunkf f K [::] = [::].
Proof. by case: f. Qed.

Lemma chunkf_cons f K b r :
  chunkf f.+1 K (b :: r) = take K (b :: r) :: chunkf f K (drop K (b :: r)).
Proof. by []. Qed.

Lemma chunkf_nil f K bs : size bs <= f -> chunkf f K bs = [::] -> bs = [::].
Proof. by case: f => [|f] /=; [rewrite leqn0 => /nilP | case: bs]. Qed.

Lemma size_drop_le K (b : byte) r f : 0 < K -> size (b :: r) <= f.+1 -> size (drop K (b :: r)) <= f.
Proof.
move=> K0 h; rewrite size_drop leq_subLR (leq_trans h) //.
by rewrite -addn1 addnC leq_add2r.
Qed.

Lemma flatten_chunkf f K bs : 0 < K -> size bs <= f -> flatten (chunkf f K bs) = bs.
Proof.
move=> K0; elim: f bs => [|f ih] bs h.
  by move: h; rewrite leqn0 => /nilP ->.
case: bs h => [|b r] h; first by rewrite chunkf_nil_arg.
by rewrite chunkf_cons flatten_cons1 ih ?cat_take_drop // size_drop_le.
Qed.

Lemma chunkf_chunked f K bs : 0 < K -> size bs <= f -> chunked K (chunkf f K bs).
Proof.
move=> K0; elim: f bs => [|f ih] bs h; first by [].
case: bs h => [|b r] h; first by rewrite chunkf_nil_arg.
have hd := size_drop_le K0 h.
rewrite chunkf_cons; have := ih _ hd.
case e: (chunkf f K (drop K (b :: r))) => [|c cs] ch.
  have : drop K (b :: r) == [::] by rewrite (chunkf_nil hd e).
  rewrite -size_eq0 size_drop subn_eq0 => hk.
  by rewrite chunked1 size_take_min (minn_idPr hk) hk.
have ne : drop K (b :: r) != [::].
  by apply/eqP=> ed; move: e; rewrite ed chunkf_nil_arg.
rewrite chunked_cons2 ch andbT size_take_min; apply/eqP/minn_idPl.
by move: ne; rewrite -size_eq0 size_drop -lt0n subn_gt0 => /ltnW.
Qed.

Lemma chunks_flatten K bs : 0 < K -> flatten (chunks K bs) = bs.
Proof. by move=> K0; rewrite /chunks count_fromE flatten_chunkf. Qed.

Lemma chunks_chunked K bs : 0 < K -> chunked K (chunks K bs).
Proof. by move=> K0; rewrite /chunks count_fromE chunkf_chunked. Qed.

Lemma chunked_ne K cs : chunked K cs -> cs != [::] -> (0 < K) && (flatten cs != [::]).
Proof.
elim: cs => [|c cs ih] // + _; case: cs ih => [|c' cs] ih.
  rewrite chunked1 flatten_cons1 cats0 => /andP [s0 hk].
  by rewrite (leq_trans s0 hk) -size_eq0 -lt0n s0.
rewrite chunked_cons2 => /andP [_ /ih /(_ isT) /andP [K0 hne]].
rewrite K0 andTb flatten_cons1; apply: (contraNneq _ hne) => e.
have /eqP := congr1 size e; rewrite size_cat addn_eq0 => /andP [_].
by rewrite size_eq0.
Qed.

Lemma chunked_chunkf K cs f :
  chunked K cs -> size (flatten cs) <= f -> chunkf f K (flatten cs) = cs.
Proof.
elim: cs f => [|c cs ih] f; first by rewrite chunkf_nil_arg.
case: cs ih => [|c' cs] ih.
  move=> /andP [s0 sk]; rewrite flatten_cons1 cats0 => hf.
  case: c s0 sk hf => [|x c] // _ sk hf.
  case: f hf => [|f] hf; first by [].
  by rewrite chunkf_cons take_oversize // drop_oversize // chunkf_nil_arg.
rewrite chunked_cons2 => /andP [/eqP ek ch] hf.
have /andP [K0 hne] := chunked_ne ch isT.
move: hf; rewrite flatten_cons1 => hf.
have hsz : size (c ++ flatten (c' :: cs)) = K + size (flatten (c' :: cs)).
  by rewrite size_cat ek.
case e: (c ++ flatten (c' :: cs)) => [|x y].
  have /eqP := congr1 size e; rewrite size_cat addn_eq0 => /andP [_].
  by rewrite size_eq0 (negbTE hne).
case: f hf => [|f] hf; first by move: hf; rewrite e.
rewrite chunkf_cons -e take_size_cat // drop_size_cat // ih //.
move: hf; rewrite hsz => hf.
by rewrite -ltnS (leq_trans _ hf) // -addn1 addnC leq_add2r.
Qed.

Lemma chunked_chunks K cs : chunked K cs -> chunks K (flatten cs) = cs.
Proof. by move=> ch; rewrite /chunks count_fromE chunked_chunkf. Qed.

(* ---- decoding the encoding ---- *)
Lemma dec_cons c t : dec (c :: t) = cbytes c ++ dec t.
Proof. by []. Qed.

Theorem dec_enc K bs : 0 < K -> dec (enc K bs) = bs.
Proof.
move=> K0; rewrite /dec /enc -map_comp.
rewrite (@eq_map _ _ _ id) ?map_id ?chunks_flatten // => c /=.
exact: cbytes_encc.
Qed.

Corollary size_dec_enc K bs : 0 < K -> size (dec (enc K bs)) = size bs.
Proof. by move=> K0; rewrite dec_enc. Qed.

Lemma enc_runs K bs : all runs_ok (enc K bs).
Proof. by apply/allP=> c /mapP [c' _ ->]; exact: encc_runs. Qed.

(* a text in canonical form is the encoding of the bytes it represents *)
Definition canon (K : nat) (t : seq (seq piece)) : bool := enc K (dec t) == t.

Lemma canonP K t : canon K t -> enc K (dec t) = t.
Proof. by move/eqP. Qed.

Lemma canon_dec K t : canon K t -> exists bs, t = enc K bs /\ dec t = bs.
Proof. by move=> /canonP e; exists (dec t); rewrite e. Qed.

(* ---- the length in binary ---- *)
Definition plen (p : piece) : N :=
  match p with PS s => N.of_nat (String.length s) | PB _ => Npos xH end.
Fixpoint clen (a : N) (c : seq piece) : N :=
  if c is p :: c' then clen (N.add a (plen p)) c' else a.
Fixpoint dlenf (a : N) (t : seq (seq piece)) : N :=
  if t is c :: t' then dlenf (clen a c) t' else a.
Definition dlen (t : seq (seq piece)) : N := dlenf N0 t.

Lemma clenE a c : clen a c = N.add a (N.of_nat (size (cbytes c))).
Proof.
elim: c a => [|p c ih] a; first by rewrite /= N.add_0_r.
rewrite [clen _ _]/= ih cbytes_cons size_cat Nat2N.inj_add N.add_assoc.
by case: p => [s|b] //=; rewrite size_bytes_of_str.
Qed.

Lemma dlenfE a t : dlenf a t = N.add a (N.of_nat (size (dec t))).
Proof.
elim: t a => [|c t ih] a; first by rewrite /= N.add_0_r.
by rewrite [dlenf _ _]/= ih clenE dec_cons size_cat Nat2N.inj_add N.add_assoc.
Qed.

Lemma dlenE t : dlen t = N.of_nat (size (dec t)).
Proof. by rewrite /dlen dlenfE. Qed.

Lemma size_dec t : size (dec t) = N.to_nat (dlen t).
Proof. by rewrite dlenE Nat2N.id. Qed.

(* ---- a cross-check value ---- *)
Definition dmask : N := N.pred (N.shiftl 1 61).   (* 2^61 - 1 *)
Definition dstep (h : N) (b : byte) : N :=
  let x := N.add (N.shiftl h 8) (Strings.Byte.to_N b) in
  let y := N.add (N.land x dmask) (N.shiftr x 61) in
  if N.leb dmask y then N.sub y dmask else y.
Definition digest (bs : seq byte) : N := foldl dstep N0 bs.
