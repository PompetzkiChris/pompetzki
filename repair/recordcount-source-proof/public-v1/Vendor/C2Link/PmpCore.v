(* C2Link.PmpCore - the Pompetzki commands executed by the input stage of pmp/verify_run2.pmp
   (pmp/jcanon.pmp and the numeral routines of pmp/gbjson2.pmp), as Rocq syntax with an
   operational semantics (2026-09-25).

   Only these forms are represented (their pmp spelling in brackets):
     SConst x a        [set x const A]          SAdd/SSub/SMul x a b  [set x add|sub|mul A B]
     SPeek x a w       [set x peek A W]         SPoke a w b           [poke A W B]
     SAlloc x a        [set x alloc A]
     STextLit x bs     [text x "LIT"]           STextPad x a l        [text x pad A L]
     STextCmp x a b    [text x compare A B]
     SWhen c a l       [when zero|nonzero|negative A goto L]
     SGoto l [goto L]  SGosub l [gosub L]  SReturn [return]  SLabel l [label L]
     STrace b          [trace off|on]  (no effect on the computation)
   An operand is a variable or an integer literal.  A text NAME is the pair of variables
   NAME (its address) and NAME_len (its length), as in the interpreter.

   State: word variables (Z), a byte memory indexed by Z, and the next free address hp.
     text x "LIT"      writes LIT and a zero byte at hp; x := hp, x_len := |LIT|;
     text x pad A L    copies L bytes from A to hp in the same way;
     text x compare A B  x := 0 when the bytes of A and B (with their lengths) are equal, else 1;
     set x alloc N     x := hp; hp := hp + N (the contents are not assumed);
     peek A 1 / poke A 1 B   one byte (B modulo 256);
     peek A 8 / poke A 8 B   eight bytes, little endian, two's complement modulo 2^64.
   Arithmetic is on Z: the interpreter's words are 64-bit, so the theorems about a routine
   state the ranges its values stay in (addresses and lengths below 2^62).  That the native
   interpreter (pompetzki.asm) executes each form as described here is the boundary of this
   development (not proved), as is the operating system's file reading.

   exec fuel P stops pc ks st runs P from index pc with the return stack ks:
     OReturn st      a return with an empty stack (the routine returned to its caller);
     OStop l st      a jump to a label l in stops (for the checker: GBFAIL, the rejection);
     OStuck pc       a missing label or running off the program;
     OFuel           the fuel ran out. *)
From Stdlib Require Import String ZArith Lia.
From Stdlib Require Strings.Byte.
From Stdlib Require Import Init.Byte.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope Z_scope.

Inductive opd := OV (x : string) | OL (z : Z).
Inductive cond := CZero | CNonzero | CNeg.
Inductive stmt :=
| SConst (x : string) (a : opd)
| SAdd (x : string) (a b : opd)
| SSub (x : string) (a b : opd)
| SMul (x : string) (a b : opd)
| SPeek (x : string) (a : opd) (w : nat)
| SPoke (a : opd) (w : nat) (b : opd)
| SAlloc (x : string) (a : opd)
| STextLit (x : string) (bs : seq byte)
| STextPad (x : string) (a l : opd)
| STextCmp (x a b : string)
| SWhen (c : cond) (a : opd) (l : string)
| SGoto (l : string)
| SGosub (l : string)
| SReturn
| SLabel (l : string)
| STrace (on : bool).

Record state := St { vars : string -> Z; mem : Z -> byte; hp : Z }.

Definition lenv (x : string) : string := (x ++ "_len")%string.
Definition setv (st : state) (x : string) (v : Z) : state :=
  St (fun y => if String.eqb y x then v else vars st y) (mem st) (hp st).
Definition setm (st : state) (a : Z) (b : byte) : state :=
  St (vars st) (fun c => if Z.eqb c a then b else mem st c) (hp st).
Definition seth (st : state) (h : Z) : state := St (vars st) (mem st) h.

Definition ev (st : state) (a : opd) : Z := match a with OV x => vars st x | OL z => z end.
Definition bz (b : byte) : Z := Z.of_nat (bnat b).
Definition zbyte (z : Z) : byte :=
  match Strings.Byte.of_nat (Z.to_nat (Z.modulo z 256)) with Some b => b | None => x00 end.

(* the bytes at a .. a+n-1 *)
Definition bytes_at (st : state) (a : Z) (n : nat) : seq byte :=
  [seq mem st (a + Z.of_nat i) | i <- iota 0 n].
Definition text_of (st : state) (x : string) : seq byte :=
  bytes_at st (vars st x) (Z.to_nat (vars st (lenv x))).

Fixpoint write_bytes (st : state) (a : Z) (bs : seq byte) : state :=
  if bs is b :: r then write_bytes (setm st a b) (a + 1) r else st.

Definition peek8 (st : state) (a : Z) : Z :=
  let u := foldr (fun i acc => acc * 256 + bz (mem st (a + Z.of_nat i))) 0 (iota 0 8) in
  if u <? 2 ^ 63 then u else u - 2 ^ 64.
Fixpoint poke_le (st : state) (a v : Z) (k : nat) : state :=
  if k is k'.+1 then poke_le (setm st a (zbyte v)) (a + 1) (Z.div v 256) k' else st.

Definition peek (st : state) (a : Z) (w : nat) : Z := if w == 8%N then peek8 st a else bz (mem st a).
Definition poke (st : state) (a : Z) (w : nat) (v : Z) : state :=
  if w == 8%N then poke_le st a (Z.modulo v (2 ^ 64)) 8 else setm st a (zbyte v).

(* text x "LIT": the bytes and a zero byte at hp *)
Definition text_new (st : state) (x : string) (bs : seq byte) : state :=
  let a := hp st in
  let st1 := write_bytes st a (rcons bs x00) in
  seth (setv (setv st1 x a) (lenv x) (Z.of_nat (size bs))) (a + Z.of_nat (size bs) + 1).

Definition test (c : cond) (v : Z) : bool :=
  match c with CZero => v =? 0 | CNonzero => negb (v =? 0) | CNeg => v <? 0 end.

Fixpoint find_label (P : seq stmt) (l : string) : option nat :=
  if P is s :: P' then
    (if s is SLabel l' then (if String.eqb l l' then Some 0%N else omap S (find_label P' l))
     else omap S (find_label P' l))
  else None.

Inductive outcome := OReturn (st : state) | OStop (l : string) (st : state) | OStuck (pc : nat) | OFuel.

Fixpoint exec (fuel : nat) (P : seq stmt) (stops : seq string) (pc : nat) (ks : seq nat) (st : state) : outcome :=
  match fuel with
  | O => OFuel
  | S f =>
    let jump (l : string) (ks : seq nat) (st : state) : outcome :=
      if has (String.eqb l) stops then OStop l st
      else match find_label P l with Some i => exec f P stops i ks st | None => OStuck pc end in
    if Nat.ltb pc (size P) then
      match nth (STrace true) P pc with
      | SConst x a => exec f P stops pc.+1 ks (setv st x (ev st a))
      | SAdd x a b => exec f P stops pc.+1 ks (setv st x (ev st a + ev st b))
      | SSub x a b => exec f P stops pc.+1 ks (setv st x (ev st a - ev st b))
      | SMul x a b => exec f P stops pc.+1 ks (setv st x (ev st a * ev st b))
      | SPeek x a w => exec f P stops pc.+1 ks (setv st x (peek st (ev st a) w))
      | SPoke a w b => exec f P stops pc.+1 ks (poke st (ev st a) w (ev st b))
      | SAlloc x a => exec f P stops pc.+1 ks (seth (setv st x (hp st)) (hp st + ev st a))
      | STextLit x bs => exec f P stops pc.+1 ks (text_new st x bs)
      | STextPad x a l => exec f P stops pc.+1 ks (text_new st x (bytes_at st (ev st a) (Z.to_nat (ev st l))))
      | STextCmp x a b =>
          exec f P stops pc.+1 ks (setv st x (if text_of st a == text_of st b then 0 else 1))
      | SWhen c a l => if test c (ev st a) then jump l ks st else exec f P stops pc.+1 ks st
      | SGoto l => jump l ks st
      | SGosub l => jump l (pc.+1 :: ks) st
      | SReturn => if ks is k :: ks' then exec f P stops k ks' st else OReturn st
      | SLabel _ | STrace _ => exec f P stops pc.+1 ks st
      end
    else OStuck pc
  end.

(* ---- basic facts ---- *)
Lemma setv_get (st : state) x v y : vars (setv st x v) y = if String.eqb y x then v else vars st y.
Proof. by []. Qed.
Lemma setv_mem st x v : mem (setv st x v) = mem st. Proof. by []. Qed.
Lemma setv_hp st x v : hp (setv st x v) = hp st. Proof. by []. Qed.

Lemma write_bytes_vars st a bs : vars (write_bytes st a bs) = vars st.
Proof. by elim: bs st a => //= b bs ih st a; rewrite ih. Qed.
Lemma write_bytes_hp st a bs : hp (write_bytes st a bs) = hp st.
Proof. by elim: bs st a => //= b bs ih st a; rewrite ih. Qed.
Lemma write_bytes_outside st a bs c : (c < a \/ a + Z.of_nat (size bs) <= c) ->
  mem (write_bytes st a bs) c = mem st c.
Proof.
elim: bs st a => //= b bs ih st a hc; rewrite ih; last by lia.
rewrite /setm /=; case: (Z.eqb_spec c a) => // ?; lia.
Qed.

(* reading below the next free address is unaffected by a new text *)
Lemma text_new_mem_below st x bs c : c < hp st -> mem (text_new st x bs) c = mem st c.
Proof. by move=> h; rewrite /text_new /= write_bytes_outside //; left. Qed.
Lemma text_new_hp st x bs : hp st <= hp (text_new st x bs).
Proof. rewrite /text_new /=; lia. Qed.
