(* A pure byte-list lexer and its readable-buffer/cursor decomposition. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore.
From RDNUM Require Import RDNUMReaders RDNUMPolicy RDNUMComplete.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition whiteb b := ((b =? 32)||(b =? 10)||(b =? 13)||(b =? 9))%bool.
Definition digitb b := ((48 <=? b)&&(b <? 58))%bool.
Lemma whiteb_true b : whiteb b=true <-> whitespace b.
Proof. unfold whiteb,whitespace;rewrite !Bool.orb_true_iff !Z.eqb_eq;tauto. Qed.
Lemma whiteb_false b : whiteb b=false <-> ~whitespace b.
Proof. destruct (whiteb b) eqn:H;split;try discriminate.
  - intro Hn;exfalso;apply Hn;apply whiteb_true;exact H.
  - intros _ Hwhite;have HT := proj2 (whiteb_true b) Hwhite;congruence.
  - reflexivity.
Qed.
Lemma digitb_true b : digitb b=true <-> 48<=b<58.
Proof. unfold digitb;rewrite Bool.andb_true_iff Z.leb_le Z.ltb_lt;tauto. Qed.
Lemma digitb_false b : digitb b=false <-> ~(48<=b<58).
Proof. destruct (digitb b) eqn:H;split;try discriminate.
  - intro Hn;exfalso;apply Hn;apply digitb_true;exact H.
  - intros _ Hd;have HT := proj2 (digitb_true b) Hd;congruence.
  - reflexivity.
Qed.

Fixpoint buffer_segment (s:state) (p:Z) (raw:list Z) : Prop :=
  match raw with []=>True | b::tail=>peek s p 1=b /\ buffer_segment s (p+1) tail end.
Fixpoint split_white (raw:list Z) : nat*list Z :=
  match raw with []=>(0%N,[]) | b::tail=>
    if whiteb b then let '(n,rest):=split_white tail in (S n,rest) else (0%N,raw) end.
Fixpoint split_decimal (raw:list Z) : list Z*list Z :=
  match raw with []=>([],[]) | b::tail=>
    if digitb b then let '(ds,rest):=split_decimal tail in (b-48::ds,rest) else ([],raw) end.
Definition whites_at s p n := forall i,(i<n)%coq_nat -> whitespace (peek s (p+Z.of_nat i) 1).
Definition tail_not_white raw := match raw with []=>True | b::_=>~whitespace b end.
Definition tail_not_digit raw := match raw with []=>True | b::_=>~(48<=b<58) end.

Theorem split_white_buffer s p raw n rest :
  buffer_segment s p raw -> split_white raw=(n,rest) ->
  whites_at s p n /\ buffer_segment s (p+Z.of_nat n) rest /\
  (n+List.length rest=List.length raw)%coq_nat /\ tail_not_white rest.
Proof.
  induction raw as [|b raw IH] in p,n,rest |- *.
  - cbn [split_white]. intros _ E;inversion E;subst. repeat split;try reflexivity.
    intros i H;lia.
  - cbn [buffer_segment split_white]. intros [Hbyte Htail] E.
    destruct (whiteb b) eqn:Hw.
    + destruct (split_white raw) as [k tail] eqn:Et. inversion E;subst n rest.
      destruct (IH (p+1) k tail Htail (Logic.eq_refl (k,tail))) as [Hws [Hbuf [Hlength Hnot]]].
      split.
      * intros i Hi. destruct i as [|i].
        -- change (whitespace (peek s (p+0) 1)). rewrite Z.add_0_r Hbyte;apply whiteb_true;exact Hw.
        -- rewrite Nat2Z.inj_succ. have Haddr : p+(Z.of_nat i+1)=p+1+Z.of_nat i by lia.
           rewrite Haddr;apply Hws;lia.
      * split.
        -- rewrite Nat2Z.inj_succ. replace (p+Z.succ (Z.of_nat k)) with (p+1+Z.of_nat k) by lia. exact Hbuf.
        -- split;[cbn [List.length];lia|exact Hnot].
    + inversion E;subst n rest. split.
      * intros i Hi;lia.
      * cbn [Z.of_nat]. rewrite Z.add_0_r. split;[split;assumption|].
        split;[reflexivity|apply whiteb_false;exact Hw].
Qed.

Theorem split_decimal_buffer s p raw ds rest :
  buffer_segment s p raw -> split_decimal raw=(ds,rest) ->
  Forall (fun d=>0<=d<10) ds /\ digit_segment s p ds /\
  buffer_segment s (p+Z.of_nat (List.length ds)) rest /\
  (List.length ds+List.length rest=List.length raw)%coq_nat /\ tail_not_digit rest.
Proof.
  induction raw as [|b raw IH] in p,ds,rest |- *.
  - cbn [split_decimal]. intros _ E;inversion E;subst. repeat split;constructor.
  - cbn [buffer_segment split_decimal]. intros [Hbyte Htail] E.
    destruct (digitb b) eqn:Hd.
    + destruct (split_decimal raw) as [digits tail] eqn:Et. inversion E;subst ds rest.
      destruct (IH (p+1) digits tail Htail (Logic.eq_refl (digits,tail))) as [Hdigits [Hseg [Hbuf [Hlength Hnot]]]].
      have Hrange := proj1 (digitb_true b) Hd.
      split;[constructor;[lia|exact Hdigits]|]. split.
      * cbn [digit_segment]. split;[rewrite Hbyte;lia|exact Hseg].
      * split.
        -- rewrite List.length_cons Nat2Z.inj_succ.
           replace (p+Z.succ (Z.of_nat (List.length digits))) with (p+1+Z.of_nat (List.length digits)) by lia. exact Hbuf.
        -- split;[cbn [List.length];lia|exact Hnot].
    + inversion E;subst ds rest. split;[constructor|]. split;[constructor|].
      cbn [List.length Z.of_nat]. rewrite Z.add_0_r. split;[split;assumption|].
      split;[reflexivity|apply digitb_false;exact Hd].
Qed.

Theorem lexical_entry_view s raw nw after ds rest :
  buffer_segment s (vars s "pos") raw -> vars s "lim"=vars s "pos"+Z.of_nat (List.length raw) ->
  split_white raw=(nw,after) -> split_decimal after=(ds,rest) ->
  entry_view s nw ds /\
  buffer_segment s (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)) rest /\
  (nw+List.length ds+List.length rest=List.length raw)%coq_nat.
Proof.
  intros Hbuffer Hlim Hwhite Hdecimal.
  destruct (@split_white_buffer s (vars s "pos") raw nw after Hbuffer Hwhite) as [Hw [Hafter [HlenW HnotW]]].
  destruct (@split_decimal_buffer s (vars s "pos"+Z.of_nat nw) after ds rest Hafter Hdecimal)
    as [Hd [Hdigits [Hrest [HlenD HnotD]]]].
  have Hlen : (nw+List.length ds+List.length rest=List.length raw)%coq_nat by lia.
  split;[|split;assumption]. unfold entry_view. split;[exact Hw|]. split.
  - destruct after as [|b after].
    + left. cbn [List.length] in HlenW. rewrite Hlim;f_equal;lia.
    + right. cbn [buffer_segment] in Hafter. unfold tail_not_white in HnotW.
      rewrite (proj1 Hafter);exact HnotW.
  - split;[exact Hd|]. split;[exact Hdigits|]. split.
    + rewrite Hlim. rewrite -Hlen !Nat2Z.inj_add. lia.
    + destruct rest as [|b rest].
      * left. cbn [List.length] in Hlen. rewrite Hlim -Hlen !Nat2Z.inj_add;lia.
      * right. cbn [buffer_segment] in Hrest. unfold tail_not_digit in HnotD.
        rewrite (proj1 Hrest);exact HnotD.
Qed.
Print Assumptions lexical_entry_view.
