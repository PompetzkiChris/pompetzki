(* C2Link.RunKit - the frame of a routine for any list of local names (2026-09-25).
   frame_on L st0 st: every variable outside L, all memory below the old next free address, and
   the order of the next free address are as in st0.  Used by the routine proofs after GBNUMSTR
   (NumeralRun keeps its own frame, NumeralLink.frame, which is frame_on NumeralLink.locals). *)
From Stdlib Require Import String ZArith Lia.
From Stdlib Require Import Init.Byte.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Frame.
Variables (L : seq string) (st0 : state).
Definition frame_on (st : state) : Prop :=
  [/\ forall y, ~~ has (String.eqb y) L -> vars st y = vars st0 y,
      forall c, (c < hp st0)%Z -> mem st c = mem st0 c & (hp st0 <= hp st)%Z].

Lemma frame_on0 : frame_on st0. Proof. by split=> //; exact: Z.le_refl. Qed.

Lemma frame_on_setv st x v : has (String.eqb x) L -> frame_on st -> frame_on (setv st x v).
Proof.
move=> hx [h1 h2 h3]; split=> // y hy.
rewrite setv_get; case: ifP => [/String.eqb_eq e|_]; last exact: h1.
by rewrite e hx in hy.
Qed.

Lemma frame_on_text st x bs : has (String.eqb x) L -> has (String.eqb (lenv x)) L ->
  frame_on st -> frame_on (text_new st x bs).
Proof.
move=> hx hl [h1 h2 h3]; split.
- move=> y hy; rewrite text_new_get.
  case: (String.eqb_spec y (lenv x)) => [e|_]; first by rewrite e hl in hy.
  case: (String.eqb_spec y x) => [e|_]; first by rewrite e hx in hy.
  exact: h1.
- by move=> c hc; rewrite text_new_mem_below; [exact: h2 | lia].
- by have := @text_new_hp st x bs; lia.
Qed.
End Frame.
