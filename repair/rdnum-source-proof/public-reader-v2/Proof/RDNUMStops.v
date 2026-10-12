(* Stop outcomes are unaffected by adding caller continuation frames. *)
From Stdlib Require Import String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
Set Implicit Arguments.

Section Stops.
Variables (P:seq stmt) (stops:seq string).
Lemma exec_stop_extension f : forall pc ks s l sf more,
  exec f P stops pc ks s = OStop l sf ->
  exec f P stops pc (ks++more) s = OStop l sf.
Proof.
  elim: f => [//|f IH] pc ks s l sf more H.
  rewrite !exec_unfold in H |- *.
  case Epc: (Nat.ltb pc (size P)) in H |- * => //.
  have jmp : forall pc0 lab ks0 s0,
    jumpo f P stops pc0 lab ks0 s0 = OStop l sf ->
    jumpo f P stops pc0 lab (ks0++more) s0 = OStop l sf.
  { move=> pc0 lab ks0 s0. rewrite /jumpo.
    case: (has (String.eqb lab) stops) => //.
    case: (find_label P lab) => // i. exact: IH. }
  case: (nth (STrace true) P pc) H =>
    [x a|x a b|x a b|x a b|x a w|a w b|x a|x bs|x a len|x a b|c a lab|lab|lab||lab|b];
    cbn [run_stmt];try exact: IH.
  - case: (test c (ev s a));[exact: jmp|exact: IH].
  - exact: jmp.
  - exact: jmp.
  - case: ks => [|k ks] => // H. exact: IH H.
Qed.
Theorem evals_stop_extension pc ks s l sf more :
  evals P stops pc ks s (OStop l sf) ->
  evals P stops pc (ks++more) s (OStop l sf).
Proof. move=> [f0 H]. exists f0 => f Hf. apply exec_stop_extension. exact: H. Qed.
End Stops.
Print Assumptions evals_stop_extension.
