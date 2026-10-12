From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From RDNUM Require Import RDNUMSource.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Ltac rvars := repeat progress (rewrite ?setv_get; cbn [String.eqb]).
Lemma peek_setv_reader st x v p w : peek (setv st x v) p w = peek st p w.
Proof. unfold peek, peek8. reflexivity. Qed.

Lemma reader_jump_stop f pc l ks st : has (String.eqb l) reader_stops = true ->
  jumpo f Preader reader_stops pc l ks st = OStop l st.
Proof. intros H. unfold jumpo. rewrite H. reflexivity. Qed.
Lemma reader_jump_go f pc l ks st i : has (String.eqb l) reader_stops = false ->
  find_label Preader l = Some i -> jumpo f Preader reader_stops pc l ks st = exec f Preader reader_stops i ks st.
Proof. intros H L. unfold jumpo. rewrite H L. reflexivity. Qed.
Ltac rresolve :=
  repeat match goal with
  | |- context [jumpo ?f Preader reader_stops ?pc ?l ?ks ?s] =>
    let b := eval vm_compute in (has (String.eqb l) reader_stops) in
    lazymatch b with
    | true => rewrite (@reader_jump_stop f pc l ks s); [|vm_compute; reflexivity]
    | false => let target := eval vm_compute in (find_label Preader l) in
      lazymatch target with Some ?i => rewrite (@reader_jump_go f pc l ks s i);
        [|vm_compute; reflexivity|vm_compute; reflexivity] end
    end
  end.

Ltac rstep_at f pc ks s :=
  rewrite (@exec_S f Preader reader_stops pc ks s); [|vm_compute; reflexivity];
  let term := eval vm_compute in (nth (STrace true) Preader pc) in
  change (nth (STrace true) Preader pc) with term;
  cbn [run_stmt ev test]; rresolve.

Ltac rsw tac :=
  lazymatch goal with |- evals Preader reader_stops ?pc ?ks ?s ?r =>
    eapply (@evals_step Preader reader_stops pc ks s);
    [ let f := fresh "fuel" in intro f; rstep_at f pc ks s;
      tac; reflexivity | ] end.
Ltac rs := rsw idtac.
Ltac rsn :=
  lazymatch goal with |- evals Preader reader_stops ?pc ?ks ?s ?r =>
    apply: (@evals_now Preader reader_stops pc ks s);
    let f := fresh "fuel" in intro f; rstep_at f pc ks s end.

Ltac rinstruction :=
  lazymatch goal with |- context [exec ?fuel Preader reader_stops ?pc ?ks ?s] =>
    let unfolded := eval compute in fuel in
    lazymatch unfolded with S ?f =>
      change fuel with unfolded; rstep_at f pc ks s;
      repeat progress (rewrite ?setv_get ?peek_setv_reader; cbn [String.eqb])
    end end.

Theorem reader_prefix n pc ks s pc' ks' s' r :
  (forall f, exec (n+f)%N Preader reader_stops pc ks s =
             exec f Preader reader_stops pc' ks' s') ->
  evals Preader reader_stops pc' ks' s' r ->
  evals Preader reader_stops pc ks s r.
Proof.
  move=> H [f0 H0]. exists (n+f0)%N => F HF.
  have EF : F=(n+(F-n))%N by rewrite subnKC //; lia.
  rewrite EF H. apply H0. lia.
Qed.
Print Assumptions reader_prefix.
