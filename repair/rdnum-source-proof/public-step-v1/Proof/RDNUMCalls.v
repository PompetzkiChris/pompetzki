(* Call composition for the unchanged PmpCore execution function. *)
From Stdlib Require Import String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
Set Implicit Arguments.

Section Calls.
Variables (P : seq stmt) (stops : seq string).
Definition return_extension (f pc : nat) (ks : seq nat) (s : state) : Prop :=
  match exec f P stops pc ks s with
  | OReturn s' => exists d, (d <= f)%N /\ forall g k K,
      exec (f + g) P stops pc (ks ++ k :: K) s = exec (f + g - d) P stops k K s'
  | _ => True
  end.
Lemma exec_return_extension f : forall pc ks s, return_extension f pc ks s.
Proof.
  rewrite /return_extension.
  elim: f => [//|f IH] pc ks s.
  case: (ltnP pc (size P)) => Hpc; last first.
  { rewrite exec_unfold. move/leP/Nat.ltb_ge: Hpc => ->. done. }
  have U : forall h K0, exec h.+1 P stops pc K0 s = run_stmt h P stops pc K0 s (nth (STrace true) P pc).
  { move=> h K0. exact: exec_S. }
  rewrite (@exec_S f P stops pc ks s Hpc).
  have nxt : forall pc0 ks0 s0,
    match exec f P stops pc0 ks0 s0 with
    | OReturn s' => exists d, (d <= f.+1)%N /\ forall g k K,
        exec (f + g) P stops pc0 (ks0 ++ k :: K) s0 = exec (f.+1 + g - d) P stops k K s'
    | _ => True end.
  { move=> pc0 ks0 s0. have H := IH pc0 ks0 s0.
    case: (exec f P stops pc0 ks0 s0) H => // s' [d [Hd Hr]].
    exists d.+1; split; first by lia.
    move=> g k K. by rewrite addSn subSS Hr. }
  have jmp : forall l ks0,
    match jumpo f P stops pc l ks0 s with
    | OReturn s' => exists d, (d <= f.+1)%N /\ forall g k K,
        jumpo (f + g) P stops pc l (ks0 ++ k :: K) s = exec (f.+1 + g - d) P stops k K s'
    | _ => True end.
  { move=> l ks0. rewrite /jumpo.
    case: (has (String.eqb l) stops) => //.
    case: (find_label P l) => // i. exact: nxt. }
  move: U. case: (nth (STrace true) P pc) =>
    [x a|x a b|x a b|x a b|x a w|a w b|x a|x bs|x a l|x a b|c a l|l|l||l|b] U;
    cbn [run_stmt];
    try (match goal with |- context [exec f P stops ?pc0 ?ks0 ?s0] =>
      have H := nxt pc0 ks0 s0;
      case: (exec f P stops pc0 ks0 s0) H => // s' [d [Hd Hr]];
      exists d; split=> // g k K; by rewrite addSn U /= Hr addSn end).
  - case Et: (test c (ev s a)); cbn beta iota.
    + have H := jmp l ks. case: (jumpo f P stops pc l ks s) H => // s' [d [Hd Hr]].
      exists d; split=> // g k K. by rewrite addSn U /= Et Hr addSn.
    + have H := nxt pc.+1 ks s. case: (exec f P stops pc.+1 ks s) H => // s' [d [Hd Hr]].
      exists d; split=> // g k K. by rewrite addSn U /= Et Hr addSn.
  - have H := jmp l ks. case: (jumpo f P stops pc l ks s) H => // s' [d [Hd Hr]].
    exists d; split=> // g k K. by rewrite addSn U /= Hr addSn.
  - have H := jmp l (pc.+1 :: ks). case: (jumpo f P stops pc l (pc.+1 :: ks) s) H => // s' [d [Hd Hr]].
    exists d; split=> // g k K. by rewrite addSn U /= Hr addSn.
  - case: ks => [|k0 ks0].
    + exists 1%N; split=> // g k K. by rewrite addSn U /= subn1.
    + have H := nxt k0 ks0 s. case: (exec f P stops k0 ks0 s) H => // s' [d [Hd Hr]].
      exists d; split=> // g k K. by rewrite addSn U /= Hr addSn.
Qed.
Theorem evals_call pc s s' k K r :
  evals P stops pc [::] s (OReturn s') -> evals P stops k K s' r ->
  evals P stops pc (k :: K) s r.
Proof.
  move=> [f1 H1] [f0 H0]. have E1 := H1 f1 (leqnn _).
  have B := exec_return_extension f1 pc [::] s.
  rewrite /return_extension E1 in B. case: B => d [Hd HB].
  exists (f1+f0)%N => F HF.
  have EF : F=(f1+(F-f1))%N by rewrite subnKC //; lia.
  rewrite EF HB. apply H0. rewrite -EF. lia.
Qed.
End Calls.
Print Assumptions evals_call.
