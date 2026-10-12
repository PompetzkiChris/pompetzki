(* RpInitOk.v - the initial registry of the replay: the seven axioms, the 670 definitions in their closed form
   A v1 .. A vn Q (P v1 .. vn) body, the 29 placeholder hypotheses; each entry derivable (reg_ok). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Sub Expand Replay Replay2 Replay3 RpInit.
Import ListNotations.
Open Scope nat_scope.

Definition hypf (h : N) : form := tof (nth (N.to_nat h) HYPD (dE 0 0)).

Fixpoint mapi {A B : Type} (f : nat -> A -> B) (i : nat) (l : list A) : list B :=
  match l with [] => [] | x :: r => f i x :: mapi f (S i) r end.

Definition REG0 : list entry :=
  map (fun d => (d, [])) AX0 ++ map (fun d => (d, [])) DEF0 ++ mapi (fun i d => (d, [N.of_nat i])) 0 HYPD.

Fixpoint allN (k : nat) (f : form) : form := match k with 0 => f | S m => All (allN m f) end.
Definition revn (k i : nat) : nat := k - 1 - i.
Definition closed_def (d : nat * nat * form) : form := match d with (p, k, body) => allN k (ren (revn k) (defax d)) end.

(* the checks, stated expanded (the kernel never evaluates Dall by conversion) *)
Definition ax_check : bool := forallb (fun e => form_eqb (tof (fst e)) (axf (snd e))) (combine AX0 (seq 0 7)).
Definition def_check : bool :=
  Nat.eqb (length DEF0) (length Dall) && forallb (fun e => form_eqb (tof (fst e)) (closed_def (snd e))) (combine DEF0 Dall).
Lemma ax_check_x : forallb (fun e => form_eqb (tof (fst e)) (axf (snd e))) (combine AX0 (seq 0 7)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma def_check_x : forallb (fun e => form_eqb (tof (fst e)) (closed_def (snd e))) (combine DEF0 Dall) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma len_AX0 : length AX0 = 7. Proof. vm_compute. reflexivity. Qed.
Lemma len_DEF0 : length DEF0 = length Dall. Proof. vm_compute. reflexivity. Qed.

Lemma allN_prov A k f : prov A f -> prov A (allN k f).
Proof. induction k; simpl; auto. intros H. apply p_gen. apply IHk. exact H. Qed.

Lemma closed_def_prov d hs : In d Dall -> prov (AH hypf hs) (closed_def d).
Proof.
  intros H. destruct d as [[p k] body]. simpl. apply allN_prov. apply p_ax. left. right. right. right.
  exists (p, k, body), (revn k). split; [exact H|reflexivity].
Qed.

Lemma in_combine_nth {A B : Type} (l1 : list A) (l2 : list B) i a b :
  nth_error l1 i = Some a -> nth_error l2 i = Some b -> In (a, b) (combine l1 l2).
Proof.
  revert l2 i. induction l1 as [|x r IH]; intros l2 i E1 E2; [destruct i; discriminate|].
  destruct l2 as [|y s]; [destruct i; discriminate|]. destruct i as [|i]; simpl in *.
  - injection E1 as <-. injection E2 as <-. left. reflexivity.
  - right. apply (IH s i E1 E2).
Qed.

Lemma nth_error_mapi {A B : Type} (f : nat -> A -> B) l : forall i j x, nth_error l j = Some x -> nth_error (mapi f i l) j = Some (f (i + j) x).
Proof.
  induction l as [|y r IH]; intros i j x E; [destruct j; discriminate|]. destruct j as [|j]; simpl in *.
  - injection E as <-. rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S i) j x E). f_equal. f_equal. lia.
Qed.

Lemma nth_error_mapi_inv {A B : Type} (f : nat -> A -> B) l : forall i j y, nth_error (mapi f i l) j = Some y ->
  exists x, nth_error l j = Some x /\ y = f (i + j) x.
Proof.
  induction l as [|z r IH]; intros i j y E; [destruct j; discriminate|]. destruct j as [|j]; simpl in *.
  - injection E as <-. exists z. split; [reflexivity|]. rewrite Nat.add_0_r. reflexivity.
  - destruct (IH (S i) j y E) as [x [E1 E2]]. exists x. split; [exact E1|]. rewrite E2. f_equal. lia.
Qed.

Theorem REG0_ok : reg_ok hypf REG0.
Proof.
  intros i d h E. unfold REG0 in E.
  destruct (Nat.lt_ge_cases i (length (map (fun d => (d, [] : list N)) AX0))) as [L1|L1].
  - rewrite nth_error_app1 in E by exact L1. rewrite nth_error_map in E. destruct (nth_error AX0 i) as [d0|] eqn:E0; simpl in E; [|discriminate]. injection E as <- <-.
    rewrite length_map in L1. pose proof ax_check_x as C. rewrite forallb_forall in C.
    assert (Hs : nth_error (seq 0 7) i = Some i) by (rewrite nth_error_seq; rewrite len_AX0 in L1; destruct (i <? 7) eqn:Q; [reflexivity|apply Nat.ltb_ge in Q; lia]).
    specialize (C _ (in_combine_nth _ _ _ _ _ E0 Hs)). simpl in C. apply form_eqb_true in C. rewrite C.
    apply p_ax. left. left. exists i. rewrite len_AX0 in L1. split; [exact L1|reflexivity].
  - rewrite nth_error_app2 in E by exact L1. rewrite length_map in E, L1.
    destruct (Nat.lt_ge_cases (i - length AX0) (length (map (fun d => (d, [] : list N)) DEF0))) as [L2|L2].
    + rewrite nth_error_app1 in E by exact L2. rewrite nth_error_map in E. destruct (nth_error DEF0 (i - length AX0)) as [d0|] eqn:E0; simpl in E; [|discriminate]. injection E as <- <-.
      rewrite length_map in L2. rewrite len_DEF0 in L2.
      destruct (nth_error Dall (i - length AX0)) as [dd|] eqn:ED; [|apply nth_error_None in ED; lia].
      pose proof def_check_x as C. rewrite forallb_forall in C.
      specialize (C _ (in_combine_nth _ _ _ _ _ E0 ED)). simpl in C. apply form_eqb_true in C. rewrite C.
      apply closed_def_prov. exact (nth_error_In _ _ ED).
    + rewrite nth_error_app2 in E by exact L2. rewrite length_map in E.
      apply nth_error_mapi_inv in E as [x [E0 Ex]]. injection Ex as Ed Eh. subst d h.
      apply p_ax. right. eexists. split; [left; reflexivity|].
      unfold hypf. rewrite Nat2N.id. f_equal. symmetry. apply nth_error_nth. rewrite <- E0. f_equal.
Qed.
