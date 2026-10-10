(* Abs.v - absoluteness of bounded (Delta_0) formulas for a transitive class, as one theorem about every such formula.
   d0: the formulas built from x in y, x = y, not, implies and the bounded universal  All (v0 in v(k+1) -> a)
   (bounded existentials are not-All-not). TrM: the class M is transitive, forall x forall y (M(y) -> x in y -> M(x)).
   abs_d0: for every d0 formula phi, every n covering its free variables and every axiom set B,
     B |- M(v0) -> .. -> M(v(n-1)) -> TrM -> (rel M phi <-> phi).
   Pure logic: no axiom of B is used. Lane LCH, 2026-10-09. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Kal Checks Ax Expand Replay.
From LCH Require Import Rel2.
Import ListNotations.
Open Scope nat_scope.

Inductive d0 : form -> Prop :=
| d0_mem x y : d0 (Mem x y)
| d0_eq x y : d0 (Eqv x y)
| d0_neg a : d0 a -> d0 (Neg a)
| d0_imp a b : d0 a -> d0 b -> d0 (Imp a b)
| d0_ball k a : d0 a -> d0 (All (Imp (Mem 0 (S k)) a)).

Section Abs.
Variable M : form.
Hypothesis HM : closedk 1 M = true.
Variable B : form -> Prop.

Definition TrM : form := All (All (Imp (Mv M 0) (Imp (Mem 1 0) (Mv M 1)))).

Lemma Mv_closed i k : i < k -> closedk k (Mv M i) = true.
Proof. intros H. unfold Mv. apply closedk_ren_bound. intros _. exact H. Qed.

Lemma TrM_closed : closedk 0 TrM = true.
Proof.
  unfold TrM. simpl. rewrite (Mv_closed 0 2 ltac:(lia)), (Mv_closed 1 2 ltac:(lia)). reflexivity.
Qed.

Lemma TrM_ren s : ren s TrM = TrM.
Proof. apply ren_closed. exact TrM_closed. Qed.

(* the transitivity instance at x = v0, y = v(S k) *)
Lemma tr_inst k : prov B (Imp TrM (Imp (Mv M (S k)) (Imp (Mem 0 (S k)) (Mv M 0)))).
Proof.
  set (X := Imp (Mv M 0) (Imp (Mem 1 0) (Mv M 1))).
  pose proof (p_inst B (All X) 0) as I1.
  pose proof (p_inst B (ren (up (scons 0 sid)) X) (S k)) as I2.
  assert (E : ren (scons (S k) sid) (ren (up (scons 0 sid)) X) = Imp (Mv M (S k)) (Imp (Mem 0 (S k)) (Mv M 0))).
  { unfold X. simpl. rewrite !Mv_ren. reflexivity. }
  rewrite E in I2. simpl in I1. exact (syl B _ _ _ I1 I2).
Qed.

Lemma all_iff a b : prov B (Imp (All (Qf a b)) (Qf (All a) (All b))).
Proof.
  assert (H1 : prov B (Imp (All (Qf a b)) (Imp (All a) (All b)))).
  { apply (syl B _ (All (Imp a b))); [apply all_imp; apply iff_l; apply iff_refl|apply p_dist]. }
  all: fail.
Abort.

Lemma qf_l a b : prov B (Imp (Qf a b) (Imp a b)).
Proof.
  pose proof (ptaut_prov B (PI (PN (PI (PI (PV 0) (PV 1)) (PN (PI (PV 1) (PV 0))))) (PI (PV 0) (PV 1))) (lv [a; b])
    ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.
Lemma qf_r a b : prov B (Imp (Qf a b) (Imp b a)).
Proof.
  pose proof (ptaut_prov B (PI (PN (PI (PI (PV 0) (PV 1)) (PN (PI (PV 1) (PV 0))))) (PI (PV 1) (PV 0))) (lv [a; b])
    ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma all_iff a b : prov B (Imp (All (Qf a b)) (Qf (All a) (All b))).
Proof.
  pose proof (syl B _ _ _ (all_imp B _ _ (qf_l a b)) (p_dist B a b)) as H1.
  pose proof (syl B _ _ _ (all_imp B _ _ (qf_r a b)) (p_dist B b a)) as H2.
  apply (mp2 B _ _ _ H1 H2).
  pose proof (ptaut_prov B
    (PI (PI (PV 0) (PI (PV 1) (PV 2))) (PI (PI (PV 0) (PI (PV 2) (PV 1)))
       (PI (PV 0) (PN (PI (PI (PV 1) (PV 2)) (PN (PI (PV 2) (PV 1))))))))
    (lv [All (Qf a b); All a; All b]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

(* a closed guard comes out of a universal *)
Lemma all_guard T X : ren S T = T -> prov B (Imp (All (Imp T X)) (Imp T (All X))).
Proof.
  intros E. pose proof (p_dist B T X) as D. pose proof (p_vac B T) as V. rewrite E in V.
  apply (p_mp _ _ _ V).
  pose proof (ptaut_prov B (PI (PI (PV 0) (PV 1)) (PI (PI (PV 2) (PI (PV 1) (PV 3))) (PI (PV 2) (PI (PV 0) (PV 3)))))
    (lv [T; All T; All (Imp T X); All X]) ltac:(vm_compute; reflexivity)) as Tt. exact (p_mp _ _ _ D Tt).
Qed.

Lemma chain_mp2 gs X Y W : prov B (Imp X (Imp Y W)) -> prov B (chain gs X) -> prov B (chain gs Y) -> prov B (chain gs W).
Proof. intros T H1 H2. exact (mp2 B _ _ _ H1 H2 (chain_imp2 B gs X Y W T)). Qed.

Lemma chain_mp3 gs X Y Z W : prov B (Imp X (Imp Y (Imp Z W))) ->
  prov B (chain gs X) -> prov B (chain gs Y) -> prov B (chain gs Z) -> prov B (chain gs W).
Proof.
  intros T H1 H2 H3. pose proof (mp2 B _ _ _ H1 H2 (chain_imp2 B gs X Y (Imp Z W) T)) as H4.
  exact (chain_mp B gs Z W H3 H4).
Qed.

Definition qf (p q : pform) : pform := PN (PI (PI p q) (PN (PI q p))).

Theorem abs_d0 phi : d0 phi -> forall n, closedk n phi = true ->
  prov B (chain (G M n) (Imp TrM (Qf (rel M phi) phi))).
Proof.
  induction 1 as [x y|x y|a Da IH|a b Da IHa Db IHb|k a Da IH]; intros n Hc; simpl.
  - apply chain_k.
    pose proof (ptaut_prov B (PI (PV 0) (qf (PV 1) (PV 1))) (lv [TrM; Mem x y]) ltac:(vm_compute; reflexivity)) as T.
    exact T.
  - apply chain_k.
    pose proof (ptaut_prov B (PI (PV 0) (qf (PV 1) (PV 1))) (lv [TrM; Eqv x y]) ltac:(vm_compute; reflexivity)) as T.
    exact T.
  - simpl in Hc. apply (chain_lift B _ _ _ ltac:(idtac) (IH n Hc)).
    pose proof (ptaut_prov B (PI (PI (PV 0) (qf (PV 1) (PV 2))) (PI (PV 0) (qf (PN (PV 1)) (PN (PV 2)))))
      (lv [TrM; rel M a; a]) ltac:(vm_compute; reflexivity)) as T. exact T.
  - simpl in Hc. apply andb_true_iff in Hc as [Ha Hb].
    apply (chain_mp2 _ _ _ _ ltac:(idtac) (IHa n Ha) (IHb n Hb)).
    pose proof (ptaut_prov B
      (PI (PI (PV 0) (qf (PV 1) (PV 2))) (PI (PI (PV 0) (qf (PV 3) (PV 4))) (PI (PV 0) (qf (PI (PV 1) (PV 3)) (PI (PV 2) (PV 4))))))
      (lv [TrM; rel M a; a; rel M b; b]) ltac:(vm_compute; reflexivity)) as T. exact T.
  - simpl in Hc. apply andb_true_iff in Hc as [Hm Ha]. apply andb_true_iff in Hm as [_ Hk].
    apply Nat.ltb_lt in Hk.
    set (C := map (ren S) (G M n)).
    pose proof (IH (S n) Ha) as I. rewrite G_S in I. apply chain_pull in I. fold C in I.
    assert (Tr : prov B (chain C (Imp TrM (Imp (Mv M (S k)) (Imp (Mem 0 (S k)) (Mv M 0)))))).
    { apply chain_k. apply tr_inst. }
    assert (Gk : prov B (chain C (Mv M (S k)))).
    { apply chain_in. unfold C. rewrite <- (Mv_ren M S k). apply in_map. apply G_in. lia. }
    set (A := Imp (Mv M 0) (Imp (Mem 0 (S k)) (rel M a))).
    set (Bf := Imp (Mem 0 (S k)) a).
    assert (P : prov B (chain C (Imp TrM (Qf A Bf)))).
    { apply (chain_mp3 _ _ _ _ _ ltac:(idtac) I Tr Gk).
      pose proof (ptaut_prov B
        (PI (PI (PV 0) (PI (PV 1) (qf (PV 2) (PV 3))))
          (PI (PI (PV 1) (PI (PV 4) (PI (PV 5) (PV 0))))
            (PI (PV 4) (PI (PV 1) (qf (PI (PV 0) (PI (PV 5) (PV 2))) (PI (PV 5) (PV 3)))))))
        (lv [Mv M 0; TrM; rel M a; a; Mv M (S k); Mem 0 (S k)]) ltac:(vm_compute; reflexivity)) as T. exact T. }
    apply p_gen in P. unfold C in P. apply chain_all in P.
    assert (F : prov B (Imp (All (Imp TrM (Qf A Bf))) (Imp TrM (Qf (All A) (All Bf))))).
    { pose proof (all_guard TrM (Qf A Bf) (TrM_ren S)) as G1. pose proof (all_iff A Bf) as G2.
      apply (p_mp _ _ _ G2). apply (p_mp _ _ _ G1).
      pose proof (ptaut_prov B (PI (PI (PV 0) (PI (PV 1) (PV 2))) (PI (PI (PV 2) (PV 3)) (PI (PV 0) (PI (PV 1) (PV 3)))))
        (lv [All (Imp TrM (Qf A Bf)); TrM; All (Qf A Bf); Qf (All A) (All Bf)]) ltac:(vm_compute; reflexivity)) as T.
      exact T. }
    pose proof (chain_lift B _ _ _ F P) as R. unfold A in R. rewrite (Mv0 M HM) in R. exact R.
Qed.
End Abs.
