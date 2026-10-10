(* Rel.v - relativization of derivations to a class. M is a formula with at most the variable 0 free (a class
   M = {x | M(x)}). rel M f bounds every quantifier of f by M: All a becomes All (M -> a). Free variables are
   handled by guards: chain (G n) g = M(0) -> M(1) -> ... -> M(n-1) -> g.
   rel_sound: if every axiom of A (with any n >= 1 guards covering its free variables) is relativized-derivable in B,
   then every theorem of A is; rel_con: then A |- Bot implies B |- Bot, provided B |- exists x M(x).
   Lane LCH, 2026-10-09. Uses the Cohen library of forcing-src/general unchanged. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Kal Checks Ax Expand Replay.
Import ListNotations.
Open Scope nat_scope.

(* ---- facts about closedk and free *)
Lemma closedk_mono f : forall k k', k <= k' -> closedk k f = true -> closedk k' f = true.
Proof.
  induction f; intros k k' Hk H; simpl in *.
  - apply andb_true_iff in H as [H1 H2]. apply Nat.ltb_lt in H1, H2. apply andb_true_iff.
    split; apply Nat.ltb_lt; lia.
  - apply andb_true_iff in H as [H1 H2]. apply Nat.ltb_lt in H1, H2. apply andb_true_iff.
    split; apply Nat.ltb_lt; lia.
  - rewrite forallb_forall in *. intros x Hx. specialize (H x Hx). apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
  - eauto.
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; eauto.
  - apply (IHf (S k) (S k')); [lia|exact H].
Qed.

Lemma free_ren f : forall i s, free i f = true -> free (s i) (ren s f) = true.
Proof.
  induction f; intros i s H; simpl in *.
  - apply orb_true_iff in H as [E|E]; apply Nat.eqb_eq in E; subst; rewrite Nat.eqb_refl;
      [reflexivity|apply orb_true_r].
  - apply orb_true_iff in H as [E|E]; apply Nat.eqb_eq in E; subst; rewrite Nat.eqb_refl;
      [reflexivity|apply orb_true_r].
  - apply existsb_exists in H as [x [Hx E]]. apply Nat.eqb_eq in E. subst x.
    apply existsb_exists. exists (s i). split; [apply in_map; exact Hx|apply Nat.eqb_refl].
  - auto.
  - apply orb_true_iff in H as [H|H]; [rewrite IHf1|rewrite IHf2]; auto using orb_true_r.
  - exact (IHf (S i) (up s) H).
Qed.

Lemma closedk_ren_bound f : forall t n, (forall i, t i < n) -> closedk n (ren t f) = true.
Proof.
  induction f; intros t m H; simpl.
  - apply andb_true_iff. split; apply Nat.ltb_lt; apply H.
  - apply andb_true_iff. split; apply Nat.ltb_lt; apply H.
  - apply forallb_forall. intros x Hx. apply in_map_iff in Hx as [y [<- _]]. apply Nat.ltb_lt. apply H.
  - auto.
  - apply andb_true_iff. split; auto.
  - apply IHf. intros [|i]; simpl; [lia|]. specialize (H i). lia.
Qed.

(* ---- guard chains, for any axiom set *)
Fixpoint chain (gs : list form) (f : form) : form :=
  match gs with [] => f | g :: r => Imp g (chain r f) end.

Lemma ren_chain gs f s : ren s (chain gs f) = chain (map (ren s) gs) (ren s f).
Proof. induction gs as [|g r IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section Chains.
Variable B : form -> Prop.

Lemma chain_k gs f : prov B f -> prov B (chain gs f).
Proof.
  induction gs as [|g r IH]; simpl; intros H; [exact H|].
  apply (p_mp _ (chain r f)); [apply IH; exact H|apply p_k].
Qed.

Lemma chain_imp gs X Y : prov B (Imp X Y) -> prov B (Imp (chain gs X) (chain gs Y)).
Proof.
  induction gs as [|g r IH]; simpl; intros H; [exact H|].
  apply (p_mp _ _ _ (IH H)).
  pose proof (ptaut_prov B (PI (PI (PV 0) (PV 1)) (PI (PI (PV 2) (PV 0)) (PI (PV 2) (PV 1))))
    (lv [chain r X; chain r Y; g]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma chain_lift gs X Y : prov B (Imp X Y) -> prov B (chain gs X) -> prov B (chain gs Y).
Proof. intros H1 H2. exact (p_mp _ _ _ H2 (chain_imp gs X Y H1)). Qed.

Lemma chain_imp2 gs X Y Z : prov B (Imp X (Imp Y Z)) ->
  prov B (Imp (chain gs X) (Imp (chain gs Y) (chain gs Z))).
Proof.
  induction gs as [|g r IH]; simpl; intros H; [exact H|].
  apply (p_mp _ _ _ (IH H)).
  pose proof (ptaut_prov B
    (PI (PI (PV 0) (PI (PV 1) (PV 2))) (PI (PI (PV 3) (PV 0)) (PI (PI (PV 3) (PV 1)) (PI (PV 3) (PV 2)))))
    (lv [chain r X; chain r Y; chain r Z; g]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma chain_mp gs X Y : prov B (chain gs X) -> prov B (chain gs (Imp X Y)) -> prov B (chain gs Y).
Proof.
  intros H1 H2.
  assert (T : prov B (Imp X (Imp (Imp X Y) Y))).
  { pose proof (ptaut_prov B (PI (PV 0) (PI (PI (PV 0) (PV 1)) (PV 1))) (lv [X; Y])
      ltac:(vm_compute; reflexivity)) as T. exact T. }
  exact (mp2 _ _ _ _ H1 H2 (chain_imp2 gs _ _ _ T)).
Qed.

Lemma chain_self gs X : prov B (Imp X (chain gs X)).
Proof.
  induction gs as [|g r IH]; simpl.
  - pose proof (ptaut_prov B (PI (PV 0) (PV 0)) (lv [X]) ltac:(vm_compute; reflexivity)) as T. exact T.
  - apply (p_mp _ _ _ IH).
    pose proof (ptaut_prov B (PI (PI (PV 0) (PV 1)) (PI (PV 0) (PI (PV 2) (PV 1))))
      (lv [X; chain r X; g]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma chain_in gs X : In X gs -> prov B (chain gs X).
Proof.
  induction gs as [|g r IH]; simpl; [intros []|]. intros [<-|H].
  - apply chain_self.
  - apply (p_mp _ (chain r X)); [apply IH; exact H|apply p_k].
Qed.

Lemma pull_imp gs g f : prov B (Imp (Imp g (chain gs f)) (chain gs (Imp g f))).
Proof.
  induction gs as [|h r IH]; simpl.
  - pose proof (ptaut_prov B (PI (PV 0) (PV 0)) (lv [Imp g f]) ltac:(vm_compute; reflexivity)) as T. exact T.
  - apply (p_mp _ _ _ IH).
    pose proof (ptaut_prov B
      (PI (PI (PI (PV 0) (PV 1)) (PV 2)) (PI (PI (PV 0) (PI (PV 3) (PV 1))) (PI (PV 3) (PV 2))))
      (lv [g; chain r f; chain r (Imp g f); h]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma chain_pull gs g f : prov B (Imp g (chain gs f)) -> prov B (chain gs (Imp g f)).
Proof. intros H. exact (p_mp _ _ _ H (pull_imp gs g f)). Qed.

Lemma all_chain gs f : prov B (Imp (All (chain (map (ren S) gs) f)) (chain gs (All f))).
Proof.
  induction gs as [|g r IH]; simpl.
  - pose proof (ptaut_prov B (PI (PV 0) (PV 0)) (lv [All f]) ltac:(vm_compute; reflexivity)) as T. exact T.
  - set (C := chain (map (ren S) r) f).
    pose proof (p_dist B (ren S g) C) as D. pose proof (p_vac B g) as Vg.
    apply (p_mp _ _ _ IH). apply (p_mp _ _ _ Vg). apply (p_mp _ _ _ D).
    pose proof (ptaut_prov B
      (PI (PI (PV 0) (PI (PV 1) (PV 2))) (PI (PI (PV 3) (PV 1)) (PI (PI (PV 2) (PV 4)) (PI (PV 0) (PI (PV 3) (PV 4))))))
      (lv [All (Imp (ren S g) C); All (ren S g); All C; g; chain r (All f)]) ltac:(vm_compute; reflexivity)) as T.
    exact T.
Qed.

Lemma chain_all gs f : prov B (All (chain (map (ren S) gs) f)) -> prov B (chain gs (All f)).
Proof. intros H. exact (p_mp _ _ _ H (all_chain gs f)). Qed.
End Chains.

(* ---- the relativization *)
Section Rel.
Variable M : form.
Hypothesis HM : closedk 1 M = true.

Fixpoint rel (f : form) : form :=
  match f with
  | Mem x y => Mem x y
  | Eqv x y => Eqv x y
  | Pr p a => Pr p a
  | Neg a => Neg (rel a)
  | Imp a b => Imp (rel a) (rel b)
  | All a => All (Imp M (rel a))
  end.

Definition Mv (i : nat) : form := ren (fun _ => i) M.
Definition G (n : nat) : list form := map Mv (seq 0 n).

Lemma M_free n : free n M = true -> n = 0.
Proof. intros H. pose proof (closedk_free M 1 n HM H). lia. Qed.

Lemma M_ren t : ren t M = Mv (t 0).
Proof. unfold Mv. apply ren_free. intros n Hn. rewrite (M_free n Hn). reflexivity. Qed.

Lemma Mv0 : Mv 0 = M.
Proof. unfold Mv. rewrite <- (ren_id M) at 2. apply ren_free. intros n Hn. rewrite (M_free n Hn). reflexivity. Qed.

Lemma M_up s : ren (up s) M = M.
Proof. rewrite M_ren. simpl. apply Mv0. Qed.

Lemma Mv_ren s i : ren s (Mv i) = Mv (s i).
Proof. unfold Mv. rewrite ren_comp. reflexivity. Qed.

Lemma G_S n : G (S n) = Mv 0 :: map (ren S) (G n).
Proof.
  unfold G. simpl. f_equal. rewrite map_map. rewrite <- seq_shift, map_map.
  apply map_ext. intros i. symmetry. apply Mv_ren.
Qed.

Lemma G_in k n : k < n -> In (Mv k) (G n).
Proof. intros H. unfold G. apply in_map. apply in_seq. lia. Qed.

Lemma rel_ren f : forall s, rel (ren s f) = ren s (rel f).
Proof.
  induction f; intros s; simpl; try reflexivity.
  - rewrite IHf. reflexivity.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite IHf, M_up. reflexivity.
Qed.

Lemma M_free_S n : free (S n) M = false.
Proof. destruct (free (S n) M) eqn:E; [apply M_free in E; discriminate|reflexivity]. Qed.

Lemma free_rel f : forall n, free n (rel f) = free n f.
Proof.
  induction f; intros m; simpl; try reflexivity.
  - apply IHf.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite M_free_S, IHf. reflexivity.
Qed.

Lemma closedk_rel f : forall k, closedk k (rel f) = closedk k f.
Proof.
  induction f; intros k; simpl; try reflexivity.
  - apply IHf.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite (closedk_mono M 1 (S k) ltac:(lia) HM), IHf. reflexivity.
Qed.

Section Sound.
Variables A B : form -> Prop.
Hypothesis HAren : forall f s, A f -> A (ren s f).
Hypothesis HA : forall f, A f -> forall n, 1 <= n -> closedk n f = true -> prov B (chain (G n) (rel f)).

Theorem rel_sound : forall f, prov A f ->
  forall s n, 1 <= n -> closedk n (ren s f) = true -> prov B (chain (G n) (ren s (rel f))).
Proof.
  intros f P. induction P; intros s n Hn Hc.
  - (* axiom *)
    rewrite <- rel_ren. exact (HA _ (HAren _ s H) n Hn Hc).
  - simpl. apply chain_k. apply p_k.
  - simpl. apply chain_k. apply p_s.
  - simpl. apply chain_k. apply p_c.
  - (* modus ponens: the free variables of a outside those of b go to the guarded variable 0 *)
    set (t := fun i => if s i <? n then s i else 0).
    assert (Ht : forall i, t i < n) by (intros i; unfold t; destruct (s i <? n) eqn:E;
      [apply Nat.ltb_lt in E; exact E|lia]).
    assert (Etb : ren t b = ren s b).
    { apply ren_free. intros i Fi. unfold t. pose proof (free_ren b i s Fi) as F2.
      pose proof (closedk_free _ n _ Hc F2) as L. replace (s i <? n) with true by (symmetry; apply Nat.ltb_lt; exact L).
      reflexivity. }
    assert (Ca : closedk n (ren t a) = true) by (apply closedk_ren_bound; exact Ht).
    assert (Cab : closedk n (ren t (Imp a b)) = true).
    { simpl. rewrite Ca, Etb, Hc. reflexivity. }
    pose proof (IHP1 t n Hn Ca) as H1. pose proof (IHP2 t n Hn Cab) as H2. simpl in H2.
    pose proof (chain_mp _ _ _ _ H1 H2) as H3.
    rewrite <- rel_ren, Etb, rel_ren in H3. exact H3.
  - (* generalization *)
    simpl in Hc. simpl. rewrite M_up.
    pose proof (IHP (up s) (S n) ltac:(lia) Hc) as H. rewrite G_S in H.
    apply chain_pull in H. apply p_gen in H. apply chain_all in H. rewrite Mv0 in H. exact H.
  - (* instantiation *)
    simpl. rewrite M_up. rewrite <- rel_ren, ren_scons_up, rel_ren.
    set (c := ren (up s) (rel a)).
    set (k := if free 0 (ren (up s) a) then s y else 0).
    assert (Hk : k < n /\ ren (scons k sid) c = ren (scons (s y) sid) c).
    { unfold k. destruct (free 0 (ren (up s) a)) eqn:F.
      - split; [|reflexivity]. simpl in Hc. apply andb_true_iff in Hc as [_ Hc2].
        rewrite ren_scons_up in Hc2. pose proof (free_ren _ 0 (scons (s y) sid) F) as F2. simpl in F2.
        exact (closedk_free _ n _ Hc2 F2).
      - split; [lia|]. apply ren_free. intros [|i] Fi; [|reflexivity].
        unfold c in Fi. rewrite <- rel_ren, free_rel in Fi. congruence. }
    destruct Hk as [Hk Ek]. rewrite <- Ek.
    pose proof (p_inst B (Imp M c) k) as I. simpl in I. rewrite M_ren in I. simpl in I.
    assert (I2 : prov B (Imp (Mv k) (Imp (All (Imp M c)) (ren (scons k sid) c)))).
    { apply (p_mp _ _ _ I).
      pose proof (ptaut_prov B (PI (PI (PV 0) (PI (PV 1) (PV 2))) (PI (PV 1) (PI (PV 0) (PV 2))))
        (lv [All (Imp M c); Mv k; ren (scons k sid) c]) ltac:(vm_compute; reflexivity)) as T. exact T. }
    exact (chain_lift _ _ _ _ I2 (chain_in _ _ _ (G_in k n Hk))).
  - (* vacuous quantification *)
    simpl. rewrite M_up. rewrite <- rel_ren. rewrite ren_S_up. rewrite rel_ren.
    apply chain_k. set (r := ren s (rel a)).
    pose proof (p_vac B r) as V1.
    assert (K1 : prov B (Imp (All (ren S r)) (All (Imp M (ren S r))))).
    { apply all_imp. apply p_k. }
    exact (syl _ _ _ _ V1 K1).
  - (* distribution *)
    simpl. rewrite M_up. apply chain_k.
    set (ra := ren (up s) (rel a)). set (rb := ren (up s) (rel b)).
    assert (T1 : prov B (Imp (All (Imp M (Imp ra rb))) (All (Imp (Imp M ra) (Imp M rb))))).
    { apply all_imp.
      pose proof (ptaut_prov B (PI (PI (PV 0) (PI (PV 1) (PV 2))) (PI (PI (PV 0) (PV 1)) (PI (PV 0) (PV 2))))
        (lv [M; ra; rb]) ltac:(vm_compute; reflexivity)) as T. exact T. }
    exact (syl _ _ _ _ T1 (p_dist B (Imp M ra) (Imp M rb))).
  - simpl. apply chain_k. apply p_refl.
  - (* Leibniz *)
    simpl. rewrite <- !rel_ren, !ren_scons_up, !rel_ren. apply chain_k. apply p_leib.
Qed.

(* closed theorems: the one guard goes, because B proves that M is not empty *)
Hypothesis HEX : prov B (Xf M).

Theorem rel_closed f : prov A f -> closedk 0 f = true -> prov B (rel f).
Proof.
  intros P Hc.
  pose proof (rel_sound f P sid 1 (le_n 1) ltac:(rewrite (ren_closed f sid Hc); exact (closedk_mono f 0 1 ltac:(lia) Hc)))
    as H.
  rewrite (ren_closed (rel f) sid) in H by (rewrite closedk_rel; exact Hc).
  simpl in H. rewrite Mv0 in H.
  assert (F0 : free 0 (rel f) = false).
  { destruct (free 0 (rel f)) eqn:E; [|reflexivity].
    rewrite free_rel in E. pose proof (closedk_free f 0 0 Hc E). lia. }
  pose proof (rule_exel B M (rel f) 0 F0 H) as E.
  assert (EM : ren (absk 0) M = M).
  { rewrite <- (ren_id M) at 2. apply ren_free. intros m Hm. rewrite (M_free m Hm). reflexivity. }
  rewrite EM in E. exact (p_mp _ _ _ HEX E).
Qed.

Theorem rel_con : prov A Bot -> prov B Bot.
Proof.
  intros P. pose proof (rel_closed Bot P eq_refl) as H. simpl in H.
  assert (H2 : prov B (All (Imp M (Eqv 0 0)))).
  { apply p_gen. apply (p_mp _ (Eqv 0 0)); [apply p_refl|apply p_k]. }
  apply (mp2 _ _ _ _ H2 H).
  pose proof (ptaut_prov B (PI (PV 0) (PI (PN (PV 0)) (PV 1))) (lv [All (Imp M (Eqv 0 0)); Bot])
    ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.
End Sound.
End Rel.
