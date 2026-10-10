(* L2RLogicA.v - lane L2R round 2, 2026-10-09. The natural-deduction layer of L2RLogic.v over an arbitrary axiom set A
   (round 1 fixed A = Gam): DA A G f is prov A (cj G -> f). Hypothesis, modus ponens, deduction theorem, generalization
   under the shifted context, instantiation, existential introduction and elimination, Leibniz; tautologies through
   Kal.taut_prov. Only logic: no axiom of A is used. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Expand Pure.
Import ListNotations.
Open Scope nat_scope.

Arguments Kf : simpl never.
Arguments Df : simpl never.
Arguments Qf : simpl never.
Arguments Xf : simpl never.

Lemma renA_Kf s a b : ren s (Kf a b) = Kf (ren s a) (ren s b). Proof. reflexivity. Qed.
Lemma renA_Df s a b : ren s (Df a b) = Df (ren s a) (ren s b). Proof. reflexivity. Qed.
Lemma renA_Qf s a b : ren s (Qf a b) = Qf (ren s a) (ren s b). Proof. reflexivity. Qed.
Lemma renA_Xf s a : ren s (Xf a) = Xf (ren (up s) a). Proof. reflexivity. Qed.
Lemma renA_Top s : ren s Top = Top. Proof. reflexivity. Qed.

Ltac ptA :=
  apply taut_prov; intros v; unfold Kf, Df, Qf, Xf; simpl;
  repeat (match goal with
          | |- context [v ?x] => destruct (v x)
          | |- context [peval v ?x] => destruct (peval v x)
          end; simpl);
  reflexivity.

Fixpoint cjA (G : list form) : form := match G with [] => Top | h :: r => Kf h (cjA r) end.

Lemma cjA_ren s G : ren s (cjA G) = cjA (map (ren s) G).
Proof. induction G as [|h r IH]; [reflexivity|]. cbn [cjA map]. rewrite renA_Kf, IH. reflexivity. Qed.

Section A.
Variable A : form -> Prop.

Definition DA (G : list form) (f : form) : Prop := prov A (Imp (cjA G) f).

Lemma TopA : prov A Top. Proof. apply p_gen. apply p_refl. Qed.

Lemma qmp a b : prov A a -> prov A (Imp a b) -> prov A b.
Proof. intros H1 H2. exact (p_mp _ _ _ H1 H2). Qed.
Lemma qmp2 a b c : prov A a -> prov A b -> prov A (Imp a (Imp b c)) -> prov A c.
Proof. intros H1 H2 H3. exact (qmp _ _ H2 (qmp _ _ H1 H3)). Qed.
Lemma qmp3 a b c d : prov A a -> prov A b -> prov A c -> prov A (Imp a (Imp b (Imp c d))) -> prov A d.
Proof. intros H1 H2 H3 H4. exact (qmp _ _ H3 (qmp2 _ _ _ H1 H2 H4)). Qed.

Lemma A_thm G f : prov A f -> DA G f.
Proof. intros H. unfold DA. apply (qmp f); [exact H|]. ptA. Qed.
Lemma A_mp G a b : DA G (Imp a b) -> DA G a -> DA G b.
Proof. unfold DA. intros H1 H2. apply (qmp2 _ _ _ H1 H2). ptA. Qed.
Lemma A_hyp G f : In f G -> DA G f.
Proof.
  induction G as [|h r IH]; simpl; [intros []|]. intros [E|H].
  - subst. unfold DA. simpl. ptA.
  - pose proof (IH H) as I. unfold DA in *. simpl. apply (qmp _ _ I). ptA.
Qed.
Lemma A_intro G a b : DA (a :: G) b -> DA G (Imp a b).
Proof. unfold DA. simpl. intros H. apply (qmp _ _ H). ptA. Qed.
Lemma A_elim G a b : DA G (Imp a b) -> DA (a :: G) b.
Proof. unfold DA. simpl. intros H. apply (qmp _ _ H). ptA. Qed.
Lemma A_t1 G a b : prov A (Imp a b) -> DA G a -> DA G b.
Proof. intros H1 H2. exact (A_mp _ _ _ (A_thm _ _ H1) H2). Qed.
Lemma A_t2 G a b c : prov A (Imp a (Imp b c)) -> DA G a -> DA G b -> DA G c.
Proof. intros H H1 H2. exact (A_mp _ _ _ (A_mp _ _ _ (A_thm _ _ H) H1) H2). Qed.
Lemma A_t3 G a b c d : prov A (Imp a (Imp b (Imp c d))) -> DA G a -> DA G b -> DA G c -> DA G d.
Proof. intros H H1 H2 H3. exact (A_mp _ _ _ (A_t2 _ _ _ _ H H1 H2) H3). Qed.

Lemma A_cj G G' : (forall f, In f G -> DA G' f) -> DA G' (cjA G).
Proof.
  induction G as [|h r IH]; intros I; simpl.
  - apply A_thm. exact TopA.
  - apply (A_t2 _ h (cjA r)); [ptA|apply I; left; reflexivity|].
    apply IH. intros f Hf. apply I. right. exact Hf.
Qed.
Lemma A_ctx G G' f : (forall g, In g G -> DA G' g) -> DA G f -> DA G' f.
Proof. intros I H. exact (A_mp _ _ _ (A_thm _ _ H) (A_cj _ _ I)). Qed.
Lemma A_weak G G' f : (forall g, In g G -> In g G') -> DA G f -> DA G' f.
Proof. intros I. apply A_ctx. intros g Hg. apply A_hyp. apply I. exact Hg. Qed.
Lemma A_cut G a b : DA G a -> DA (a :: G) b -> DA G b.
Proof. intros H1 H2. exact (A_mp _ _ _ (A_intro _ _ _ H2) H1). Qed.
Lemma A_add G a f : DA G f -> DA (a :: G) f.
Proof. intros H. apply (A_weak G); [intros g Hg; right; exact Hg|exact H]. Qed.
Lemma A_ren G f s : DA G f -> DA (map (ren s) G) (ren s f).
Proof. unfold DA. intros H. rewrite <- cjA_ren. exact (ren_adm _ _ s H). Qed.

Lemma A_all G f : DA (map (ren S) G) f -> DA G (All f).
Proof.
  unfold DA. rewrite <- cjA_ren. intros H.
  pose proof (p_mp _ _ _ (p_gen _ _ H) (p_dist A (ren S (cjA G)) f)) as H2.
  exact (syl _ _ _ _ (p_vac A (cjA G)) H2).
Qed.
Lemma A_inst G f y : DA G (All f) -> DA G (ren (scons y sid) f).
Proof. intros H. exact (A_t1 _ _ _ (p_inst _ f y) H). Qed.
Lemma A_exI G f y : DA G (ren (scons y sid) f) -> DA G (Xf f).
Proof. intros H. exact (A_t1 _ _ _ (rule_exi _ f y) H). Qed.

Lemma exA_out f g : prov A (Imp (All (Imp f (ren S g))) (Imp (Xf f) g)).
Proof.
  assert (H1 : prov A (Imp (All (Imp f (ren S g))) (All (Imp (Neg (ren S g)) (Neg f))))) by (apply all_imp; ptA).
  pose proof (p_dist A (Neg (ren S g)) (Neg f)) as H2.
  pose proof (p_vac A (Neg g)) as H3. simpl in H3.
  apply (qmp3 _ _ _ _ H1 H2 H3). ptA.
Qed.
Lemma A_exE G f g : DA G (Xf f) -> DA (f :: map (ren S) G) (ren S g) -> DA G g.
Proof.
  intros H1 H2. pose proof (A_all _ _ (A_intro _ _ _ H2)) as H4. exact (A_t2 _ _ _ _ (exA_out f g) H4 H1).
Qed.
Lemma A_leib G a x y : DA G (Eqv x y) -> DA G (ren (scons x sid) a) -> DA G (ren (scons y sid) a).
Proof. intros H1 H2. exact (A_t2 _ _ _ _ (p_leib _ a x y) H1 H2). Qed.

Lemma A_and G a b : DA G a -> DA G b -> DA G (Kf a b).
Proof. intros H1 H2. apply (A_t2 _ a b); [ptA|exact H1|exact H2]. Qed.
Lemma A_andl G a b : DA G (Kf a b) -> DA G a.
Proof. intros H. apply (A_t1 _ (Kf a b)); [ptA|exact H]. Qed.
Lemma A_andr G a b : DA G (Kf a b) -> DA G b.
Proof. intros H. apply (A_t1 _ (Kf a b)); [ptA|exact H]. Qed.
Lemma A_iffl G a b : DA G (Qf a b) -> DA G a -> DA G b.
Proof. intros H1 H2. apply (A_t2 _ (Qf a b) a); [ptA|exact H1|exact H2]. Qed.
Lemma A_iffr G a b : DA G (Qf a b) -> DA G b -> DA G a.
Proof. intros H1 H2. apply (A_t2 _ (Qf a b) b); [ptA|exact H1|exact H2]. Qed.
Lemma A_iffi G a b : DA (a :: G) b -> DA (b :: G) a -> DA G (Qf a b).
Proof. intros H1 H2. apply (A_t2 _ (Imp a b) (Imp b a)); [ptA|exact (A_intro _ _ _ H1)|exact (A_intro _ _ _ H2)]. Qed.
Lemma A_absurd G a c : DA G a -> DA G (Neg a) -> DA G c.
Proof. intros H1 H2. apply (A_t2 _ a (Neg a)); [ptA|exact H1|exact H2]. Qed.

Lemma A_exE2 G a b g : DA G (Xf (Kf a b)) -> DA (a :: b :: map (ren S) G) (ren S g) -> DA G g.
Proof.
  intros H1 H2. apply (A_exE _ _ _ H1). apply (A_cut _ a); [apply (A_andl _ a b); apply A_hyp; left; reflexivity|].
  apply (A_cut _ b); [apply (A_andr _ a b); apply A_hyp; right; left; reflexivity|].
  apply (A_weak (a :: b :: map (ren S) G)); [|exact H2]. intros h Hh; simpl in Hh |- *; tauto.
Qed.

(* from a context to the guard chain of Rel2 and back *)
Fixpoint chainA (gs : list form) (f : form) : form := match gs with [] => f | g :: r => Imp g (chainA r f) end.
Lemma chain_gen gs : forall f h, prov A (Imp h (Imp (cjA gs) f)) -> prov A (Imp h (chainA gs f)).
Proof.
  induction gs as [|g r IH]; intros f h H; simpl in *.
  - apply (qmp2 _ _ _ H TopA). ptA.
  - assert (H2 : prov A (Imp (Kf h g) (Imp (cjA r) f))) by (apply (qmp _ _ H); ptA).
    pose proof (IH f (Kf h g) H2) as H3. apply (qmp _ _ H3). ptA.
Qed.
Lemma unchain_gen gs : forall f h, prov A (Imp h (chainA gs f)) -> prov A (Imp h (Imp (cjA gs) f)).
Proof.
  induction gs as [|g r IH]; intros f h H; simpl in *.
  - apply (qmp _ _ H). ptA.
  - assert (H2 : prov A (Imp (Kf h g) (chainA r f))) by (apply (qmp _ _ H); ptA).
    pose proof (IH f (Kf h g) H2) as H3. apply (qmp _ _ H3). ptA.
Qed.
Lemma A_chain gs f : DA gs f -> prov A (chainA gs f).
Proof.
  intros H. unfold DA in H. assert (H1 : prov A (Imp Top (Imp (cjA gs) f))) by (apply (qmp _ _ H); ptA).
  exact (qmp _ _ TopA (chain_gen gs f Top H1)).
Qed.
Lemma A_unchain gs f : prov A (chainA gs f) -> DA gs f.
Proof.
  intros H. assert (H1 : prov A (Imp Top (chainA gs f))) by (apply (qmp _ _ H); ptA).
  pose proof (unchain_gen gs f Top H1) as H2. unfold DA. exact (qmp _ _ TopA H2).
Qed.
End A.

Arguments DA : simpl never.

Ltac rsA := repeat progress (rewrite ?renA_Kf, ?renA_Df, ?renA_Qf, ?renA_Xf, ?renA_Top; cbn).
Ltac rsAin H := repeat progress (rewrite ?renA_Kf, ?renA_Df, ?renA_Qf, ?renA_Xf, ?renA_Top in H; cbn in H).
Ltac hypA := apply A_hyp; repeat (first [left; reflexivity | right]); fail.
Ltac haveA name f := match goal with |- DA ?A ?G _ => assert (name : DA A G f) end.
Ltac addA f := apply (A_cut _ _ f).
