(* Replay.v - the kernel's derivations, checked again in Rocq. A checker for the rules of lib/zfc.pmp and lib/logic.pmp
   (ZFC mode: use spec gen mp taut exi exel alli inst leib refl k s c dist vac sep coll), on de Bruijn formulas, and its
   soundness for prov. A theorem's variables are numbered by one frame per theorem; a rule's side conditions become
   equations between formulas (the named substitutions, with their capture checks, are the kernel's; here the
   instance is the de Bruijn one, and the check is that the written formula equals it). Every entry of the registry is
   a formula with the placeholder hypotheses it rests on; a checked theorem becomes a new entry. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Sub Expand.
Import ListNotations.
Open Scope nat_scope.

(* ---- renaming the free variables of a derivable formula is admissible in every axiom set: generalize variable 0,
   instantiate it, N times *)
Lemma gen_inst (A : form -> Prop) a y : prov A a -> prov A (ren (scons y sid) a).
Proof. intros H. apply (p_mp _ (All a)); [apply p_gen; exact H|apply p_inst]. Qed.

Definition rho_t (s : nat -> nat) (N t : nat) : nat -> nat := fun i => if i <? t then s i + N - t else i - t.

Theorem ren_adm (A : form -> Prop) a s : prov A a -> prov A (ren s a).
Proof.
  intros H. set (N := fvb a).
  assert (Hstep : forall t, t <= N -> prov A (ren (rho_t s N t) a)).
  { induction t as [|t IH]; intros Ht.
    - rewrite (ren_free a _ (fun n => n)); [rewrite ren_id; exact H|]. intros n _. unfold rho_t. simpl. lia.
    - pose proof (gen_inst A _ (s t + N - S t) (IH ltac:(lia))) as G. rewrite ren_comp in G.
      rewrite (ren_free a _ (fun i => scons (s t + N - S t) sid (rho_t s N t i))); [exact G|].
      intros i Fi. pose proof (free_fvb a i Fi) as Li. fold N in Li. unfold rho_t, scons, sid.
      destruct (i <? S t) eqn:E1; destruct (i <? t) eqn:E2;
        apply Nat.ltb_lt in E1 || apply Nat.ltb_ge in E1; apply Nat.ltb_lt in E2 || apply Nat.ltb_ge in E2.
      + destruct (s i + N - t) eqn:E; [lia|]. lia.
      + assert (i = t) by lia. subst i. replace (t - t) with 0 by lia. reflexivity.
      + lia.
      + destruct (i - t) eqn:E; [lia|]. lia. }
  pose proof (Hstep N (le_n N)) as R. rewrite (ren_free a _ s) in R; [exact R|].
  intros i Fi. pose proof (free_fvb a i Fi) as Li. fold N in Li. unfold rho_t.
  replace (i <? N) with true by (symmetry; apply Nat.ltb_lt; exact Li). lia.
Qed.

(* ---- the rules' shapes, and the formulas they need *)
Definition absk (k : nat) : nat -> nat := fun j => if j =? k then 0 else S j.

Lemma absk_nofree f k : free k f = false -> ren (absk k) f = ren S f.
Proof.
  intros H. apply ren_free. intros n Fn. unfold absk. destruct (n =? k) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. subst. congruence.
Qed.

Section Rules.
Variable A : form -> Prop.

Lemma syl a b c : prov A (Imp a b) -> prov A (Imp b c) -> prov A (Imp a c).
Proof.
  intros H1 H2. apply (mp2 A _ _ _ H1 H2).
  pose proof (ptaut_prov A (PI (PI (PV 0) (PV 1)) (PI (PI (PV 1) (PV 2)) (PI (PV 0) (PV 2)))) (lv [a; b; c])
    ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma contra a b : prov A (Imp a b) -> prov A (Imp (Neg b) (Neg a)).
Proof.
  intros H. apply (p_mp _ _ _ H).
  pose proof (ptaut_prov A (PI (PI (PV 0) (PV 1)) (PI (PN (PV 1)) (PN (PV 0)))) (lv [a; b])
    ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma gen_k F k : prov A F -> prov A (All (ren (absk k) F)).
Proof. intros H. apply p_gen. apply ren_adm. exact H. Qed.

Lemma rule_exi f t : prov A (Imp (ren (scons t sid) f) (Neg (All (Neg f)))).
Proof.
  pose proof (p_inst A (Neg f) t) as I. simpl in I.
  apply (p_mp _ _ _ I).
  pose proof (ptaut_prov A (PI (PI (PV 0) (PN (PV 1))) (PI (PV 1) (PN (PV 0)))) (lv [All (Neg f); ren (scons t sid) f])
    ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma rule_alli H f k : free k H = false -> prov A (Imp H f) -> prov A (Imp H (All (ren (absk k) f))).
Proof.
  intros Fk D. pose proof (gen_k _ k D) as G. simpl in G. rewrite (absk_nofree H k Fk) in G.
  pose proof (p_mp _ _ _ G (p_dist A (ren S H) (ren (absk k) f))) as D2.
  exact (syl _ _ _ (p_vac A H) D2).
Qed.

Lemma rule_exel P G k : free k G = false -> prov A (Imp P G) -> prov A (Imp (Neg (All (Neg (ren (absk k) P)))) G).
Proof.
  intros Fk D. pose proof (contra _ _ D) as C. pose proof (gen_k _ k C) as Gn. simpl in Gn.
  rewrite (absk_nofree G k Fk) in Gn.
  pose proof (p_mp _ _ _ Gn (p_dist A (Neg (ren S G)) (Neg (ren (absk k) P)))) as D2.
  pose proof (p_vac A (Neg G)) as V. simpl in V.
  pose proof (syl _ _ _ V D2) as E. pose proof (contra _ _ E) as E2.
  apply (p_mp _ _ _ E2).
  pose proof (ptaut_prov A (PI (PI (PV 0) (PN (PN (PV 1)))) (PI (PV 0) (PV 1)))
    (lv [Neg (All (Neg (ren (absk k) P))); G]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.
End Rules.

(* ---- tautologies: the atoms (the subformulas that are not N or I, equal ones once), every assignment *)
Fixpoint findf (a : form) (l : list form) : nat :=
  match l with [] => 0 | b :: r => if form_eqb a b then 0 else S (findf a r) end.
Fixpoint addat (l : list form) (f : form) : list form :=
  match f with
  | Neg a => addat l a
  | Imp a b => addat (addat l a) b
  | _ => if existsb (form_eqb f) l then l else l ++ [f]
  end.
Fixpoint topf (at_ : list form) (f : form) : pform :=
  match f with Neg a => PN (topf at_ a) | Imp a b => PI (topf at_ a) (topf at_ b) | _ => PV (findf f at_) end.

Definition updb (w : nat -> bool) (m : nat) (b : bool) : nat -> bool := fun i => if i =? m then b else w i.
Fixpoint allbits (n : nat) (p : pform) (w : nat -> bool) : bool :=
  match n with 0 => pval w p | S m => allbits m p (updb w m true) && allbits m p (updb w m false) end.

Lemma allbits_ok n p : forall w, allbits n p w = true -> forall w', (forall i, n <= i -> w' i = w i) -> pval w' p = true.
Proof.
  induction n as [|m IH]; intros w H w' E; simpl in H.
  - rewrite <- H. apply pval_ext. intros i _. apply E. lia.
  - apply andb_true_iff in H as [H1 H2]. destruct (w' m) eqn:Wm.
    + apply (IH _ H1). intros i Hi. unfold updb. destruct (i =? m) eqn:Ei; [apply Nat.eqb_eq in Ei; subst; exact Wm|].
      apply Nat.eqb_neq in Ei. apply E. lia.
    + apply (IH _ H2). intros i Hi. unfold updb. destruct (i =? m) eqn:Ei; [apply Nat.eqb_eq in Ei; subst; exact Wm|].
      apply Nat.eqb_neq in Ei. apply E. lia.
Qed.

Lemma form_eqb_refl g : form_eqb g g = true.
Proof.
  induction g; simpl; rewrite ?Nat.eqb_refl; simpl; auto; try (rewrite IHg1, IHg2; reflexivity).
  induction l as [|x l IHl]; simpl; [reflexivity|]. rewrite Nat.eqb_refl. exact IHl.
Qed.

Lemma findf_lt a l : In a l -> findf a l < length l.
Proof.
  induction l as [|b r IH]; simpl; [tauto|]. destruct (form_eqb a b) eqn:E; [lia|].
  intros [->|H]; [rewrite form_eqb_refl in E; discriminate|]. specialize (IH H). lia.
Qed.

Lemma findf_nth a l d : In a l -> nth (findf a l) l d = a.
Proof.
  induction l as [|b r IH]; simpl; [tauto|]. destruct (form_eqb a b) eqn:E.
  - intros _. symmetry. apply form_eqb_true. exact E.
  - intros [->|H]; [rewrite form_eqb_refl in E; discriminate|]. apply IH. exact H.
Qed.

Lemma addat_mono l f a : In a l -> In a (addat l f).
Proof.
  revert l. induction f as [x y|x y|p args|g IH|g IH1 h IH2|g IH]; intros l H; simpl; auto;
    destruct (existsb _ l); try exact H; apply in_or_app; left; exact H.
Qed.

Lemma addat_atom l f a : In a [f] -> In a (if existsb (form_eqb f) l then l else l ++ [f]).
Proof.
  intros [<-|[]]. destruct (existsb (form_eqb f) l) eqn:E.
  - apply existsb_exists in E as [b [Hb Eb]]. apply form_eqb_true in Eb. subst. exact Hb.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma addat_has l f : forall a, In a (atoms f) -> In a (addat l f).
Proof.
  revert l. induction f as [x y|x y|p args|g IH|g IH1 h IH2|g IH]; intros l a Ha; simpl in *.
  - exact (addat_atom l _ a Ha).
  - exact (addat_atom l _ a Ha).
  - exact (addat_atom l _ a Ha).
  - exact (IH l a Ha).
  - apply in_app_or in Ha as [Ha|Ha]; [apply addat_mono; apply IH1; exact Ha|apply IH2; exact Ha].
  - exact (addat_atom l _ a Ha).
Qed.

Lemma peval_topf v l f : (forall a, In a (atoms f) -> In a l) ->
  peval v f = pval (fun i => v (nth i l Bot)) (topf l f).
Proof.
  induction f as [x y|x y|p args|g IH|g IH1 h IH2|g IH]; intros H; simpl in *;
    try (rewrite (findf_nth _ l Bot (H _ (or_introl eq_refl))); reflexivity).
  - rewrite IH; auto.
  - rewrite IH1, IH2; auto; intros a Ha; apply H; apply in_or_app; auto.
Qed.

Definition tautchk (f : form) : bool :=
  let l := addat [] f in allbits (length l) (topf l f) (fun _ => false).

Lemma pmax_topf l f : (forall a, In a (atoms f) -> In a l) -> pmax (topf l f) <= length l.
Proof.
  induction f as [x y|x y|p args|g IH|g IH1 h IH2|g IH]; intros H; simpl in *;
    try (pose proof (findf_lt _ l (H _ (or_introl eq_refl))); lia).
  - apply IH; auto.
  - assert (pmax (topf l g) <= length l) by (apply IH1; intros a Ha; apply H; apply in_or_app; auto).
    assert (pmax (topf l h) <= length l) by (apply IH2; intros a Ha; apply H; apply in_or_app; auto). lia.
Qed.

Theorem tautchk_prov (A : form -> Prop) f : tautchk f = true -> prov A f.
Proof.
  intros T. apply taut_prov. intros v. unfold tautchk in T. set (l := addat [] f) in *.
  assert (Hl : forall a, In a (atoms f) -> In a l) by apply addat_has.
  rewrite (peval_topf v l f Hl).
  set (w := fun i => if i <? length l then v (nth i l Bot) else false).
  rewrite (pval_ext _ _ w); [|intros i Hi; unfold w; pose proof (pmax_topf l f Hl); rewrite (proj2 (Nat.ltb_lt i (length l))) by lia; reflexivity].
  apply (allbits_ok _ _ _ T). intros i Hi. unfold w. rewrite (proj2 (Nat.ltb_ge i (length l)) Hi). reflexivity.
Qed.
