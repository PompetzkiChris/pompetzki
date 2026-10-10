(* L2RLogic.v - lane L2R, 2026-10-09. A natural-deduction layer over prov Gam (Prov.v, Ax.v): a context is a list of
   formulas, D G f is prov Gam (cj G -> f) with cj G their conjunction. Rules: hypothesis, modus ponens, the
   deduction theorem, generalization under a shifted context, instantiation, existential introduction and
   elimination, Leibniz. Propositional steps go through Kal.taut_prov (Kalmar), decided by case analysis on the atoms.
   Then the facts this lane takes from the verified replay of Theorem 29 (RpFinal.entry_is_prov: entries of the
   registry REGF, each derivable in Gam), and the unfolding of the registered definitions Emp1, Suc2, App3, Fnc1. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Replay2 Expand Pure RpInitOk RpFinal.
Import ListNotations.
Open Scope nat_scope.

Notation Pv := (prov Gam).

Arguments Kf : simpl never.
Arguments Df : simpl never.
Arguments Qf : simpl never.
Arguments Xf : simpl never.

Lemma ren_Kf s a b : ren s (Kf a b) = Kf (ren s a) (ren s b). Proof. reflexivity. Qed.
Lemma ren_Df s a b : ren s (Df a b) = Df (ren s a) (ren s b). Proof. reflexivity. Qed.
Lemma ren_Qf s a b : ren s (Qf a b) = Qf (ren s a) (ren s b). Proof. reflexivity. Qed.
Lemma ren_Xf s a : ren s (Xf a) = Xf (ren (up s) a). Proof. reflexivity. Qed.
Lemma ren_Top s : ren s Top = Top. Proof. reflexivity. Qed.

(* every propositional tautology over the atoms in sight: case analysis on the truth values of the atoms *)
Ltac pt :=
  apply taut_prov; intros v; unfold Kf, Df, Qf, Xf; simpl;
  repeat (match goal with
          | |- context [v ?x] => destruct (v x)
          | |- context [peval v ?x] => destruct (peval v x)
          end; simpl);
  reflexivity.

Lemma pmp a b : Pv a -> Pv (Imp a b) -> Pv b.
Proof. intros H1 H2. exact (p_mp _ _ _ H1 H2). Qed.
Lemma pmp2 a b c : Pv a -> Pv b -> Pv (Imp a (Imp b c)) -> Pv c.
Proof. intros H1 H2 H3. exact (pmp _ _ H2 (pmp _ _ H1 H3)). Qed.
Lemma pmp3 a b c d : Pv a -> Pv b -> Pv c -> Pv (Imp a (Imp b (Imp c d))) -> Pv d.
Proof. intros H1 H2 H3 H4. exact (pmp _ _ H3 (pmp2 _ _ _ H1 H2 H4)). Qed.

Lemma pv_inst f y : Pv (All f) -> Pv (ren (scons y sid) f).
Proof. intros H. exact (pmp _ _ H (p_inst _ f y)). Qed.

(* ---- contexts *)
Fixpoint cj (G : list form) : form := match G with [] => Top | h :: r => Kf h (cj r) end.
Definition D (G : list form) (f : form) : Prop := Pv (Imp (cj G) f).
Arguments D : simpl never.

Lemma Top_pv : Pv Top. Proof. apply p_gen. apply p_refl. Qed.

Lemma cj_ren s G : ren s (cj G) = cj (map (ren s) G).
Proof. induction G as [|h r IH]; [reflexivity|]. cbn [cj map]. rewrite ren_Kf, IH. reflexivity. Qed.

Lemma D_thm G f : Pv f -> D G f.
Proof. intros H. unfold D. apply (pmp f); [exact H|]. pt. Qed.

Lemma D_mp G a b : D G (Imp a b) -> D G a -> D G b.
Proof. unfold D. intros H1 H2. apply (pmp2 _ _ _ H1 H2). pt. Qed.

Lemma D_hyp G f : In f G -> D G f.
Proof.
  induction G as [|h r IH]; simpl; [intros []|]. intros [E|H].
  - subst. unfold D. simpl. pt.
  - pose proof (IH H) as I. unfold D in *. simpl. apply (pmp _ _ I). pt.
Qed.

Lemma D_intro G a b : D (a :: G) b -> D G (Imp a b).
Proof. unfold D. simpl. intros H. apply (pmp _ _ H). pt. Qed.
Lemma D_elim G a b : D G (Imp a b) -> D (a :: G) b.
Proof. unfold D. simpl. intros H. apply (pmp _ _ H). pt. Qed.

Lemma D_t1 G a b : Pv (Imp a b) -> D G a -> D G b.
Proof. intros H1 H2. exact (D_mp _ _ _ (D_thm _ _ H1) H2). Qed.
Lemma D_t2 G a b c : Pv (Imp a (Imp b c)) -> D G a -> D G b -> D G c.
Proof. intros H H1 H2. exact (D_mp _ _ _ (D_mp _ _ _ (D_thm _ _ H) H1) H2). Qed.
Lemma D_t3 G a b c d : Pv (Imp a (Imp b (Imp c d))) -> D G a -> D G b -> D G c -> D G d.
Proof. intros H H1 H2 H3. exact (D_mp _ _ _ (D_t2 _ _ _ _ H H1 H2) H3). Qed.
Lemma D_t4 G a b c d e : Pv (Imp a (Imp b (Imp c (Imp d e)))) -> D G a -> D G b -> D G c -> D G d -> D G e.
Proof. intros H H1 H2 H3 H4. exact (D_mp _ _ _ (D_t3 _ _ _ _ _ H H1 H2 H3) H4). Qed.

Lemma D_cj G G' : (forall f, In f G -> In f G') -> D G' (cj G).
Proof.
  induction G as [|h r IH]; intros I; simpl.
  - apply D_thm. exact Top_pv.
  - apply (D_t2 _ h (cj r)); [pt|apply D_hyp; apply I; left; reflexivity|].
    apply IH. intros f Hf. apply I. right. exact Hf.
Qed.

Lemma D_weak G G' f : (forall g, In g G -> In g G') -> D G f -> D G' f.
Proof. intros I H. exact (D_mp _ _ _ (D_thm _ _ H) (D_cj _ _ I)). Qed.

Lemma D_cut G a b : D G a -> D (a :: G) b -> D G b.
Proof. intros H1 H2. exact (D_mp _ _ _ (D_intro _ _ _ H2) H1). Qed.

Lemma D_ren G f s : D G f -> D (map (ren s) G) (ren s f).
Proof. unfold D. intros H. rewrite <- cj_ren. exact (ren_adm _ _ s H). Qed.

(* ---- quantifiers *)
Lemma D_all G f : D (map (ren S) G) f -> D G (All f).
Proof.
  unfold D. rewrite <- cj_ren. intros H.
  pose proof (p_mp _ _ _ (p_gen _ _ H) (p_dist Gam (ren S (cj G)) f)) as H2.
  exact (syl _ _ _ _ (p_vac Gam (cj G)) H2).
Qed.

Lemma D_inst G f y : D G (All f) -> D G (ren (scons y sid) f).
Proof. intros H. exact (D_t1 _ _ _ (p_inst _ f y) H). Qed.

Lemma D_exI G f y : D G (ren (scons y sid) f) -> D G (Xf f).
Proof. intros H. exact (D_t1 _ _ _ (rule_exi _ f y) H). Qed.

Lemma ex_out f g : Pv (Imp (All (Imp f (ren S g))) (Imp (Xf f) g)).
Proof.
  assert (H1 : Pv (Imp (All (Imp f (ren S g))) (All (Imp (Neg (ren S g)) (Neg f))))).
  { apply all_imp. pt. }
  pose proof (p_dist Gam (Neg (ren S g)) (Neg f)) as H2.
  pose proof (p_vac Gam (Neg g)) as H3. simpl in H3.
  apply (pmp3 _ _ _ _ H1 H2 H3). pt.
Qed.

Lemma D_exE G f g : D G (Xf f) -> D (f :: map (ren S) G) (ren S g) -> D G g.
Proof.
  intros H1 H2.
  assert (H3 : D (map (ren S) G) (Imp f (ren S g))) by (apply D_intro; exact H2).
  pose proof (D_all _ _ H3) as H4.
  exact (D_t2 _ _ _ _ (ex_out f g) H4 H1).
Qed.

Lemma D_leib G a x y : D G (Eqv x y) -> D G (ren (scons x sid) a) -> D G (ren (scons y sid) a).
Proof. intros H1 H2. exact (D_t2 _ _ _ _ (p_leib _ a x y) H1 H2). Qed.

Lemma D_refl G x : D G (Eqv x x). Proof. apply D_thm. apply p_refl. Qed.

Lemma D_sym G x y : D G (Eqv x y) -> D G (Eqv y x).
Proof.
  intros H. pose proof (D_leib G (Eqv 0 (S x)) x y H) as L. simpl in L.
  exact (L (D_refl G x)).
Qed.

Lemma D_trans G x y z : D G (Eqv x y) -> D G (Eqv y z) -> D G (Eqv x z).
Proof.
  intros H1 H2. pose proof (D_leib G (Eqv (S x) 0) y z H2) as L. simpl in L. exact (L H1).
Qed.

(* ---- propositional shapes in context *)
Lemma D_and G a b : D G a -> D G b -> D G (Kf a b).
Proof. intros H1 H2. apply (D_t2 _ a b); [pt|exact H1|exact H2]. Qed.
Lemma D_andl G a b : D G (Kf a b) -> D G a.
Proof. intros H. apply (D_t1 _ (Kf a b)); [pt|exact H]. Qed.
Lemma D_andr G a b : D G (Kf a b) -> D G b.
Proof. intros H. apply (D_t1 _ (Kf a b)); [pt|exact H]. Qed.
Lemma D_iffl G a b : D G (Qf a b) -> D G a -> D G b.
Proof. intros H1 H2. apply (D_t2 _ (Qf a b) a); [pt|exact H1|exact H2]. Qed.
Lemma D_iffr G a b : D G (Qf a b) -> D G b -> D G a.
Proof. intros H1 H2. apply (D_t2 _ (Qf a b) b); [pt|exact H1|exact H2]. Qed.
Lemma D_iffi G a b : D (a :: G) b -> D (b :: G) a -> D G (Qf a b).
Proof. intros H1 H2. apply (D_t2 _ (Imp a b) (Imp b a)); [pt|exact (D_intro _ _ _ H1)|exact (D_intro _ _ _ H2)]. Qed.
Lemma D_orl G a b : D G a -> D G (Df a b).
Proof. intros H. apply (D_t1 _ a); [pt|exact H]. Qed.
Lemma D_orr G a b : D G b -> D G (Df a b).
Proof. intros H. apply (D_t1 _ b); [pt|exact H]. Qed.
Lemma D_orE G a b c : D G (Df a b) -> D (a :: G) c -> D (b :: G) c -> D G c.
Proof.
  intros H H1 H2. apply (D_t3 _ (Df a b) (Imp a c) (Imp b c)); [pt|exact H|exact (D_intro _ _ _ H1)|exact (D_intro _ _ _ H2)].
Qed.
Lemma D_absurd G a c : D G a -> D G (Neg a) -> D G c.
Proof. intros H1 H2. apply (D_t2 _ a (Neg a)); [pt|exact H1|exact H2]. Qed.
Lemma D_negI G a : D (a :: G) (Neg a) -> D G (Neg a).
Proof. intros H. apply (D_t1 _ (Imp a (Neg a))); [pt|exact (D_intro _ _ _ H)]. Qed.
Lemma D_nnE G a : D G (Neg (Neg a)) -> D G a.
Proof. intros H. apply (D_t1 _ (Neg (Neg a))); [pt|exact H]. Qed.
Lemma D_byc G a : D (Neg a :: G) a -> D G a.
Proof. intros H. apply (D_t1 _ (Imp (Neg a) a)); [pt|exact (D_intro _ _ _ H)]. Qed.
Lemma D_em G a c : D (a :: G) c -> D (Neg a :: G) c -> D G c.
Proof.
  intros H1 H2. apply (D_t2 _ (Imp a c) (Imp (Neg a) c)); [pt|exact (D_intro _ _ _ H1)|exact (D_intro _ _ _ H2)].
Qed.

(* an existential whose body is a conjunction, eliminated into two hypotheses *)
Lemma D_exE2 G a b g : D G (Xf (Kf a b)) -> D (a :: b :: map (ren S) G) (ren S g) -> D G g.
Proof.
  intros H1 H2. apply (D_exE _ _ _ H1). apply (D_cut _ a); [apply (D_andl _ a b); apply D_hyp; left; reflexivity|].
  apply (D_cut _ b); [apply (D_andr _ a b); apply D_hyp; right; left; reflexivity|].
  apply (D_weak (a :: b :: map (ren S) G)); [|exact H2].
  intros h Hh; simpl in Hh |- *; tauto.
Qed.

(* ---- the facts taken from the verified replay *)
Definition Emp (x : nat) : form := Pr 17 [x].
Definition Suc (s y : nat) : form := Pr 18 [s; y].
Definition Opr (p a b : nat) : form := Pr 8 [p; a; b].
Definition App (f x y : nat) : form := Pr 9 [f; x; y].
Definition Fnc (f : nat) : form := Pr 10 [f].
Definition NatP (x : nat) : form := Pr 72 [x].

Ltac inst_all H ys :=
  match ys with
  | [] => idtac
  | ?y :: ?r => apply (pv_inst _ y) in H; simpl in H; inst_all H r
  end.

Lemma F_NoSelf x : Pv (Neg (Mem x x)).
Proof.
  assert (H : Pv (All (Neg (Mem 0 0)))) by (apply (entry_is_prov 731); vm_compute; reflexivity).
  inst_all H [x]. exact H.
Qed.

Lemma F_NoTwo a b : Pv (Neg (Kf (Mem a b) (Mem b a))).
Proof.
  assert (H : Pv (All (All (Neg (Kf (Mem 1 0) (Mem 0 1))))))
    by (apply (entry_is_prov 732); vm_compute; reflexivity).
  inst_all H [a; b]. exact H.
Qed.

Lemma F_SucUq a b c : Pv (Imp (Kf (Suc a c) (Suc b c)) (Eqv a b)).
Proof.
  assert (H : Pv (All (All (All (Imp (Kf (Pr 18 [2; 0]) (Pr 18 [1; 0])) (Eqv 2 1))))))
    by (apply (entry_is_prov 733); vm_compute; reflexivity).
  inst_all H [a; b; c]. exact H.
Qed.

Lemma F_SucInj a b c : Pv (Imp (Kf (Suc a b) (Suc a c)) (Eqv b c)).
Proof.
  assert (H : Pv (All (All (All (Imp (Kf (Pr 18 [2; 1]) (Pr 18 [2; 0])) (Eqv 1 0))))))
    by (apply (entry_is_prov 734); vm_compute; reflexivity).
  inst_all H [a; b; c]. exact H.
Qed.

Lemma F_EmpUq a b : Pv (Imp (Kf (Emp a) (Emp b)) (Eqv a b)).
Proof.
  assert (H : Pv (All (All (Imp (Kf (Pr 17 [1]) (Pr 17 [0])) (Eqv 1 0)))))
    by (apply (entry_is_prov 739); vm_compute; reflexivity).
  inst_all H [a; b]. exact H.
Qed.

Lemma F_Kur1 a b c d e : Pv (Imp (Kf (Opr a b c) (Opr a d e)) (Eqv b d)).
Proof.
  assert (H : Pv (All (All (All (All (All (Imp (Kf (Pr 8 [4; 3; 2]) (Pr 8 [4; 1; 0])) (Eqv 3 1))))))))
    by (apply (entry_is_prov 720); vm_compute; reflexivity).
  inst_all H [a; b; c; d; e]. exact H.
Qed.

Lemma F_Kur2 a b c d e : Pv (Imp (Kf (Opr a b c) (Opr a d e)) (Eqv c e)).
Proof.
  assert (H : Pv (All (All (All (All (All (Imp (Kf (Pr 8 [4; 3; 2]) (Pr 8 [4; 1; 0])) (Eqv 2 0))))))))
    by (apply (entry_is_prov 721); vm_compute; reflexivity).
  inst_all H [a; b; c; d; e]. exact H.
Qed.

Lemma F_OprEx a b : Pv (Xf (Opr 0 (S a) (S b))).
Proof.
  assert (H : Pv (All (All (Xf (Pr 8 [0; 2; 1]))))) by (apply (entry_is_prov 712); vm_compute; reflexivity).
  inst_all H [a; b]. exact H.
Qed.

Lemma F_MemApp f a b d : Pv (Imp (Kf (Mem d f) (Opr d a b)) (App f a b)).
Proof.
  assert (H : Pv (All (All (All (All (Imp (Kf (Mem 0 3) (Pr 8 [0; 2; 1])) (Pr 9 [3; 2; 1])))))))
    by (apply (entry_is_prov 737); vm_compute; reflexivity).
  inst_all H [f; a; b; d]. exact H.
Qed.

Lemma F_FncApp f a b c : Pv (Imp (Fnc f) (Imp (Kf (App f a b) (App f a c)) (Eqv b c))).
Proof.
  assert (H : Pv (All (All (All (All (Imp (Pr 10 [3]) (Imp (Kf (Pr 9 [3; 2; 1]) (Pr 9 [3; 2; 0])) (Eqv 1 0))))))))
    by (apply (entry_is_prov 722); vm_compute; reflexivity).
  inst_all H [f; a; b; c]. exact H.
Qed.

Lemma F_SucEx y : Pv (Xf (Suc 0 (S y))).
Proof.
  assert (H : Pv (Xf (Pr 18 [0; 1]))) by (apply (entry_is_prov 974); vm_compute; reflexivity).
  exact (ren_adm _ _ (fun _ => y) H).
Qed.

Lemma F_AddEx r p : Pv (Xf (All (Qf (Mem 0 1) (Df (Mem 0 (S (S r))) (Eqv 0 (S (S p))))))).
Proof.
  assert (H : Pv (Xf (All (Qf (Mem 0 1) (Df (Mem 0 2) (Eqv 0 3))))))
    by (apply (entry_is_prov 1062); vm_compute; reflexivity).
  exact (ren_adm _ _ (fun n => match n with 0 => r | _ => p end) H).
Qed.

(* ---- the registered definitions *)
Definition dlook (p : nat) : option (nat * form) :=
  match find (fun d => match d with (q, _, _) => Nat.eqb q p end) Dall with Some (_, k, B) => Some (k, B) | None => None end.

Lemma dlook_in p k B : dlook p = Some (k, B) -> In (p, k, B) Dall.
Proof.
  unfold dlook. destruct (find _ Dall) as [[[q k'] B']|] eqn:E; [|discriminate].
  intros H. injection H as <- <-. pose proof (find_some _ _ E) as [I Q]. apply Nat.eqb_eq in Q. subst. exact I.
Qed.

Lemma def_pv p k B s : dlook p = Some (k, B) -> Pv (Qf (Pr p (map s (seq 0 k))) (ren s B)).
Proof. intros E. pose proof (ren_adm _ _ s (defax_prov _ (dlook_in _ _ _ E))) as H. exact H. Qed.

Lemma U_Emp x : Pv (Qf (Emp x) (All (Neg (Mem 0 (S x))))).
Proof. exact (def_pv 17 1 _ (fun _ => x) ltac:(vm_compute; reflexivity)). Qed.

Lemma U_Suc s y : Pv (Qf (Suc s y) (All (Qf (Mem 0 (S s)) (Df (Mem 0 (S y)) (Eqv 0 (S y)))))).
Proof. exact (def_pv 18 2 _ (fun n => match n with 0 => s | _ => y end) ltac:(vm_compute; reflexivity)). Qed.

Lemma U_App f x y : Pv (Qf (App f x y) (Xf (Kf (Mem 0 (S f)) (Opr 0 (S x) (S y))))).
Proof.
  exact (def_pv 9 3 _ (fun n => match n with 0 => f | 1 => x | _ => y end) ltac:(vm_compute; reflexivity)).
Qed.

Lemma U_Fnc f : Pv (Qf (Fnc f) (All (All (All (Imp (Kf (App (S (S (S f))) 2 1) (App (S (S (S f))) 2 0)) (Eqv 1 0)))))).
Proof. exact (def_pv 10 1 _ (fun _ => f) ltac:(vm_compute; reflexivity)). Qed.

Lemma D_nil f : D [] f -> Pv f.
Proof. intros H. exact (pmp _ _ Top_pv H). Qed.

(* renaming pushed through the abbreviations, then computed *)
Ltac rs := repeat progress (rewrite ?ren_Kf, ?ren_Df, ?ren_Qf, ?ren_Xf, ?ren_Top; cbn).
Ltac rsin H := repeat progress (rewrite ?ren_Kf, ?ren_Df, ?ren_Qf, ?ren_Xf, ?ren_Top in H; cbn in H).
Ltac hyp := apply D_hyp; repeat (first [left; reflexivity | right]); fail.

(* the empty set, from Infinity (entry 4 of the axiom table) *)
Lemma F_EmpEx : Pv (Xf (Emp 0)).
Proof.
  apply D_nil.
  assert (H : Pv (axf 4)) by (apply p_ax; left; exists 4; split; [lia|reflexivity]).
  set (Ib := All (Imp (Mem 0 1) (Xf (Kf (All (Qf (Mem 0 1) (Df (Mem 0 2) (Eqv 0 2)))) (Mem 0 2))))).
  assert (E : axf 4 = Xf (Kf (Xf (Kf (All (Neg (Mem 0 1))) (Mem 0 1))) Ib)) by (vm_compute; reflexivity).
  rewrite E in H.
  apply (D_exE2 [] _ _ _ (D_thm _ _ H)). rs.
  apply (D_exE2 _ (All (Neg (Mem 0 1))) (Mem 0 1)); [hyp|]. rs.
  apply (D_exI _ _ 0). rs.
  apply (D_iffr _ _ _ (D_thm _ _ (U_Emp 0))). hyp.
Qed.

(* a fact in the current goal's context *)
Ltac have name f := match goal with |- D ?G _ => assert (name : D G f) end.

(* a propositional consequence of facts in the same context *)
Ltac dt1 H := match type of H with D _ ?a => apply (D_t1 _ a); [pt|exact H] end.
Ltac dt2 H1 H2 := match type of H1 with D _ ?a => match type of H2 with D _ ?b =>
  apply (D_t2 _ a b); [pt|exact H1|exact H2] end end.
Ltac dt3 H1 H2 H3 := match type of H1 with D _ ?a => match type of H2 with D _ ?b => match type of H3 with D _ ?c =>
  apply (D_t3 _ a b c); [pt|exact H1|exact H2|exact H3] end end end.
Ltac dt4 H1 H2 H3 H4 := match type of H1 with D _ ?a => match type of H2 with D _ ?b => match type of H3 with D _ ?c =>
  match type of H4 with D _ ?d => apply (D_t4 _ a b c d); [pt|exact H1|exact H2|exact H3|exact H4] end end end end.

Lemma D_cut2 G a b g : D G a -> D G b -> D (a :: b :: G) g -> D G g.
Proof.
  intros H1 H2 H. apply (D_cut _ _ _ H2). apply (D_cut (b :: G) a); [|exact H].
  apply (D_weak G); [intros h Hh; right; exact Hh|exact H1].
Qed.
Lemma D_cut3 G a b c g : D G a -> D G b -> D G c -> D (a :: b :: c :: G) g -> D G g.
Proof.
  intros H1 H2 H3 H. apply (D_cut2 _ _ _ _ H2 H3). apply (D_cut (b :: c :: G) a); [|exact H].
  apply (D_weak G); [intros h Hh; right; right; exact Hh|exact H1].
Qed.
