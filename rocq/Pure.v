(* Pure.v - the input theory Gam0 and the purification pi. Gam0: the seven axioms, every instance of Separation and
   Collection (any formula, any symbols), the 23 definitions of lib/zfcbase.pmp (ZB_BASE, the first 23 the kernel
   registered: Sub2 .. Usec3, in every renaming) and notCH*. pi replaces each ZB_BASE symbol by its definition unfolded
   down to the pure language and every other predicate symbol by the closed pure formula Top = A x (x = x): the value of
   an input formula is the value of its purification. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Expand.
Import ListNotations.
Open Scope nat_scope.

Lemma somes_in {X : Type} (l : list (option X)) x : In x (somes l) <-> In (Some x) l.
Proof.
  induction l as [|[y|] r IH]; simpl; [tauto| |].
  - split; [intros [<-|H]; [left; reflexivity|right; apply IH; exact H]|].
    intros [E|H]; [injection E as <-; left; reflexivity|right; apply IH; exact H].
  - rewrite IH. split; [intros H; right; exact H|intros [E|H]; [discriminate|exact H]].
Qed.

Lemma somes_sub (P : string * list string * string -> Prop) (l : list (string * list string * string)) d :
  (forall e, In e l -> In e defs) -> In d (somes (map pdef l)) -> In d Dall.
Proof.
  intros Hl H. unfold Dall. apply somes_in in H. apply somes_in.
  apply in_map_iff in H as [e [E He]]. apply in_map_iff. exists e. split; [exact E|apply Hl; exact He].
Qed.

(* ---- the input theory *)
Definition Top : form := All (Eqv 0 0).
Definition D0 : list (nat * nat * form) := somes (map pdef (firstn 23 defs)).
Definition notch_text : string :=
  "X w X x X y K K K K Om1 w A u I E u x Sub2 u w A u I E u y Sub2 u w N Le2 x w N Le2 y x".
Definition notch : form := match pstmt symtab [] notch_text with Some f => f | None => Top end.

Definition Gam0 (f : form) : Prop := ZFC7 f \/ SepAx f \/ CollAx f \/ DefAx D0 f \/ f = notch.

Definition D0_names : list string := map (fun d => match d with (n, _, _) => n end) (firstn 23 defs).
Lemma D0_names_ok : D0_names = ["Sub2"; "Sng2"; "Upr3"; "Opr3"; "App3"; "Fnc1"; "Inj1"; "Tot2"; "Rng2"; "Le2"; "Tr1";
  "Ord1"; "Emp1"; "Suc2"; "Ind1"; "Om1"; "Cnt1"; "Card1"; "InfO1"; "Sec3"; "CSec2"; "Cov3"; "Usec3"]%string.
Proof. vm_compute. reflexivity. Qed.
Lemma D0_parse : List.length D0 = 23. Proof. vm_compute. reflexivity. Qed.
Lemma notch_parse : pstmt symtab [] notch_text <> None. Proof. vm_compute. discriminate. Qed.

Lemma D0_in d : In d D0 -> In d Dall.
Proof.
  apply (somes_sub (fun _ => True)). intros e He. rewrite <- (firstn_skipn 23 defs). apply in_or_app. left. exact He.
Qed.

(* ---- expD: renaming, purity, pure formulas fixed *)
Section E.
Variable fb : nat -> list nat -> form.
Variable T : list (nat * nat * form).
Hypothesis Hc : forall p k B, tlook T p = Some (k, B) -> closedk k B = true.
Hypothesis Hfb : forall p a s, fb p (map s a) = ren s (fb p a).

Lemma expD_ren f : forall s, expD fb T (ren s f) = ren s (expD fb T f).
Proof.
  induction f; intros s; simpl; try reflexivity.
  - destruct (tlook T n) as [[k B]|] eqn:E; [|apply Hfb]. rewrite length_map.
    destruct (Nat.eqb (List.length l) k) eqn:L; [|apply Hfb].
    apply Nat.eqb_eq in L. rewrite ren_comp. apply ren_free. intros i Fi.
    pose proof (closedk_free B k i (Hc n k B E) Fi) as Lt. unfold argr.
    rewrite (nth_indep (map s l) 0 (s 0)) by (rewrite length_map; lia). apply map_nth.
  - f_equal. apply IHf.
  - f_equal; [apply IHf1|apply IHf2].
  - f_equal. apply IHf.
Qed.
End E.

Lemma expD_pure fb T (Hs : forall p k B, tlook T p = Some (k, B) -> syms B = []) (Hb : forall p a, syms (fb p a) = []) :
  forall f, syms (expD fb T f) = [].
Proof.
  induction f; simpl; try reflexivity.
  - destruct (tlook T n) as [[k B]|] eqn:E; [|apply Hb].
    destruct (Nat.eqb (List.length l) k); [rewrite syms_ren; apply (Hs n k B E)|apply Hb].
  - exact IHf.
  - rewrite IHf1, IHf2. reflexivity.
  - exact IHf.
Qed.

Lemma expD_fix fb T f : syms f = [] -> expD fb T f = f.
Proof.
  induction f; simpl; intros H; try reflexivity; try discriminate.
  - rewrite IHf; auto.
  - apply app_eq_nil in H as [H1 H2]. rewrite IHf1, IHf2; auto.
  - rewrite IHf; auto.
Qed.

Lemma expD_Qf fb T a b : expD fb T (Qf a b) = Qf (expD fb T a) (expD fb T b).
Proof. reflexivity. Qed.

(* ---- pi *)
Definition fb0 : nat -> list nat -> form := fun _ _ => Top.
(* the table as a literal: its facts are the checks below, so the kernel never evaluates the unfolding *)
Definition T0 : list (nat * nat * form) := Eval vm_compute in buildT fb0 [] D0.
Definition pi : form -> form := expD fb0 T0.

Lemma tlook_in T p k B : tlook T p = Some (k, B) -> In (p, k, B) T.
Proof.
  induction T as [|[[q j] C] r IH]; simpl; [discriminate|].
  destruct (Nat.eqb p q) eqn:E; [intros H; injection H as <- <-; apply Nat.eqb_eq in E; subst; left; reflexivity|].
  intros H. right. apply IH. exact H.
Qed.

Definition T0_check : bool :=
  forallb (fun e => match e with (_, k, B) => closedk k B && match syms B with [] => true | _ => false end end) T0.
Lemma T0_check_ok : T0_check = true. Proof. vm_compute. reflexivity. Qed.
Lemma T0_check_x : forallb (fun e => match e with (_, k, B) => closedk k B && match syms B with [] => true | _ => false end end) T0
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma T0_entry p k B : tlook T0 p = Some (k, B) -> closedk k B = true /\ syms B = [].
Proof.
  intros E. apply tlook_in in E. pose proof T0_check_x as C. rewrite forallb_forall in C.
  specialize (C _ E). apply andb_true_iff in C as [C1 C2]. split; [exact C1|]. destruct (syms B); [reflexivity|discriminate].
Qed.

Lemma pi_ren f s : pi (ren s f) = ren s (pi f).
Proof. apply expD_ren; [intros p k B E; exact (proj1 (T0_entry p k B E))|reflexivity]. Qed.

Lemma pi_pure f : syms (pi f) = [].
Proof. apply expD_pure; [intros p k B E; exact (proj2 (T0_entry p k B E))|reflexivity]. Qed.

Lemma pi_fix f : syms f = [] -> pi f = f.
Proof. apply expD_fix. Qed.

Lemma pi_Sep g : pi (SepF g) = SepF (pi g).
Proof.
  unfold SepF. change (pi (All (Xf (All (Qf (Mem 0 1) (Kf (Mem 0 2) (ren skip1 g)))))))
    with (All (Xf (All (Qf (Mem 0 1) (Kf (Mem 0 2) (pi (ren skip1 g))))))). rewrite pi_ren. reflexivity.
Qed.

Lemma pi_Coll g : pi (CollF g) = CollF (pi g).
Proof.
  unfold CollF. change (pi (All (Imp (All (Imp (Mem 0 1) (Xf g))) (Xf (All (Imp (Mem 0 2) (Xf (Kf (Mem 0 2) (ren ins2 g)))))))))
    with (All (Imp (All (Imp (Mem 0 1) (Xf (pi g)))) (Xf (All (Imp (Mem 0 2) (Xf (Kf (Mem 0 2) (pi (ren ins2 g))))))))).
  rewrite pi_ren. reflexivity.
Qed.

(* each ZB_BASE definition purifies to X <-> X *)
Definition D0_check : bool :=
  forallb (fun d => match d with (p, k, body) => form_eqb (pi (Pr p (seq 0 k))) (pi body) end) D0.
Lemma D0_check_ok : D0_check = true. Proof. vm_compute. reflexivity. Qed.
Lemma D0_check_x : forallb (fun d => match d with (p, k, body) => form_eqb (pi (Pr p (seq 0 k))) (pi body) end) D0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_defax d s : In d D0 -> exists X, pi (ren s (defax d)) = Qf X X /\ syms X = [].
Proof.
  intros H. destruct d as [[p k] body]. pose proof D0_check_x as C. rewrite forallb_forall in C.
  specialize (C _ H). apply form_eqb_true in C.
  exists (ren s (pi body)). split; [|rewrite syms_ren; apply pi_pure].
  rewrite pi_ren. unfold defax, pi. rewrite expD_Qf. unfold pi in C. rewrite C. reflexivity.
Qed.
