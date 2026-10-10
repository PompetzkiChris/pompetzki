(* Use.v - instantiating a kernel theorem about placeholders: uniform substitution into another axiom set, for a class
   of parameter maps closed under the shift under a binder; the pairing of an object-level substitution (formulas for
   placeholders) with the value-level one (their values for the placeholders' value symbols); Gam is closed under it. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax.
Import ListNotations.
Open Scope nat_scope.

Theorem prov_psub_to (A B : form -> Prop) tau (P : (nat -> nat) -> Prop) :
  (forall rho, P rho -> P (fun j => S (rho j))) ->
  (forall rho f, P rho -> A f -> prov B (psub tau rho f)) ->
  forall f, prov A f -> forall rho, P rho -> prov B (psub tau rho f).
Proof.
  intros HP HA f D. induction D; intros rho Pr0; simpl.
  - apply HA; assumption.
  - apply p_k.
  - apply p_s.
  - apply p_c.
  - eapply p_mp; [apply IHD1|apply IHD2]; assumption.
  - apply p_gen. apply IHD. apply HP. exact Pr0.
  - rewrite psub_scons. apply p_inst.
  - rewrite psub_S. apply p_vac.
  - apply p_dist.
  - apply p_refl.
  - rewrite !psub_scons. apply p_leib.
Qed.

(* ---- the placeholders: phs (object symbols), phv (their value symbols) *)
Definition phs : list nat := map fst phpairs.
Definition phv : list nat := map snd phpairs.
Fixpoint nlookr (l : list (nat * nat)) (v : nat) : option nat :=
  match l with [] => None | (q, w) :: r => if Nat.eqb v w then Some q else nlookr r v end.
Definition vz_inv (q : nat) : nat := match nlookr phpairs q with Some p => p | None => q end.

(* facts about the finite table, each checked by computation *)
Definition inj_check : bool := forallb (fun e => match e with (p, v) => match nlookr phpairs v with Some p' => Nat.eqb p p' | None => false end end) phpairs.
Definition small_check : bool := forallb (fun p => p <? 1000) phs && forallb (fun v => v <? 1000) phv.
Definition base_check : bool := forallb (fun q => negb (existsb (Nat.eqb q) (phs ++ phv))) [sVE; sVQ; sVN; sVI; sRg].
Definition defs_avoid_check : bool :=
  forallb (fun d => forallb (fun p => negb (existsb (Nat.eqb p) (phs ++ phv))) (syms (defax d))) Dall.
Lemma inj_ok : inj_check = true. Proof. vm_compute. reflexivity. Qed.
Lemma small_ok : small_check = true. Proof. vm_compute. reflexivity. Qed.
Lemma base_ok : base_check = true. Proof. vm_compute. reflexivity. Qed.
Lemma defs_avoid_ok : defs_avoid_check = true. Proof. vm_compute. reflexivity. Qed.

Lemma nlook_in p v : nlook phpairs p = Some v -> In (p, v) phpairs.
Proof.
  generalize phpairs. induction l as [|[q w] r IH]; simpl; [discriminate|].
  destruct (Nat.eqb p q) eqn:E; [intros H; injection H as <-; apply Nat.eqb_eq in E; subst; left; reflexivity|].
  intros H. right. apply IH. exact H.
Qed.

Lemma vz_inv_vz p v : nlook phpairs p = Some v -> vz_inv v = p.
Proof.
  intros H. apply nlook_in in H. pose proof inj_ok as I. unfold inj_check in I. rewrite forallb_forall in I.
  specialize (I _ H).
  change (match nlookr phpairs v with Some p' => Nat.eqb p p' | None => false end = true) in I.
  unfold vz_inv. destruct (nlookr phpairs v); [apply Nat.eqb_eq in I; auto|discriminate].
Qed.

Lemma nlookr_in v p : nlookr phpairs v = Some p -> In (p, v) phpairs.
Proof.
  generalize phpairs. induction l as [|[q w] r IH]; simpl; [discriminate|].
  destruct (Nat.eqb v w) eqn:E; [intros H; injection H as <-; apply Nat.eqb_eq in E; subst; left; reflexivity|].
  intros H. right. apply IH. exact H.
Qed.

(* an object-level substitution of formulas for placeholders, from a list of pairs; its value-level partner *)
Fixpoint alook (l : list (nat * form)) (p : nat) : option form :=
  match l with [] => None | (q, f) :: r => if Nat.eqb p q then Some f else alook r p end.
Definition otau (l : list (nat * form)) : nat -> option form :=
  fun p => match nlook phpairs p with Some _ => alook l p | None => None end.
Definition vtau (l : list (nat * form)) : nat -> option form :=
  fun q => match nlookr phpairs q with Some p => option_map V (alook l p) | None => None end.

Lemma vtau_sym l p : vtau l (vz p) = option_map V (otau l p).
Proof.
  unfold vtau, otau, vz. destruct (nlook phpairs p) as [v|] eqn:E.
  - pose proof (vz_inv_vz p v E) as Hv. unfold vz_inv in Hv.
    destruct (nlookr phpairs v) as [p'|] eqn:F; [subst; reflexivity|].
    apply nlook_in in E. pose proof inj_ok as I. unfold inj_check in I. rewrite forallb_forall in I.
    specialize (I _ E).
    change (match nlookr phpairs v with Some p' => Nat.eqb p p' | None => false end = true) in I.
    rewrite F in I. discriminate.
  - destruct (nlookr phpairs (1000 + p)) as [p'|] eqn:F; [|reflexivity].
    apply nlookr_in in F. pose proof small_ok as S. unfold small_check in S. apply andb_true_iff in S as [_ S].
    rewrite forallb_forall in S. specialize (S (1000 + p) (in_map snd _ _ F)). apply Nat.ltb_lt in S. lia.
Qed.

Lemma vtau_none_notv l q : ~ In q phv -> vtau l q = None.
Proof.
  intros H. unfold vtau. destruct (nlookr phpairs q) as [p|] eqn:F; [|reflexivity].
  exfalso. apply H. apply nlookr_in in F. apply (in_map snd _ _ F).
Qed.

Lemma vtau_base l : vtau l sVE = None /\ vtau l sVQ = None /\ vtau l sVN = None /\ vtau l sVI = None /\ vtau l sRg = None.
Proof. unfold vtau. vm_compute. repeat split; reflexivity. Qed.

(* the same facts, stated expanded: using them needs no unfolding (the kernel would evaluate the definitions otherwise) *)
Lemma defs_avoid_x : forallb (fun d => forallb (fun p => negb (existsb (Nat.eqb p) (phs ++ phv))) (syms (defax d))) Dall = true.
Proof. vm_compute. reflexivity. Qed.

Lemma defs_avoid_in d p : In d Dall -> In p (syms (defax d)) -> ~ In p phv.
Proof.
  intros Hd Hp Hv. pose proof (proj1 (forallb_forall _ Dall) defs_avoid_x d Hd) as A.
  pose proof (proj1 (forallb_forall _ _) A p Hp) as B. apply negb_true_iff in B.
  rewrite existsb_app in B. apply orb_false_iff in B as [_ B].
  assert (existsb (Nat.eqb p) phv = true) by (apply existsb_exists; exists p; split; auto; apply Nat.eqb_refl).
  congruence.
Qed.
