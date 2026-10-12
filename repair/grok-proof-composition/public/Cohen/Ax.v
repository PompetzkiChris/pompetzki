(* Ax.v - the axiom sets. Gam: the seven axioms of the kernel's table, every instance of Separation and Collection in
   the kernel's form (any formula, any symbols), and the definitions the kernel registered (Def:P, open: Q P(v1..vk) body,
   in every renaming). Gam0: the theory of the input derivations: the seven axioms, Separation, Collection, the
   definitions of lib/zfcbase.pmp (ZB_BASE) and notCH*. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks.
Import ListNotations.
Open Scope nat_scope.

(* ---- renamings that agree on the free variables *)
Lemma ren_free (f : form) : forall s t, (forall n, free n f = true -> s n = t n) -> ren s f = ren t f.
Proof.
  induction f; intros s t H; simpl in *.
  - f_equal; apply H; rewrite Nat.eqb_refl; solve [reflexivity | apply orb_true_r].
  - f_equal; apply H; rewrite Nat.eqb_refl; solve [reflexivity | apply orb_true_r].
  - f_equal. apply map_ext_in. intros x Hx. apply H. apply existsb_exists. exists x. split; auto. apply Nat.eqb_refl.
  - f_equal. auto.
  - f_equal; [apply IHf1|apply IHf2]; intros n Hn; apply H; rewrite Hn; auto using orb_true_r.
  - f_equal. apply IHf. intros [|n] Hn; simpl; auto.
Qed.

Fixpoint closedk (k : nat) (f : form) : bool :=
  match f with
  | Mem x y | Eqv x y => (x <? k) && (y <? k)
  | Pr _ a => forallb (fun x => x <? k) a
  | Neg a => closedk k a
  | Imp a b => closedk k a && closedk k b
  | All a => closedk (S k) a
  end.

Lemma closedk_free f : forall k n, closedk k f = true -> free n f = true -> n < k.
Proof.
  induction f; intros k m Hc Hf; simpl in *.
  - apply andb_true_iff in Hc as [H1 H2]. apply Nat.ltb_lt in H1, H2.
    apply orb_true_iff in Hf as [E|E]; apply Nat.eqb_eq in E; subst; auto.
  - apply andb_true_iff in Hc as [H1 H2]. apply Nat.ltb_lt in H1, H2.
    apply orb_true_iff in Hf as [E|E]; apply Nat.eqb_eq in E; subst; auto.
  - apply existsb_exists in Hf as [x [Hx E]]. apply Nat.eqb_eq in E. subst.
    rewrite forallb_forall in Hc. apply Nat.ltb_lt. auto.
  - eauto.
  - apply andb_true_iff in Hc as [H1 H2]. apply orb_true_iff in Hf as [E|E]; eauto.
  - specialize (IHf (S k) (S m) Hc Hf). lia.
Qed.

Lemma ren_closed f s : closedk 0 f = true -> ren s f = f.
Proof.
  intros Hc. rewrite <- (ren_id f) at 2. apply ren_free. intros n Hn.
  pose proof (closedk_free f 0 n Hc Hn). lia.
Qed.

Lemma syms_ren f : forall s, syms (ren s f) = syms f.
Proof. induction f; intros s; simpl; auto; rewrite IHf1, IHf2; reflexivity. Qed.

(* ---- Separation and Collection under renaming and substitution *)
Lemma SepF_ren g s : ren s (SepF g) = SepF (ren (up (up s)) g).
Proof.
  unfold SepF, Qf, Kf, Xf. simpl.
  assert (E : ren (up (up (up s))) (ren skip1 g) = ren skip1 (ren (up (up s)) g))
    by (rewrite !ren_comp; apply ren_ext; intros [|[|n]]; reflexivity).
  rewrite E. reflexivity.
Qed.

Lemma CollF_ren g s : ren s (CollF g) = CollF (ren (up (up (up s))) g).
Proof.
  unfold CollF, Kf, Xf. simpl.
  assert (E : ren (up (up (up (up s)))) (ren ins2 g) = ren ins2 (ren (up (up (up s))) g))
    by (rewrite !ren_comp; apply ren_ext; intros [|[|[|n]]]; reflexivity).
  rewrite E. reflexivity.
Qed.

Lemma SepF_psub g tau rho : psub tau rho (SepF g) = SepF (psub tau (fun j => S (S (rho j))) g).
Proof. unfold SepF, Qf, Kf, Xf. simpl. rewrite ren_psub. reflexivity. Qed.

Lemma CollF_psub g tau rho : psub tau rho (CollF g) = CollF (psub tau (fun j => S (S (S (rho j)))) g).
Proof. unfold CollF, Kf, Xf. simpl. rewrite ren_psub. reflexivity. Qed.

(* ---- the definitions *)
Definition pdef (d : string * list string * string) : option (nat * nat * form) :=
  match d with (n, ps, b) => match pstmt symtab ps b with Some body => Some (sid_of n, List.length ps, body) | None => None end end.
Fixpoint somes {A : Type} (l : list (option A)) : list A :=
  match l with [] => [] | Some x :: r => x :: somes r | None :: r => somes r end.
Definition Dall : list (nat * nat * form) := somes (map pdef defs).
Definition defax (d : nat * nat * form) : form := match d with (p, k, body) => Qf (Pr p (seq 0 k)) body end.

Definition ZFC7 (f : form) : Prop := exists i, i < 7 /\ f = axf i.
Definition SepAx (f : form) : Prop := exists g, f = SepF g.
Definition CollAx (f : form) : Prop := exists g, f = CollF g.
Definition DefAx (D : list (nat * nat * form)) (f : form) : Prop := exists d s, In d D /\ f = ren s (defax d).

Definition Gam (f : form) : Prop := ZFC7 f \/ SepAx f \/ CollAx f \/ DefAx Dall f.

(* ---- facts checked by computation *)
Definition all_defs_parse : bool := Nat.eqb (List.length Dall) (List.length defs).
Definition axioms_closed : bool := forallb (fun i => closedk 0 (axf i)) (seq 0 7).
Definition axioms_pure : bool := forallb (fun i => match syms (axf i) with [] => true | _ => false end) (seq 0 7).
Lemma all_defs_parse_ok : all_defs_parse = true. Proof. vm_compute. reflexivity. Qed.
Lemma axioms_closed_ok : axioms_closed = true. Proof. vm_compute. reflexivity. Qed.
Lemma axioms_pure_ok : axioms_pure = true. Proof. vm_compute. reflexivity. Qed.

Lemma axf_closed i : i < 7 -> closedk 0 (axf i) = true.
Proof.
  intros H. pose proof axioms_closed_ok as C. unfold axioms_closed in C. rewrite forallb_forall in C.
  apply C. apply in_seq. lia.
Qed.
Lemma axf_pure i : i < 7 -> syms (axf i) = [].
Proof.
  intros H. pose proof axioms_pure_ok as C. unfold axioms_pure in C. rewrite forallb_forall in C.
  specialize (C i ltac:(apply in_seq; lia)). destruct (syms (axf i)); [reflexivity|discriminate].
Qed.

(* Gam is closed under renaming *)
Lemma Gam_ren f s : Gam f -> Gam (ren s f).
Proof.
  intros [[i [Hi ->]]|[[g ->]|[[g ->]|[d [t [Hd ->]]]]]].
  - left. exists i. split; auto. apply ren_closed. apply axf_closed. exact Hi.
  - right; left. exists (ren (up (up s)) g). apply SepF_ren.
  - right; right; left. exists (ren (up (up (up s))) g). apply CollF_ren.
  - right; right; right. exists d, (fun n => s (t n)). split; auto. apply ren_comp.
Qed.

Lemma prov_Gam_ren f : prov Gam f -> forall s, prov Gam (ren s f).
Proof. apply prov_ren. intros g s Hg. apply p_ax. apply Gam_ren. exact Hg. Qed.
