(* Prov.v - a Hilbert calculus for first-order logic with equality over an axiom set Ax (a predicate on formulas; open
   axioms stand for their universal closures): K, S, contraposition, modus ponens, generalization, instantiation,
   vacuous quantification, distribution, reflexivity and Leibniz's law for every formula. The metatheorems: renaming,
   cut (replacing axioms by derivations), and uniform substitution of formulas for predicate symbols. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn.
Import ListNotations.

Definition sid : nat -> nat := fun n => n.

Inductive prov (Ax : form -> Prop) : form -> Prop :=
| p_ax f : Ax f -> prov Ax f
| p_k a b : prov Ax (Imp a (Imp b a))
| p_s a b c : prov Ax (Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c)))
| p_c a b : prov Ax (Imp (Imp (Neg a) (Neg b)) (Imp b a))
| p_mp a b : prov Ax a -> prov Ax (Imp a b) -> prov Ax b
| p_gen a : prov Ax a -> prov Ax (All a)
| p_inst a y : prov Ax (Imp (All a) (ren (scons y sid) a))
| p_vac a : prov Ax (Imp a (All (ren S a)))
| p_dist a b : prov Ax (Imp (All (Imp a b)) (Imp (All a) (All b)))
| p_refl x : prov Ax (Eqv x x)
| p_leib a x y : prov Ax (Imp (Eqv x y) (Imp (ren (scons x sid) a) (ren (scons y sid) a))).

(* ---- cut: axioms of A replaced by derivations from B *)
Lemma prov_cut (A B : form -> Prop) : (forall f, A f -> prov B f) -> forall f, prov A f -> prov B f.
Proof.
  intros H f P. induction P.
  - apply H; assumption.
  - apply p_k.
  - apply p_s.
  - apply p_c.
  - eapply p_mp; [exact IHP1|exact IHP2].
  - apply p_gen; auto.
  - apply p_inst.
  - apply p_vac.
  - apply p_dist.
  - apply p_refl.
  - apply p_leib.
Qed.

Lemma prov_mono (A B : form -> Prop) : (forall f, A f -> B f) -> forall f, prov A f -> prov B f.
Proof. intros H. apply prov_cut. intros f Hf. apply p_ax. auto. Qed.

(* ---- renaming *)
Lemma ren_scons_up (a : form) (s : nat -> nat) y :
  ren s (ren (scons y sid) a) = ren (scons (s y) sid) (ren (up s) a).
Proof. rewrite !ren_comp. apply ren_ext. intros [|n]; reflexivity. Qed.

Lemma ren_S_up (a : form) (s : nat -> nat) : ren (up s) (ren S a) = ren S (ren s a).
Proof. rewrite !ren_comp. apply ren_ext. intros [|n]; reflexivity. Qed.

Lemma prov_ren (A : form -> Prop) : (forall f s, A f -> prov A (ren s f)) ->
  forall f, prov A f -> forall s, prov A (ren s f).
Proof.
  intros HA f P. induction P; intros s; simpl.
  - apply HA; assumption.
  - apply p_k.
  - apply p_s.
  - apply p_c.
  - eapply p_mp; [apply IHP1|apply IHP2].
  - apply p_gen. apply IHP.
  - rewrite ren_scons_up. apply p_inst.
  - rewrite ren_S_up. apply p_vac.
  - apply p_dist.
  - apply p_refl.
  - rewrite !ren_scons_up. apply p_leib.
Qed.

(* ---- uniform substitution *)
Lemma psub_scons (a : form) tau rho y :
  psub tau rho (ren (scons y sid) a) = ren (scons y sid) (psub tau (fun n => S (rho n)) a).
Proof. rewrite ren_psub. apply psub_ext. intros n. reflexivity. Qed.

Lemma psub_S (a : form) tau rho : psub tau (fun n => S (rho n)) (ren S a) = ren S (psub tau rho a).
Proof. rewrite ren_psub. reflexivity. Qed.

Theorem prov_psub (A : form -> Prop) tau : (forall rho f, A f -> prov A (psub tau rho f)) ->
  forall f, prov A f -> forall rho, prov A (psub tau rho f).
Proof.
  intros HA f P. induction P; intros rho; simpl.
  - apply HA; assumption.
  - apply p_k.
  - apply p_s.
  - apply p_c.
  - eapply p_mp; [apply IHP1|apply IHP2].
  - apply p_gen. apply IHP.
  - rewrite psub_scons. apply p_inst.
  - rewrite psub_S. apply p_vac.
  - apply p_dist.
  - apply p_refl.
  - rewrite !psub_scons. apply p_leib.
Qed.
