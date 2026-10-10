(* Expand.v - unfolding defined symbols. A table T lists (symbol, arity, body); expD fb T replaces every atom P a whose
   symbol has an entry of arity length a by the body with its variable i read as the i-th argument, and every other atom
   P a by fb P a. Replacement of equivalents: when Gam proves every entry's definition (Good T), Gam proves
   f <-> expD Pr T f for every formula f. buildT unfolds a list of definitions in order, each body over the entries
   before it; the result is Good when the definitions are Gam's. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax.
Import ListNotations.
Open Scope nat_scope.

Fixpoint tlook (T : list (nat * nat * form)) (p : nat) : option (nat * form) :=
  match T with [] => None | (q, k, B) :: r => if Nat.eqb p q then Some (k, B) else tlook r p end.

Definition argr (a : list nat) : nat -> nat := fun i => nth i a 0.

Fixpoint expD (fb : nat -> list nat -> form) (T : list (nat * nat * form)) (f : form) : form :=
  match f with
  | Mem x y => Mem x y
  | Eqv x y => Eqv x y
  | Pr p a => match tlook T p with
              | Some (k, B) => if Nat.eqb (List.length a) k then ren (argr a) B else fb p a
              | None => fb p a
              end
  | Neg g => Neg (expD fb T g)
  | Imp g h => Imp (expD fb T g) (expD fb T h)
  | All g => All (expD fb T g)
  end.

Fixpoint buildT (fb : nat -> list nat -> form) (T : list (nat * nat * form)) (ds : list (nat * nat * form)) :=
  match ds with [] => T | (p, k, body) :: r => buildT fb ((p, k, expD fb T body) :: T) r end.

Lemma map_argr_seq (a : list nat) : map (argr a) (seq 0 (List.length a)) = a.
Proof.
  unfold argr. induction a as [|x a IH]; [reflexivity|]. simpl. f_equal.
  rewrite <- seq_shift, map_map. exact IH.
Qed.

(* ---- propositional facts, each an instance of a checked tautology schema *)
Section P.
Variable A : form -> Prop.

Lemma iff_refl f : prov A (Qf f f).
Proof.
  pose proof (ptaut_prov A (PN (PI (PI (PV 0) (PV 0)) (PN (PI (PV 0) (PV 0))))) (lv [f]) ltac:(vm_compute; reflexivity)) as H.
  exact H.
Qed.

Lemma mp2 a b c : prov A a -> prov A b -> prov A (Imp a (Imp b c)) -> prov A c.
Proof. intros Ha Hb H. apply (p_mp _ b); [exact Hb|]. apply (p_mp _ a); assumption. Qed.

Lemma iff_trans a b c : prov A (Qf a b) -> prov A (Qf b c) -> prov A (Qf a c).
Proof.
  intros H1 H2. apply (mp2 _ _ _ H1 H2).
  (* Q a b -> Q b c -> Q a c *)
  pose proof (ptaut_prov A
    (PI (PN (PI (PI (PV 0) (PV 1)) (PN (PI (PV 1) (PV 0)))))
      (PI (PN (PI (PI (PV 1) (PV 2)) (PN (PI (PV 2) (PV 1)))))
          (PN (PI (PI (PV 0) (PV 2)) (PN (PI (PV 2) (PV 0)))))))
    (lv [a; b; c]) ltac:(vm_compute; reflexivity)) as H. exact H.
Qed.

Lemma iff_neg a b : prov A (Qf a b) -> prov A (Qf (Neg a) (Neg b)).
Proof.
  intros H. apply (p_mp _ _ _ H).
  pose proof (ptaut_prov A
    (PI (PN (PI (PI (PV 0) (PV 1)) (PN (PI (PV 1) (PV 0)))))
        (PN (PI (PI (PN (PV 0)) (PN (PV 1))) (PN (PI (PN (PV 1)) (PN (PV 0)))))))
    (lv [a; b]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma iff_imp a b c d : prov A (Qf a b) -> prov A (Qf c d) -> prov A (Qf (Imp a c) (Imp b d)).
Proof.
  intros H1 H2. apply (mp2 _ _ _ H1 H2).
  pose proof (ptaut_prov A
    (PI (PN (PI (PI (PV 0) (PV 1)) (PN (PI (PV 1) (PV 0)))))
      (PI (PN (PI (PI (PV 2) (PV 3)) (PN (PI (PV 3) (PV 2)))))
          (PN (PI (PI (PI (PV 0) (PV 2)) (PI (PV 1) (PV 3))) (PN (PI (PI (PV 1) (PV 3)) (PI (PV 0) (PV 2))))))))
    (lv [a; b; c; d]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma iff_l a b : prov A (Qf a b) -> prov A (Imp a b).
Proof.
  intros H. apply (p_mp _ _ _ H).
  pose proof (ptaut_prov A (PI (PN (PI (PI (PV 0) (PV 1)) (PN (PI (PV 1) (PV 0))))) (PI (PV 0) (PV 1)))
    (lv [a; b]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma iff_r a b : prov A (Qf a b) -> prov A (Imp b a).
Proof.
  intros H. apply (p_mp _ _ _ H).
  pose proof (ptaut_prov A (PI (PN (PI (PI (PV 0) (PV 1)) (PN (PI (PV 1) (PV 0))))) (PI (PV 1) (PV 0)))
    (lv [a; b]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma iff_intro a b : prov A (Imp a b) -> prov A (Imp b a) -> prov A (Qf a b).
Proof.
  intros H1 H2. apply (mp2 _ _ _ H1 H2).
  pose proof (ptaut_prov A (PI (PI (PV 0) (PV 1)) (PI (PI (PV 1) (PV 0)) (PN (PI (PI (PV 0) (PV 1)) (PN (PI (PV 1) (PV 0)))))))
    (lv [a; b]) ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Lemma all_imp a b : prov A (Imp a b) -> prov A (Imp (All a) (All b)).
Proof. intros H. apply (p_mp _ (All (Imp a b))); [apply p_gen; exact H|apply p_dist]. Qed.

Lemma iff_all a b : prov A (Qf a b) -> prov A (Qf (All a) (All b)).
Proof.
  intros H. apply iff_intro; apply all_imp; [apply iff_l|apply iff_r]; exact H.
Qed.
End P.

(* ---- replacement of equivalents *)
Definition Good (T : list (nat * nat * form)) : Prop :=
  forall p k B, tlook T p = Some (k, B) -> prov Gam (Qf (Pr p (seq 0 k)) B).

Theorem repl T : Good T -> forall f, prov Gam (Qf f (expD Pr T f)).
Proof.
  intros G f. induction f; simpl.
  - apply iff_refl.
  - apply iff_refl.
  - destruct (tlook T n) as [[k B]|] eqn:E; [|apply iff_refl].
    destruct (Nat.eqb (List.length l) k) eqn:L; [|apply iff_refl].
    apply Nat.eqb_eq in L. subst k.
    pose proof (prov_Gam_ren _ (G n (List.length l) B E) (argr l)) as R.
    unfold Qf, Kf in R |- *. simpl in R. rewrite map_argr_seq in R. exact R.
  - apply iff_neg. exact IHf.
  - apply iff_imp; assumption.
  - apply iff_all. exact IHf.
Qed.

Lemma defax_prov d : In d Dall -> prov Gam (defax d).
Proof.
  intros H. apply p_ax. right; right; right. exists d, (fun n => n). split; [exact H|]. symmetry. apply ren_id.
Qed.

Theorem buildT_good ds : (forall d, In d ds -> In d Dall) -> forall T, Good T -> Good (buildT Pr T ds).
Proof.
  induction ds as [|[[p k] body] r IH]; intros Hin T G; simpl; [exact G|].
  apply IH; [intros d Hd; apply Hin; right; exact Hd|].
  intros q k' B E. simpl in E. destruct (Nat.eqb q p) eqn:Q.
  - apply Nat.eqb_eq in Q. subst q. injection E as <- <-.
    apply (iff_trans _ _ body).
    + exact (defax_prov (p, k, body) (Hin _ (or_introl eq_refl))).
    + apply repl. exact G.
  - apply G. exact E.
Qed.

Lemma good_nil : Good []. Proof. intros p k B E. discriminate. Qed.
