(* Syn.v - first-order formulas of the kernel's language (lib/logic.pmp, ZFC mode) with de Bruijn variables:
   E x y (membership), = x y, predicate symbols applied to variables, N, I, A. Terms are variables only.
   Renaming, and simultaneous substitution of formulas for predicate symbols (with parameters). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
Import ListNotations.

Inductive form : Type :=
| Mem : nat -> nat -> form
| Eqv : nat -> nat -> form
| Pr : nat -> list nat -> form
| Neg : form -> form
| Imp : form -> form -> form
| All : form -> form.

Definition up (s : nat -> nat) : nat -> nat :=
  fun n => match n with 0 => 0 | S m => S (s m) end.

Fixpoint ren (s : nat -> nat) (f : form) : form :=
  match f with
  | Mem x y => Mem (s x) (s y)
  | Eqv x y => Eqv (s x) (s y)
  | Pr p a => Pr p (map s a)
  | Neg a => Neg (ren s a)
  | Imp a b => Imp (ren s a) (ren s b)
  | All a => All (ren (up s) a)
  end.

(* the abbreviations of the kernel (ZF_EXPAND): K a b = N I a N b, D a b = I N a b, Q a b = K (I a b) (I b a),
   X a = N A N a *)
Definition Kf (a b : form) : form := Neg (Imp a (Neg b)).
Definition Df (a b : form) : form := Imp (Neg a) b.
Definition Qf (a b : form) : form := Kf (Imp a b) (Imp b a).
Definition Xf (a : form) : form := Neg (All (Neg a)).

Lemma up_ext (s t : nat -> nat) : (forall n, s n = t n) -> forall n, up s n = up t n.
Proof. intros H [|n]; simpl; auto. Qed.

Lemma ren_ext (f : form) : forall s t, (forall n, s n = t n) -> ren s f = ren t f.
Proof.
  induction f; intros s t H; simpl; try (rewrite !H; reflexivity).
  - f_equal. apply map_ext. auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal. apply IHf. apply up_ext. auto.
Qed.

Lemma up_comp (s t : nat -> nat) n : up s (up t n) = up (fun m => s (t m)) n.
Proof. destruct n; reflexivity. Qed.

Lemma ren_comp (f : form) : forall s t, ren s (ren t f) = ren (fun n => s (t n)) f.
Proof.
  induction f; intros s t; simpl; try reflexivity.
  - f_equal. rewrite map_map. reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal. rewrite IHf. apply ren_ext. intros n. apply up_comp.
Qed.

Lemma up_id n : up (fun m => m) n = n.
Proof. destruct n; reflexivity. Qed.

Lemma ren_id (f : form) : ren (fun n => n) f = f.
Proof.
  induction f; simpl; try reflexivity.
  - f_equal. apply map_id.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal. rewrite (ren_ext f (up (fun m => m)) (fun m => m)); auto. apply up_id.
Qed.

Lemma ren_id' (f : form) (s : nat -> nat) : (forall n, s n = n) -> ren s f = f.
Proof. intros H. rewrite (ren_ext f s (fun n => n)); auto. apply ren_id. Qed.

(* ---- predicate substitution. tau p = Some th: every atom Pr p a becomes th with its variable i < length a read as the
   i-th argument and its variable length a + j read as the parameter j, which rho places. Under a binder the
   parameters move one place out. *)
Definition inst_args (a : list nat) (rho : nat -> nat) : nat -> nat :=
  fun i => if i <? length a then nth i a 0 else rho (i - length a).

Fixpoint psub (tau : nat -> option form) (rho : nat -> nat) (f : form) : form :=
  match f with
  | Mem x y => Mem x y
  | Eqv x y => Eqv x y
  | Pr p a => match tau p with Some th => ren (inst_args a rho) th | None => Pr p a end
  | Neg a => Neg (psub tau rho a)
  | Imp a b => Imp (psub tau rho a) (psub tau rho b)
  | All a => All (psub tau (fun n => S (rho n)) a)
  end.

Lemma inst_args_ren (a : list nat) (rho s : nat -> nat) i :
  s (inst_args a rho i) = inst_args (map s a) (fun n => s (rho n)) i.
Proof.
  unfold inst_args. rewrite length_map. destruct (i <? length a) eqn:E.
  - apply Nat.ltb_lt in E. rewrite (nth_indep (map s a) 0 (s 0)) by (rewrite length_map; exact E).
    rewrite map_nth. reflexivity.
  - reflexivity.
Qed.

Lemma psub_ext (f : form) : forall tau rho rho', (forall n, rho n = rho' n) -> psub tau rho f = psub tau rho' f.
Proof.
  induction f; intros tau rho rho' H; simpl; try reflexivity.
  - destruct (tau n); [|reflexivity]. apply ren_ext. intros i. unfold inst_args. destruct (i <? length l); auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal. apply IHf. intros; simpl; f_equal; auto.
Qed.

(* renaming after substitution = substitution (parameters renamed too) after renaming *)
Lemma ren_psub (f : form) : forall tau rho s,
  ren s (psub tau rho f) = psub tau (fun n => s (rho n)) (ren s f).
Proof.
  induction f; intros tau rho s; simpl; try reflexivity.
  - destruct (tau n) as [th|]; [|reflexivity].
    rewrite ren_comp. apply ren_ext. intros i. apply inst_args_ren.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal. rewrite IHf. apply psub_ext. intros n. reflexivity.
Qed.

(* ---- symbols and free variables *)
Fixpoint syms (f : form) : list nat :=
  match f with
  | Mem _ _ | Eqv _ _ => []
  | Pr p _ => [p]
  | Neg a | All a => syms a
  | Imp a b => syms a ++ syms b
  end.

Lemma psub_none (f : form) : forall tau rho, (forall p, In p (syms f) -> tau p = None) -> psub tau rho f = f.
Proof.
  induction f; intros tau rho H; simpl in *; try reflexivity.
  - rewrite H by auto. reflexivity.
  - f_equal; auto.
  - f_equal; apply IHf1 || apply IHf2; intros p Hp; apply H; apply in_or_app; auto.
  - f_equal; auto.
Qed.

Fixpoint free (n : nat) (f : form) : bool :=
  match f with
  | Mem x y | Eqv x y => (x =? n) || (y =? n)
  | Pr _ a => existsb (fun x => x =? n) a
  | Neg a => free n a
  | Imp a b => free n a || free n b
  | All a => free (S n) a
  end.

(* scons y s: 0 goes to y, n+1 to s n *)
Definition scons (y : nat) (s : nat -> nat) : nat -> nat := fun n => match n with 0 => y | S m => s m end.

Lemma form_eq_dec (f g : form) : {f = g} + {f <> g}.
Proof. decide equality; try apply Nat.eq_dec. apply list_eq_dec, Nat.eq_dec. Qed.

(* a boolean equality that computes (form_eq_dec is opaque) *)
Fixpoint nlist_eqb (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Nat.eqb x y && nlist_eqb a' b'
  | _, _ => false
  end.

Fixpoint form_eqb (f g : form) : bool :=
  match f, g with
  | Mem x y, Mem x' y' => Nat.eqb x x' && Nat.eqb y y'
  | Eqv x y, Eqv x' y' => Nat.eqb x x' && Nat.eqb y y'
  | Pr p a, Pr p' a' => Nat.eqb p p' && nlist_eqb a a'
  | Neg a, Neg a' => form_eqb a a'
  | Imp a b, Imp a' b' => form_eqb a a' && form_eqb b b'
  | All a, All a' => form_eqb a a'
  | _, _ => false
  end.

Lemma list_eqb_nat_true (a b : list nat) : nlist_eqb a b = true -> a = b.
Proof.
  revert b. induction a as [|x a IH]; intros [|y b]; simpl; try discriminate; auto.
  intros H. apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H1. f_equal; auto.
Qed.

Lemma form_eqb_true (f : form) : forall g, form_eqb f g = true -> f = g.
Proof.
  induction f; intros [] H; simpl in H; try discriminate;
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end;
    repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end; subst; auto.
  all: f_equal; auto; apply list_eqb_nat_true; assumption.
Qed.
