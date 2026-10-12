(* Sub.v - free variables, and the SUB invariant under renaming and under placeholder substitution. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Val Inv Checks Ax.
Import ListNotations.
Open Scope nat_scope.

(* a bound on the free variables *)
Fixpoint fvb (f : form) : nat :=
  match f with
  | Mem x y | Eqv x y => S (Nat.max x y)
  | Pr _ a => S (fold_right Nat.max 0 a)
  | Neg a => fvb a
  | Imp a b => Nat.max (fvb a) (fvb b)
  | All a => pred (fvb a)
  end.

Lemma fold_max_ge (a : list nat) x : In x a -> x <= fold_right Nat.max 0 a.
Proof. induction a; simpl; [tauto|]. intros [<-|H]; [lia|]. specialize (IHa H). lia. Qed.

Lemma free_fvb f : forall i, free i f = true -> i < fvb f.
Proof.
  induction f; intros i H; simpl in *.
  - apply orb_true_iff in H as [E|E]; apply Nat.eqb_eq in E; subst; lia.
  - apply orb_true_iff in H as [E|E]; apply Nat.eqb_eq in E; subst; lia.
  - apply existsb_exists in H as [x [Hx E]]. apply Nat.eqb_eq in E. subst i. pose proof (fold_max_ge l x Hx). lia.
  - auto.
  - apply orb_true_iff in H as [E|E]; [specialize (IHf1 i E)|specialize (IHf2 i E)]; lia.
  - specialize (IHf (S i) H). lia.
Qed.

Lemma free_ren f : forall s i, free i (ren s f) = true -> exists j, free j f = true /\ s j = i.
Proof.
  induction f; intros s i H; simpl in *.
  - apply orb_true_iff in H as [E|E]; apply Nat.eqb_eq in E; [exists n|exists n0]; rewrite ?Nat.eqb_refl, ?orb_true_r; auto.
  - apply orb_true_iff in H as [E|E]; apply Nat.eqb_eq in E; [exists n|exists n0]; rewrite ?Nat.eqb_refl, ?orb_true_r; auto.
  - apply existsb_exists in H as [x [Hx E]]. apply in_map_iff in Hx as [y [<- Hy]]. apply Nat.eqb_eq in E.
    exists y. split; auto. apply existsb_exists. exists y. split; auto. apply Nat.eqb_refl.
  - auto.
  - apply orb_true_iff in H as [E|E]; [destruct (IHf1 s i E) as [j [J1 J2]]|destruct (IHf2 s i E) as [j [J1 J2]]];
      exists j; rewrite J1; auto using orb_true_r.
  - destruct (IHf (up s) (S i) H) as [[|j] [J1 J2]]; simpl in J2; [discriminate|].
    injection J2 as J2. exists j. auto.
Qed.

(* ---- SUB under renaming: the hole must not be merged with another free variable *)
Lemma sv_ren f s h a : (forall i, free i f = true -> i <> h -> s i <> s h) ->
  ren s (ren (sv h a) f) = ren (sv (s h) (s a)) (ren s f).
Proof.
  intros Hi. rewrite !ren_comp. apply ren_free. intros n Hn. unfold sv.
  destruct (n =? h) eqn:E.
  - apply Nat.eqb_eq in E. subst. rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq in E. destruct (s n =? s h) eqn:F; [|reflexivity].
    apply Nat.eqb_eq in F. exfalso. exact (Hi n Hn E F).
Qed.

Lemma SUB_ren vz f h a b s : (forall i, free i f = true -> i <> h -> s i <> s h) ->
  ren (up s) (SUBf vz f h a b) = SUBf vz (ren s f) (s h) (s a) (s b).
Proof.
  intros Hi. unfold SUBf, Kf. simpl.
  assert (E1 : ren (up (up (up (up s)))) (ren w1 (val vz (ren (sv h a) f))) = ren w1 (val vz (ren (sv (s h) (s a)) (ren s f)))).
  { rewrite <- sv_ren by exact Hi. rewrite (val_ren vz (ren (sv h a) f) s), !ren_comp. apply ren_ext. intros [|[|n]]; reflexivity. }
  assert (E0 : ren (up (up (up (up s)))) (ren w0 (val vz (ren (sv h b) f))) = ren w0 (val vz (ren (sv (s h) (s b)) (ren s f)))).
  { rewrite <- sv_ren by exact Hi. rewrite (val_ren vz (ren (sv h b) f) s), !ren_comp. apply ren_ext. intros [|[|n]]; reflexivity. }
  rewrite E1, E0. reflexivity.
Qed.

(* ---- SUB under placeholder substitution: the parameters must avoid the hole *)
Section PS.
Variable vz : nat -> nat.
Variable tau tau' : nat -> option form.
Hypothesis Hsym : forall p, tau' (vz p) = option_map (val vz) (tau p).
Hypothesis Hbase : tau' sVE = None /\ tau' sVQ = None /\ tau' sVN = None /\ tau' sVI = None /\ tau' sRg = None.

Lemma psub_sv f h a rho : (forall j, rho j <> h) -> psub tau rho (ren (sv h a) f) = ren (sv h a) (psub tau rho f).
Proof.
  intros Hr. rewrite ren_psub. apply psub_ext. intros j. unfold sv.
  destruct (rho j =? h) eqn:E; [apply Nat.eqb_eq in E; exfalso; exact (Hr j E)|reflexivity].
Qed.

Lemma SUB_psub f h a b rho : (forall j, rho j <> h) ->
  psub tau' (fun j => 1 + rho j) (SUBf vz f h a b) = SUBf vz (psub tau rho f) h a b.
Proof.
  intros Hr. destruct Hbase as (HE & HQ & HN & HI & HR).
  assert (A1 : psub tau' (fun j => S (S (S (S (rho j))))) (ren w1 (val vz (ren (sv h a) f)))
               = ren w1 (val vz (ren (sv h a) (psub tau rho f)))).
  { rewrite <- (psub_sv f h a rho Hr). rewrite (val_psub vz tau tau' Hsym Hbase). rewrite ren_psub. reflexivity. }
  assert (A0 : psub tau' (fun j => S (S (S (S (rho j))))) (ren w0 (val vz (ren (sv h b) f)))
               = ren w0 (val vz (ren (sv h b) (psub tau rho f)))).
  { rewrite <- (psub_sv f h b rho Hr). rewrite (val_psub vz tau tau' Hsym Hbase). rewrite ren_psub. reflexivity. }
  unfold SUBf, Kf. simpl. rewrite HQ, A1, A0. reflexivity.
Qed.
End PS.
