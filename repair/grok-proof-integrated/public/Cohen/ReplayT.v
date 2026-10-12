(* ReplayT.v - deciding a tautology by splitting on one variable at a time and simplifying the constants away (Shannon
   expansion): sound because substituting a truth value for a variable is evaluating it. Exhaustive in the worst case,
   and a proof step's tautology usually collapses after a few splits. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Kal Replay.
Import ListNotations.

Inductive bf : Type := BT | BF | BV (n : nat) | BN (a : bf) | BI (a b : bf).

Fixpoint bev (w : nat -> bool) (b : bf) : bool :=
  match b with BT => true | BF => false | BV n => w n | BN a => negb (bev w a) | BI a c => implb (bev w a) (bev w c) end.

Definition mkN (a : bf) : bf := match a with BT => BF | BF => BT | BN x => x | _ => BN a end.
Definition mkI (a c : bf) : bf :=
  match a, c with
  | BF, _ => BT
  | _, BT => BT
  | BT, _ => c
  | _, BF => mkN a
  | _, _ => BI a c
  end.

Lemma bev_mkN w a : bev w (mkN a) = negb (bev w a).
Proof. destruct a; simpl; auto. rewrite negb_involutive. reflexivity. Qed.

Lemma bev_mkI w a c : bev w (mkI a c) = implb (bev w a) (bev w c).
Proof.
  destruct a, c; simpl; try reflexivity; try (rewrite ?bev_mkN; simpl; destruct (bev w _); reflexivity);
    try (destruct (bev w _); reflexivity); try (destruct (w _); reflexivity);
    try (destruct (bev w _), (bev w _); reflexivity).
Qed.

Fixpoint subst (v : nat) (c : bool) (b : bf) : bf :=
  match b with
  | BV n => if Nat.eqb n v then (if c then BT else BF) else BV n
  | BN a => mkN (subst v c a)
  | BI a d => mkI (subst v c a) (subst v c d)
  | _ => b
  end.

Lemma bev_subst w v c b : bev w (subst v c b) = bev (updb w v c) b.
Proof.
  induction b; simpl; try reflexivity.
  - unfold updb. destruct (Nat.eqb n v); [destruct c; reflexivity|reflexivity].
  - rewrite bev_mkN, IHb. reflexivity.
  - rewrite bev_mkI, IHb1, IHb2. reflexivity.
Qed.

Fixpoint somevar (b : bf) : option nat :=
  match b with
  | BV n => Some n
  | BN a => somevar a
  | BI a d => match somevar a with Some n => Some n | None => somevar d end
  | _ => None
  end.

Fixpoint taut_bf (k : nat) (b : bf) : bool :=
  match b with
  | BT => true
  | BF => false
  | _ =>
    match k, somevar b with
    | S k', Some v => taut_bf k' (subst v true b) && taut_bf k' (subst v false b)
    | _, _ => false
    end
  end.

Lemma updb_same w v : forall i, updb w v (w v) i = w i.
Proof. intros i. unfold updb. destruct (Nat.eqb i v) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity|reflexivity]. Qed.

Lemma bev_ext w w' b : (forall i, w i = w' i) -> bev w b = bev w' b.
Proof. intros H. induction b; simpl; auto; congruence. Qed.

Lemma taut_bf_S k b : taut_bf (S k) b =
  match b with
  | BT => true
  | BF => false
  | _ => match somevar b with Some v => taut_bf k (subst v true b) && taut_bf k (subst v false b) | None => false end
  end.
Proof. destruct b; reflexivity. Qed.

Theorem taut_bf_ok k : forall b, taut_bf k b = true -> forall w, bev w b = true.
Proof.
  induction k as [|k IH]; intros b H w.
  - destruct b; simpl in H; try discriminate. reflexivity.
  - assert (G : forall v, taut_bf k (subst v true b) && taut_bf k (subst v false b) = true -> bev w b = true).
    { intros v H2. apply andb_true_iff in H2 as [H1 H2].
      rewrite <- (bev_ext (updb w v (w v)) w b (updb_same w v)), <- bev_subst.
      destruct (w v); [exact (IH _ H1 w)|exact (IH _ H2 w)]. }
    rewrite taut_bf_S in H. destruct b; try reflexivity; try discriminate;
      destruct (somevar _) as [v|] eqn:S; try discriminate; exact (G v H).
Qed.

Fixpoint tobf (p : pform) : bf :=
  match p with PV i => BV i | PN q => mkN (tobf q) | PI q r => mkI (tobf q) (tobf r) end.

Lemma bev_tobf w p : bev w (tobf p) = pval w p.
Proof. induction p; simpl; [reflexivity|rewrite bev_mkN, IHp; reflexivity|rewrite bev_mkI, IHp1, IHp2; reflexivity]. Qed.

Definition tautchk2 (f : form) : bool := let l := addat [] f in taut_bf (length l) (tobf (topf l f)).

Theorem tautchk2_prov (A : form -> Prop) f : tautchk2 f = true -> prov A f.
Proof.
  intros T. apply taut_prov. intros v. unfold tautchk2 in T.
  rewrite (peval_topf v (addat [] f) f (addat_has [] f)). rewrite <- bev_tobf.
  exact (taut_bf_ok _ _ T _).
Qed.
