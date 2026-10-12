(* GrokNumericGaps.v - Grok Bot, new file. Closes two gaps of numeric-v5 using the
   unchanged definitions of DecimalSignificantV4 (digit, parse_digits, parse_decimal).
   Statements are about the Gallina model over list Z only; no text/byte/tokenizer claim. *)
From Stdlib Require Import ZArith List Lia Bool.
From NumericV5 Require Import DecimalSignificantV4.
Import ListNotations.
Open Scope Z_scope.

(* ---- Gap 1: all-zero inputs *)
Lemma parse_digits_zeros_count0 : forall (n : nat) (a : Z),
  parse_digits (repeat 0 n) a 0 = Some a.
Proof. induction n as [|n IH]; intros a; [reflexivity|exact (IH a)]. Qed.

Theorem parse_decimal_all_zeros : forall n : nat,
  (1 <= n)%nat -> parse_decimal (repeat 0 n) = Some 0.
Proof.
  intros [|n] H; [lia|]. unfold parse_decimal. simpl repeat. cbv beta iota.
  exact (parse_digits_zeros_count0 (S n) 0).
Qed.

Theorem parse_decimal_empty : parse_decimal [] = None.
Proof. reflexivity. Qed.

(* ---- Gap 2: more than twelve significant digits.
   Significant digits of ds: ds = repeat 0 k ++ d :: tail with d <> 0; they are d :: tail. *)
Definition significant_split (ds : list Z) (k : nat) (d : Z) (tail : list Z) : Prop :=
  ds = repeat 0 k ++ d :: tail /\ d <> 0.

Lemma parse_digits_overflow : forall ds a (n : nat),
  (1 <= n)%nat -> (n <= 12)%nat -> (12 < n + length ds)%nat -> parse_digits ds a n = None.
Proof.
  induction ds as [|d t IH]; intros a n H1 H12 Hlen; simpl in *; [lia|].
  destruct (digit d); [|reflexivity].
  replace (Nat.eqb n 0) with false by (symmetry; apply Nat.eqb_neq; lia). simpl.
  destruct (Nat.ltb n 12) eqn:L.
  - apply Nat.ltb_lt in L. apply IH; lia.
  - reflexivity.
Qed.

Lemma parse_digits_first_significant : forall d tail,
  d <> 0 -> parse_digits (d :: tail) 0 0 =
            if digit d then parse_digits tail d 1 else None.
Proof.
  intros d tail Hd. simpl. destruct (digit d); [|reflexivity].
  replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd). reflexivity.
Qed.

(* No digit-validity hypothesis is needed: an invalid element also yields None. *)
Theorem more_than_twelve_significant_refused : forall ds k d tail,
  significant_split ds k d tail -> (12 < length (d :: tail))%nat -> parse_decimal ds = None.
Proof.
  intros ds k d tail [-> Hd] Hlen.
  assert (NE : repeat 0 k ++ d :: tail <> []) by (destruct k; discriminate).
  unfold parse_decimal. destruct (repeat 0 k ++ d :: tail) as [|x r] eqn:E; [contradiction|].
  rewrite <- E, leading_zeros_preserve, parse_digits_first_significant by exact Hd.
  destruct (digit d); [|reflexivity]. simpl in Hlen. apply parse_digits_overflow; lia.
Qed.

(* ---- Characterization for lists of valid digits *)
Lemma zeros_or_split : forall ds,
  (exists k, ds = repeat 0 k) \/ (exists k d tail, significant_split ds k d tail).
Proof.
  induction ds as [|x t IH]; [left; exists 0%nat; reflexivity|].
  destruct (Z.eq_dec x 0) as [->|Hx].
  - destruct IH as [[k ->]|[k [d [tail [-> Hd]]]]].
    + left; exists (S k); reflexivity.
    + right; exists (S k), d, tail; split; [reflexivity|exact Hd].
  - right; exists 0%nat, x, t; split; [reflexivity|exact Hx].
Qed.

Lemma parse_digits_fits : forall ds a (n : nat),
  Forall (fun d => digit d = true) ds -> (1 <= n)%nat -> (n + length ds <= 12)%nat ->
  exists v, parse_digits ds a n = Some v.
Proof.
  induction ds as [|d t IH]; intros a n F H1 Hlen; simpl in *; [eexists; reflexivity|].
  inversion F as [|? ? Hd Ft]; subst. rewrite Hd.
  replace (Nat.eqb n 0) with false by (symmetry; apply Nat.eqb_neq; lia). simpl.
  replace (Nat.ltb n 12) with true by (symmetry; apply Nat.ltb_lt; lia).
  apply IH; [exact Ft|lia|lia].
Qed.

Theorem parse_decimal_none_iff : forall ds,
  Forall (fun d => digit d = true) ds ->
  (parse_decimal ds = None <->
   ds = [] \/ exists k d tail, significant_split ds k d tail /\ (12 < length (d :: tail))%nat).
Proof.
  intros ds F. split.
  - intros N. destruct (zeros_or_split ds) as [[k ->]|[k [d [tail S]]]].
    + destruct k as [|k]; [left; reflexivity|].
      rewrite parse_decimal_all_zeros in N by lia. discriminate.
    + right. exists k, d, tail. split; [exact S|].
      destruct (Nat.lt_ge_cases 12 (length (d :: tail))) as [L|L]; [exact L|exfalso].
      destruct S as [E Hd]. subst ds.
      apply Forall_app in F as [_ F]. inversion F as [|? ? Hdig Ft]; subst.
      unfold parse_decimal in N. destruct (repeat 0 k ++ d :: tail) as [|x r] eqn:E;
        [destruct k; discriminate|].
      rewrite <- E, leading_zeros_preserve, parse_digits_first_significant, Hdig in N by exact Hd.
      simpl in L. destruct (parse_digits_fits tail d 1 Ft (le_n 1) ltac:(lia)) as [v V].
      rewrite V in N. discriminate.
  - intros [->|[k [d [tail [S L]]]]]; [reflexivity|].
    exact (more_than_twelve_significant_refused ds k d tail S L).
Qed.

(* Invalid elements: parse_decimal refuses any list containing a non-digit. *)
Theorem invalid_digit_refused : forall ds,
  ~ Forall (fun d => digit d = true) ds -> parse_decimal ds = None.
Proof.
  intros ds NF. destruct ds as [|x r]; [reflexivity|]. unfold parse_decimal.
  assert (G : forall l a n, ~ Forall (fun d => digit d = true) l -> parse_digits l a n = None).
  { induction l as [|y l IH]; intros a n H; [exfalso; apply H; constructor|]. simpl.
    destruct (digit y) eqn:Dy; [|reflexivity].
    assert (Hl : ~ Forall (fun d => digit d = true) l) by (intro C; apply H; constructor; assumption).
    destruct ((Nat.eqb n 0 && (y =? 0))%bool); [apply IH; exact Hl|].
    destruct (Nat.ltb n 12); [apply IH; exact Hl|reflexivity]. }
  apply G; exact NF.
Qed.
