From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.

(* Exact decimal arithmetic model for the v5 significant-digit policy.
   This module does not assert a relation to tokenization or executable bytes. *)
Fixpoint pow10 (n : nat) : Z :=
  match n with O => 1 | S k => 10 * pow10 k end.

Definition digit (d : Z) : bool := (0 <=? d) && (d <? 10).
Definition in_range (a : Z) (n : nat) : Prop := 0 <= a < pow10 n.

Fixpoint parse_digits (ds : list Z) (a : Z) (n : nat) : option Z :=
  match ds with
  | [] => Some a
  | d :: tail =>
      if digit d then
        if ((Nat.eqb n 0) && (Z.eqb d 0))%bool then parse_digits tail a n
        else if Nat.ltb n 12 then parse_digits tail (10 * a + d) (S n)
        else None
      else None
  end.

Definition parse_decimal (ds : list Z) : option Z :=
  match ds with [] => None | _ => parse_digits ds 0 0 end.

Lemma pow10_positive : forall n, 0 < pow10 n.
Proof. induction n; [change (0 < 1); lia|change (0 < 10 * pow10 n); nia]. Qed.

Lemma pow10_monotone : forall n m, (n <= m)%nat -> pow10 n <= pow10 m.
Proof.
  intros n m H. induction H.
  - lia.
  - change (pow10 n <= 10 * pow10 m). pose proof (pow10_positive m). nia.
Qed.

Lemma digit_spec : forall d, digit d = true -> 0 <= d < 10.
Proof.
  intros d H. unfold digit in H. apply Bool.andb_true_iff in H.
  destruct H as [H0 H9]. apply Z.leb_le in H0. apply Z.ltb_lt in H9. lia.
Qed.

Lemma checked_step_range : forall a n d,
  in_range a n -> 0 <= d < 10 -> in_range (10 * a + d) (S n).
Proof. unfold in_range; intros a n d Ha Hd. change (0 <= 10 * a + d < 10 * pow10 n). nia. Qed.

Theorem parse_digits_bound : forall ds a n value,
  (n <= 12)%nat -> in_range a n ->
  parse_digits ds a n = Some value -> 0 <= value < pow10 12.
Proof.
  induction ds as [|d tail IH]; intros a n value Hn Ha Hparse.
  - simpl in Hparse. inversion Hparse; subst.
    unfold in_range in Ha. pose proof (pow10_monotone n 12 Hn). lia.
  - simpl in Hparse. destruct (digit d) eqn:Hd; try discriminate.
    destruct (((Nat.eqb n 0) && (Z.eqb d 0))%bool) eqn:Hz.
    + eapply IH; eauto.
    + destruct (Nat.ltb n 12) eqn:Hlimit; try discriminate.
      apply Nat.ltb_lt in Hlimit.
      eapply (IH (10 * a + d) (S n) value); [lia| |exact Hparse].
      apply checked_step_range; [exact Ha|apply digit_spec; exact Hd].
Qed.

Theorem parse_decimal_bound : forall ds value,
  parse_decimal ds = Some value -> 0 <= value <= 999999999999.
Proof.
  intros ds value H. destruct ds as [|d tail]; try discriminate.
  unfold parse_decimal in H.
  assert (Hr : in_range 0 0) by (unfold in_range; simpl; lia).
  pose proof (parse_digits_bound (d :: tail) 0 0 value (Nat.le_0_l 12) Hr H) as B.
  cbn [pow10] in B. lia.
Qed.

Theorem leading_zeros_preserve : forall k ds,
  parse_digits (repeat 0 k ++ ds) 0 0 = parse_digits ds 0 0.
Proof. induction k; intros ds; simpl; auto. Qed.

Theorem padded_decimal_preserves : forall k d tail,
  parse_decimal (repeat 0 k ++ d :: tail) = parse_decimal (d :: tail).
Proof.
  intros k d tail. destruct k; [reflexivity|].
  unfold parse_decimal. simpl. apply leading_zeros_preserve.
Qed.

Theorem thirteenth_significant_refused : forall ds a d,
  digit d = true ->
  parse_digits (d :: ds) a 12 = None.
Proof. intros ds a d Hd. simpl. rewrite Hd. reflexivity. Qed.

Theorem checked_accumulator_fits_signed64 : forall a d,
  0 <= a <= 99999999999 -> 0 <= d < 10 ->
  0 <= 10 * a + d <= 999999999999 /\
  10 * a + d < 9223372036854775808.
Proof. intros a d Ha Hd. nia. Qed.

Example padded_one : parse_decimal (repeat 0 64 ++ [1]) = Some 1.
Proof. vm_compute. reflexivity. Qed.
Example all_zero : parse_decimal (repeat 0 256) = Some 0.
Proof. vm_compute. reflexivity. Qed.
Example max_index : parse_decimal (repeat 9 12) = Some 999999999999.
Proof. vm_compute. reflexivity. Qed.
Example thirteen_digits : parse_decimal (1 :: repeat 0 12) = None.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions parse_decimal_bound.
Print Assumptions leading_zeros_preserve.
Print Assumptions padded_decimal_preserves.
Print Assumptions thirteenth_significant_refused.
Print Assumptions checked_accumulator_fits_signed64.
