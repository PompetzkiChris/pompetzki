(* GrokRecordCount.v - Grok Bot, new file. Exact Z arithmetic and a syntax-level count model.
   Scope: arithmetic / list-model statements only. NOT proved: that pmp/Racket/native code
   computes these expressions (RDNUM semantics), or compiler/executable preservation. *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Definition fits64 (x : Z) : Prop := - 2 ^ 63 <= x <= 2 ^ 63 - 1.

Lemma pow2_63 : 2 ^ 63 = 9223372036854775808.
Proof. reflexivity. Qed.

Theorem rem_sub_num_fits : forall num rem,
  0 <= num <= 999999999999 -> 0 <= rem <= 2 ^ 63 - 1 ->
  fits64 (rem - num) /\ (rem - num < 0 <-> num > rem).
Proof. intros num rem Hn Hr. unfold fits64. rewrite pow2_63 in *. lia. Qed.

Theorem num_mul8_fits : forall num, 0 <= num <= 999999999999 -> fits64 (num * 8).
Proof. intros num Hn. unfold fits64. rewrite pow2_63. lia. Qed.

Theorem num_prefix_sum_fits : forall num prefix,
  0 <= num <= 999999999999 -> 0 <= prefix <= 706 -> fits64 (num + prefix).
Proof. intros num prefix Hn Hp. unfold fits64. rewrite pow2_63. lia. Qed.

Theorem num_prefix_mul24_fits : forall num prefix,
  0 <= num <= 999999999999 -> 0 <= prefix <= 706 -> fits64 ((num + prefix) * 24).
Proof. intros num prefix Hn Hp. unfold fits64. rewrite pow2_63. lia. Qed.

Theorem num_prefix_mul24_bound : forall num prefix,
  0 <= num <= 999999999999 -> 0 <= prefix <= 706 -> 0 <= (num + prefix) * 24 <= 24000000016920.
Proof. intros num prefix Hn Hp. lia. Qed.

(* Syntax model: records are nonempty byte lists; serialized byte count = length (concat rs). *)
Theorem records_le_bytes : forall (A : Type) (rs : list (list A)),
  Forall (fun r => r <> []) rs -> (length rs <= length (concat rs))%nat.
Proof.
  intros A rs F. induction F as [|r rs Hr F IH]; simpl; [lia|].
  rewrite length_app. destruct r as [|x r]; [contradiction|simpl; lia].
Qed.

Corollary records_le_rem : forall (A : Type) (rs : list (list A)) (rem : Z),
  Forall (fun r => r <> []) rs -> Z.of_nat (length (concat rs)) <= rem ->
  Z.of_nat (length rs) <= rem.
Proof.
  intros A rs rem F H. pose proof (records_le_bytes A rs F) as L. lia.
Qed.
