(* GrokSigned64.v - Grok Bot, new file. Two's-complement 64-bit wrap model over Z.
   Arithmetic-model theorems only: NOT a proof that pmp/Racket/native code or the compiler
   implements signed64 or these operations. *)
From Stdlib Require Import ZArith Lia.
From GrokRC Require Import GrokRecordCount.
Open Scope Z_scope.

Definition signed64 (z : Z) : Z :=
  let u := z mod 2 ^ 64 in if u <? 2 ^ 63 then u else u - 2 ^ 64.

Lemma pow2_64 : 2 ^ 64 = 18446744073709551616.
Proof. reflexivity. Qed.

Theorem signed64_id : forall z, fits64 z -> signed64 z = z.
Proof.
  intros z H. unfold fits64, signed64 in *. rewrite pow2_63 in *. rewrite pow2_64.
  destruct (Z.le_gt_cases 0 z) as [P|N].
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z 9223372036854775808); lia.
  - rewrite <- (Z.mod_unique z 18446744073709551616 (-1) (z + 18446744073709551616)) by lia.
    destruct (Z.ltb_spec (z + 18446744073709551616) 9223372036854775808); lia.
Qed.

Theorem signed64_range : forall z, fits64 (signed64 z).
Proof.
  intros z. unfold fits64, signed64. rewrite pow2_63, pow2_64.
  pose proof (Z.mod_pos_bound z 18446744073709551616 ltac:(lia)).
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); lia.
Qed.

Theorem signed64_periodic : forall z k, signed64 (z + k * 2 ^ 64) = signed64 z.
Proof. intros z k. unfold signed64. rewrite Z.mod_add by (rewrite pow2_64; lia). reflexivity. Qed.

Theorem signed64_idempotent : forall z, signed64 (signed64 z) = signed64 z.
Proof. intros z. apply signed64_id, signed64_range. Qed.

Section Premises.
Variables num rem prefix : Z.
Hypothesis Hnum : 0 <= num <= 999999999999.
Hypothesis Hrem : 0 <= rem <= 2 ^ 63 - 1.
Hypothesis Hprefix : 0 <= prefix <= 706.

Theorem signed64_rem_sub : signed64 (rem - num) = rem - num.
Proof. apply signed64_id. apply (rem_sub_num_fits num rem Hnum Hrem). Qed.

Theorem signed64_mul8 : signed64 (num * 8) = num * 8.
Proof. apply signed64_id, num_mul8_fits, Hnum. Qed.

Theorem signed64_mul24 : signed64 ((num + prefix) * 24) = (num + prefix) * 24.
Proof. apply signed64_id, num_prefix_mul24_fits; assumption. Qed.

Theorem signed64_sum : signed64 (num + prefix) = num + prefix.
Proof. apply signed64_id, num_prefix_sum_fits; assumption. Qed.

Lemma num_fits : fits64 num.
Proof. unfold fits64. rewrite pow2_63. lia. Qed.
Lemma rem_fits : fits64 rem.
Proof. unfold fits64. rewrite pow2_63 in *. lia. Qed.
Lemma prefix_fits : fits64 prefix.
Proof. unfold fits64. rewrite pow2_63. lia. Qed.

Theorem signed64_wrapped_rem_sub : signed64 (signed64 rem - signed64 num) = rem - num.
Proof. rewrite (signed64_id rem rem_fits), (signed64_id num num_fits). exact signed64_rem_sub. Qed.

Theorem signed64_wrapped_mul8 : signed64 (signed64 num * 8) = num * 8.
Proof. rewrite (signed64_id num num_fits). exact signed64_mul8. Qed.

Theorem signed64_wrapped_mul24 :
  signed64 (signed64 (signed64 num + signed64 prefix) * 24) = (num + prefix) * 24.
Proof.
  rewrite (signed64_id num num_fits), (signed64_id prefix prefix_fits), signed64_sum.
  exact signed64_mul24.
Qed.

Theorem signed64_rem_sub_neg_iff : signed64 (rem - num) < 0 <-> num > rem.
Proof. rewrite signed64_rem_sub. lia. Qed.

Theorem signed64_rem_sub_neg_bool : (signed64 (rem - num) <? 0) = (rem <? num).
Proof.
  rewrite signed64_rem_sub. destruct (Z.ltb_spec (rem - num) 0), (Z.ltb_spec rem num); lia.
Qed.
End Premises.
