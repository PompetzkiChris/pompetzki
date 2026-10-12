(* GrokUnsigned64.v - Grok Bot, new file. Unsigned 64-bit word / ALU arithmetic model over Z,
   bridged to signed64 from GrokSigned64. MODEL BOUNDARY: arithmetic model only; no statement
   about pmp/Racket/native code, compiler, or RECORDCOUNT source instruction semantics. *)
From Stdlib Require Import ZArith Lia.
From GrokRC Require Import GrokRecordCount GrokSigned64.
Open Scope Z_scope.

Definition encode64 (z : Z) : Z := z mod 2 ^ 64.
Definition decode64 (u : Z) : Z := if u <? 2 ^ 63 then u else u - 2 ^ 64.
Definition wadd64 (a b : Z) : Z := (a + b) mod 2 ^ 64.
Definition wsub64 (a b : Z) : Z := (a - b) mod 2 ^ 64.
Definition wmul64 (a b : Z) : Z := (a * b) mod 2 ^ 64.
Definition topbit64 (u : Z) : bool := (u / 2 ^ 63) mod 2 =? 1.

Theorem decode_encode64 : forall z, decode64 (encode64 z) = signed64 z.
Proof. reflexivity. Qed.

Theorem encode64_range : forall z, 0 <= encode64 z < 2 ^ 64.
Proof. intros z. apply Z.mod_pos_bound. rewrite pow2_64. lia. Qed.

Theorem encode_decode64 : forall u, 0 <= u < 2 ^ 64 -> encode64 (decode64 u) = u.
Proof.
  intros u H. unfold encode64, decode64. rewrite pow2_64, pow2_63 in *.
  destruct (Z.ltb_spec u 9223372036854775808).
  - apply Z.mod_small; lia.
  - symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

Theorem decode_encode64_fits : forall z, fits64 z -> decode64 (encode64 z) = z.
Proof. intros z H. rewrite decode_encode64. apply signed64_id, H. Qed.

Theorem topbit64_neg_bool : forall u, 0 <= u < 2 ^ 64 -> topbit64 u = (decode64 u <? 0).
Proof.
  intros u H. unfold topbit64, decode64. rewrite pow2_64, pow2_63 in *.
  destruct (Z.ltb_spec u 9223372036854775808).
  - rewrite Z.div_small by lia. destruct (Z.ltb_spec u 0); [lia|reflexivity].
  - rewrite <- (Z.div_unique u 9223372036854775808 1 (u - 9223372036854775808)) by lia.
    destruct (Z.ltb_spec (u - 18446744073709551616) 0); [reflexivity|lia].
Qed.

Theorem topbit64_neg_iff : forall u, 0 <= u < 2 ^ 64 -> (topbit64 u = true <-> decode64 u < 0).
Proof. intros u H. rewrite topbit64_neg_bool by exact H. apply Z.ltb_lt. Qed.

Lemma wsub64_encode : forall a b, wsub64 (encode64 a) (encode64 b) = encode64 (a - b).
Proof. intros. unfold wsub64, encode64. rewrite <- Zminus_mod. reflexivity. Qed.
Lemma wadd64_encode : forall a b, wadd64 (encode64 a) (encode64 b) = encode64 (a + b).
Proof. intros. unfold wadd64, encode64. rewrite <- Zplus_mod. reflexivity. Qed.
Lemma wmul64_encode_l : forall a k, wmul64 (encode64 a) k = encode64 (a * k).
Proof. intros. unfold wmul64, encode64. rewrite Zmult_mod_idemp_l. reflexivity. Qed.

Section Premises.
Variables num rem prefix : Z.
Hypothesis Hnum : 0 <= num <= 999999999999.
Hypothesis Hrem : 0 <= rem <= 2 ^ 63 - 1.
Hypothesis Hprefix : 0 <= prefix <= 706.

(* bridges to GrokSigned64 *)
Theorem bridge_rem_sub : decode64 (wsub64 (encode64 rem) (encode64 num)) = signed64 (rem - num).
Proof. rewrite wsub64_encode. apply decode_encode64. Qed.
Theorem bridge_mul8 : decode64 (wmul64 (encode64 num) 8) = signed64 (num * 8).
Proof. rewrite wmul64_encode_l. apply decode_encode64. Qed.
Theorem bridge_mul24 :
  decode64 (wmul64 (wadd64 (encode64 num) (encode64 prefix)) 24) = signed64 ((num + prefix) * 24).
Proof. rewrite wadd64_encode, wmul64_encode_l. apply decode_encode64. Qed.

Theorem u64_rem_sub : decode64 (wsub64 (encode64 rem) (encode64 num)) = rem - num.
Proof. rewrite bridge_rem_sub. apply signed64_rem_sub; assumption. Qed.

Theorem u64_rem_sub_topbit_iff : topbit64 (wsub64 (encode64 rem) (encode64 num)) = true <-> num > rem.
Proof.
  rewrite wsub64_encode, topbit64_neg_iff by apply encode64_range.
  rewrite <- wsub64_encode, u64_rem_sub. lia.
Qed.

Theorem u64_rem_sub_topbit_bool : topbit64 (wsub64 (encode64 rem) (encode64 num)) = (rem <? num).
Proof.
  rewrite wsub64_encode, topbit64_neg_bool by apply encode64_range.
  rewrite <- wsub64_encode, u64_rem_sub.
  destruct (Z.ltb_spec (rem - num) 0), (Z.ltb_spec rem num); lia.
Qed.

Theorem u64_mul8 : decode64 (wmul64 (encode64 num) 8) = num * 8.
Proof. rewrite bridge_mul8. apply signed64_mul8; assumption. Qed.

Theorem u64_mul8_topbit : topbit64 (wmul64 (encode64 num) 8) = false.
Proof.
  rewrite wmul64_encode_l, topbit64_neg_bool by apply encode64_range.
  rewrite <- wmul64_encode_l, u64_mul8. apply Z.ltb_ge. lia.
Qed.

Theorem u64_mul24 : decode64 (wmul64 (wadd64 (encode64 num) (encode64 prefix)) 24) = (num + prefix) * 24.
Proof. rewrite bridge_mul24. apply signed64_mul24; assumption. Qed.

Theorem u64_mul24_topbit : topbit64 (wmul64 (wadd64 (encode64 num) (encode64 prefix)) 24) = false.
Proof.
  rewrite wadd64_encode, wmul64_encode_l, topbit64_neg_bool by apply encode64_range.
  rewrite <- wmul64_encode_l, <- wadd64_encode, u64_mul24. apply Z.ltb_ge. lia.
Qed.
End Premises.
