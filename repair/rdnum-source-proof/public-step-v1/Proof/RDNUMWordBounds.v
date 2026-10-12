From Stdlib Require Import String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From C2Link Require Import PmpCore.
From NumericV5 Require DecimalSignificantV4.
From RDNUM Require Import RDNUMSource RDNUMNumber.
Module M := DecimalSignificantV4.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Definition signed64 (z:Z) : Z := (z+9223372036854775808) mod 18446744073709551616-9223372036854775808.
Lemma signed64_identity z : -9223372036854775808<=z<9223372036854775808 -> signed64 z = z.
Proof. intros H;unfold signed64;rewrite Z.mod_small;lia. Qed.
Definition number_mul_state s := setv (setv (number_prepare s) "t" (vars s "nd"-12)) "num" (vars s "num"*10).
Theorem checked_source_accumulator_signed64 s n :
  (n<12)%coq_nat -> M.in_range (vars s "num") n ->
  0<=peek s (vars s "pos") 1-48<10 ->
  0<=vars (number_mul_state s) "num"<=999999999990 /\
  0<=vars (number_sig_step s) "num"<=999999999999 /\
  signed64 (vars (number_mul_state s) "num") = vars (number_mul_state s) "num" /\
  signed64 (vars (number_sig_step s) "num") = vars (number_sig_step s) "num".
Proof.
  intros Hn Ha Hd.
  have Hn11 : (n<=11)%coq_nat by lia.
  have Hp := @M.pow10_monotone n 11 Hn11.
  unfold M.in_range in Ha. cbn [M.pow10] in Hp.
  have Hnum : 0<=vars s "num"<=99999999999 by lia.
  change (0<=vars s "num"*10<=999999999990 /\
    0<=vars s "num"*10+(peek s (vars s "pos") 1-48)<=999999999999 /\
    signed64 (vars s "num"*10) = vars s "num"*10 /\
    signed64 (vars s "num"*10+(peek s (vars s "pos") 1-48)) = vars s "num"*10+(peek s (vars s "pos") 1-48)).
  repeat split;try nia;apply signed64_identity;nia.
Qed.
Theorem source_cursor_subtraction_signed64 pos lim :
  0<=pos<=lim -> lim<4611686018427387904 ->
  signed64 (pos-lim) = pos-lim /\ ((signed64 (pos-lim) <? 0) = (pos <? lim)).
Proof.
  intros Hpos Hlim. have Hfit : -9223372036854775808<=pos-lim<9223372036854775808 by lia.
  rewrite (@signed64_identity (pos-lim) Hfit). split;[reflexivity|].
  destruct (Z_lt_ge_dec pos lim) as [H|H].
  - have A : (pos-lim <? 0) = true by apply Z.ltb_lt;lia.
    have B : (pos <? lim) = true by apply Z.ltb_lt;lia. now rewrite A B.
  - have A : (pos-lim <? 0) = false by apply Z.ltb_ge;lia.
    have B : (pos <? lim) = false by apply Z.ltb_ge;lia. now rewrite A B.
Qed.
Print Assumptions checked_source_accumulator_signed64.
Print Assumptions source_cursor_subtraction_signed64.
