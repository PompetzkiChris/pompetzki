(* Source-state subtraction bounds, using unchanged Grok arithmetic declarations. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From C2Link Require Import PmpCore ExecMono.
From GrokRC Require GrokRecordCount.
From RecordCount Require Import RecordCountSource RecordCountStep RecordCountMemory.
Module G := GrokRecordCount.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition count_address_contract (s:state) : Prop :=
  0<=vars s "num"<=999999999999 /\
  0<=vars s "pos"<=vars s "lim" /\
  vars s "lim"<=hp s /\ hp s<4611686018427387904.
Definition signed64 (z:Z) := (z+9223372036854775808) mod 18446744073709551616-9223372036854775808.
Lemma fits64_signed64_identity z : G.fits64 z -> signed64 z=z.
Proof. intros H;unfold G.fits64 in H;rewrite G.pow2_63 in H.
  unfold signed64;rewrite Z.mod_small;lia. Qed.

Theorem RECORDCOUNT_actual_subtractions_fit s : count_address_contract s ->
  vars (first_sub_state s) "t"=vars s "lim"-vars s "pos" /\
  vars (checked_state s) "t"=vars s "lim"-vars s "pos"-vars s "num" /\
  G.fits64 (vars (first_sub_state s) "t") /\
  G.fits64 (vars (checked_state s) "t") /\
  (vars (checked_state s) "t"<0 <-> vars s "num">remaining s).
Proof.
  intros [Hnum [Hpos [Hhp Hcap]]].
  have Hr : 0<=remaining s<=2^63-1 by unfold remaining;rewrite G.pow2_63;lia.
  have HG := G.rem_sub_num_fits (vars s "num") (remaining s) Hnum Hr.
  have Hfirst : G.fits64 (remaining s) by unfold G.fits64,remaining;rewrite G.pow2_63;lia.
  split;[reflexivity|]. split;[reflexivity|].
  change (G.fits64 (remaining s) /\ G.fits64 (remaining s-vars s "num") /\
     (remaining s-vars s "num"<0 <-> vars s "num">remaining s)). tauto.
Qed.
Theorem RECORDCOUNT_actual_signed64_test s : count_address_contract s ->
  signed64 (vars (first_sub_state s) "t")=vars (first_sub_state s) "t" /\
  signed64 (vars (checked_state s) "t")=vars (checked_state s) "t" /\
  ((signed64 (vars (checked_state s) "t") <? 0)=(remaining s <? vars s "num")).
Proof.
  intros H. destruct (RECORDCOUNT_actual_subtractions_fit H) as [_ [_ [Ha [Hb Hneg]]]].
  rewrite (fits64_signed64_identity Ha) (fits64_signed64_identity Hb).
  split;[reflexivity|]. split;[reflexivity|].
  change ((remaining s-vars s "num" <? 0)=(remaining s <? vars s "num")).
  destruct (Z_lt_ge_dec (remaining s) (vars s "num")) as [Hlt|Hge].
  - have A : (remaining s-vars s "num" <? 0)=true by apply Z.ltb_lt;lia.
    have B : (remaining s <? vars s "num")=true by apply Z.ltb_lt;exact Hlt. now rewrite A B.
  - have A : (remaining s-vars s "num" <? 0)=false by apply Z.ltb_ge;lia.
    have B : (remaining s <? vars s "num")=false by apply Z.ltb_ge;lia. now rewrite A B.
Qed.
Theorem RECORDCOUNT_diagnostic_word_bounds s : count_address_contract s ->
  G.fits64 (vars (failure_state s) "WHY") /\
  G.fits64 (vars (failure_state s) "WHY_len") /\ G.fits64 (hp (failure_state s)).
Proof.
  intros [Hnum [Hpos [Hhp Hcap]]].
  destruct (failure_state_registers s) as [Ht [Hw [Hl [Halloc Hframe]]]].
  rewrite Hw Hl Halloc. unfold G.fits64;rewrite G.pow2_63;repeat split;lia.
Qed.

Theorem RECORDCOUNT_input_region_unchanged s sf : count_address_contract s ->
  (evals Precord record_stops pc_RECORDCOUNT [] s (OReturn sf) \/
   evals Precord record_stops pc_RECORDCOUNT [] s (OStop "FAIL" sf)) ->
  forall a,vars s "pos"<=a<vars s "lim" -> mem sf a=mem s a.
Proof.
  intros [Hnum [Hpos [Hhp Hcap]]] [Hr|Hr] a Ha.
  - destruct (@RECORDCOUNT_return_effects s sf Hr) as [_ [_ [Hmem _]]]. now rewrite Hmem.
  - destruct (@RECORDCOUNT_failure_effects s sf Hr) as [_ [_ [_ [_ [_ [Hmem _]]]]]].
    apply Hmem;left;lia.
Qed.

Theorem RECORDCOUNT_bounded_returns_iff s : count_address_contract s ->
  ((exists sf,evals Precord record_stops pc_RECORDCOUNT [] s (OReturn sf)) <->
   vars s "num"<=vars s "lim"-vars s "pos").
Proof.
  intros H;split.
  - intros [sf Hr];apply RECORDCOUNT_returns_iff in Hr;exact (proj1 Hr).
  - intro Hle;exists (checked_state s);apply RECORDCOUNT_return_evals;exact Hle.
Qed.
Theorem RECORDCOUNT_bounded_fails_iff s : count_address_contract s ->
  ((exists sf,evals Precord record_stops pc_RECORDCOUNT [] s (OStop "FAIL" sf)) <->
   vars s "num">vars s "lim"-vars s "pos").
Proof.
  intros H;split.
  - intros [sf Hr];apply RECORDCOUNT_fails_iff in Hr;exact (proj1 Hr).
  - intro Hgt;exists (failure_state s);apply RECORDCOUNT_failure_evals;exact Hgt.
Qed.
Print Assumptions RECORDCOUNT_actual_subtractions_fit.
Print Assumptions RECORDCOUNT_actual_signed64_test.
Print Assumptions RECORDCOUNT_diagnostic_word_bounds.
Print Assumptions RECORDCOUNT_input_region_unchanged.
Print Assumptions RECORDCOUNT_bounded_returns_iff.
Print Assumptions RECORDCOUNT_bounded_fails_iff.
