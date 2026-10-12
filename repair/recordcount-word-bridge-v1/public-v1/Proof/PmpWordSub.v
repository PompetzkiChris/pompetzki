(* PMP subtraction-state to unsigned-word arithmetic bridge.
   C2Link, the retained RECORDCOUNT controller, and Grok originals are imported unchanged.
   This does not identify emitted native code or an OS process with either semantics. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From C2Link Require Import PmpCore ExecMono.
From GrokRC Require GrokRecordCount GrokSigned64 GrokUnsigned64.
From RecordCount Require Import RecordCountSource RecordCountStep RecordCountMemory RecordCountBounds.
Import ListNotations.
Module U := GrokUnsigned64.
Module S := GrokSigned64.
Module G := GrokRecordCount.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Theorem PMP_sub_instruction s x a b :
  exec 2 [SSub x a b; SReturn] [] 0 [] s =
  OReturn (setv s x (ev s a-ev s b)).
Proof. reflexivity. Qed.

Theorem PMP_sub_word_commutes s x a b :
  U.wsub64 (U.encode64 (ev s a)) (U.encode64 (ev s b)) =
  U.encode64 (vars (setv s x (ev s a-ev s b)) x).
Proof. rewrite U.wsub64_encode setv_get String.eqb_refl. reflexivity. Qed.

Theorem PMP_sub_word_decode s x a b : G.fits64 (ev s a-ev s b) ->
  U.decode64 (U.wsub64 (U.encode64 (ev s a)) (U.encode64 (ev s b))) =
  vars (setv s x (ev s a-ev s b)) x.
Proof.
  intros H. rewrite U.wsub64_encode (U.decode_encode64_fits _ H).
  rewrite setv_get String.eqb_refl. reflexivity.
Qed.

Theorem PMP_negative_word_commutes z : G.fits64 z ->
  U.topbit64 (U.encode64 z) = test CNeg z.
Proof.
  intros H. rewrite U.topbit64_neg_bool; last apply U.encode64_range.
  rewrite (U.decode_encode64_fits _ H). reflexivity.
Qed.

Definition first_word s := U.wsub64 (U.encode64 (vars s "lim")) (U.encode64 (vars s "pos")).
Definition checked_word s := U.wsub64 (first_word s) (U.encode64 (vars s "num")).

Theorem RECORDCOUNT_words_exact s :
  first_word s = U.encode64 (vars (first_sub_state s) "t") /\
  checked_word s = U.encode64 (vars (checked_state s) "t").
Proof.
  have A : first_word s = U.encode64 (remaining s).
  { unfold first_word,remaining. apply U.wsub64_encode. }
  split; [exact A|]. unfold checked_word. rewrite A U.wsub64_encode. reflexivity.
Qed.

Theorem RECORDCOUNT_word_decode s : count_address_contract s ->
  U.decode64 (first_word s) = vars (first_sub_state s) "t" /\
  U.decode64 (checked_word s) = vars (checked_state s) "t".
Proof.
  intros H. destruct (RECORDCOUNT_words_exact s) as [A B].
  destruct (RECORDCOUNT_actual_subtractions_fit H) as [_ [_ [Ha [Hb _]]]].
  rewrite A B. split; apply U.decode_encode64_fits; assumption.
Qed.

Theorem RECORDCOUNT_word_test s : count_address_contract s ->
  U.topbit64 (checked_word s) = test CNeg (vars (checked_state s) "t") /\
  U.topbit64 (checked_word s) = (remaining s <? vars s "num").
Proof.
  intros H. destruct (RECORDCOUNT_words_exact s) as [_ B].
  destruct (RECORDCOUNT_actual_subtractions_fit H) as [_ [_ [_ [Hb _]]]].
  rewrite B (PMP_negative_word_commutes Hb).
  split; [reflexivity|].
  change ((remaining s-vars s "num" <? 0) = (remaining s <? vars s "num")).
  destruct (Z.ltb_spec (remaining s-vars s "num") 0),
           (Z.ltb_spec (remaining s) (vars s "num")); lia.
Qed.

Theorem RECORDCOUNT_word_control s : count_address_contract s ->
  ((exists sf, evals Precord record_stops pc_RECORDCOUNT [] s (OReturn sf)) <->
    U.topbit64 (checked_word s) = false) /\
  ((exists sf, evals Precord record_stops pc_RECORDCOUNT [] s (OStop "FAIL" sf)) <->
    U.topbit64 (checked_word s) = true).
Proof.
  intros H. destruct (RECORDCOUNT_word_test H) as [_ B]. rewrite B.
  rewrite (RECORDCOUNT_bounded_returns_iff H) (RECORDCOUNT_bounded_fails_iff H).
  split.
  - rewrite Z.ltb_ge. unfold remaining. tauto.
  - rewrite Z.ltb_lt. unfold remaining. lia.
Qed.

Theorem RECORDCOUNT_signed_models_agree s : count_address_contract s ->
  RecordCountBounds.signed64 (vars (first_sub_state s) "t") =
    S.signed64 (vars (first_sub_state s) "t") /\
  RecordCountBounds.signed64 (vars (checked_state s) "t") =
    S.signed64 (vars (checked_state s) "t").
Proof.
  intros H. destruct (RECORDCOUNT_actual_subtractions_fit H) as [_ [_ [Ha [Hb _]]]].
  rewrite (fits64_signed64_identity Ha) (fits64_signed64_identity Hb)
          (S.signed64_id _ Ha) (S.signed64_id _ Hb). split; reflexivity.
Qed.

Theorem RECORDCOUNT_word_execution_prefix s ks f :
  exec (2+f)%N Precord record_stops pc_RECORDCOUNT ks s =
    exec f Precord record_stops 2%N ks (first_sub_state s) /\
  exec (3+f)%N Precord record_stops pc_RECORDCOUNT ks s =
    exec f Precord record_stops 3%N ks (checked_state s) /\
  first_word s = U.encode64 (vars (first_sub_state s) "t") /\
  checked_word s = U.encode64 (vars (checked_state s) "t").
Proof.
  split;[apply RECORDCOUNT_first_subtraction_prefix|].
  split;[apply RECORDCOUNT_subtraction_prefix|]. apply RECORDCOUNT_words_exact.
Qed.

Theorem RECORDCOUNT_return_word_result s sf : count_address_contract s ->
  evals Precord record_stops pc_RECORDCOUNT [] s (OReturn sf) ->
  U.decode64 (checked_word s) = vars sf "t" /\ U.topbit64 (checked_word s) = false.
Proof.
  intros H Hr. destruct (RECORDCOUNT_word_decode H) as [_ Hvalue].
  destruct (RECORDCOUNT_word_control H) as [Hreturn _].
  have Hbit : U.topbit64 (checked_word s) = false.
  { apply Hreturn. exists sf. exact Hr. }
  apply RECORDCOUNT_returns_iff in Hr. destruct Hr as [_ ->]. tauto.
Qed.

Theorem RECORDCOUNT_failure_word_result s sf : count_address_contract s ->
  evals Precord record_stops pc_RECORDCOUNT [] s (OStop "FAIL" sf) ->
  U.decode64 (checked_word s) = vars sf "t" /\ U.topbit64 (checked_word s) = true.
Proof.
  intros H Hr. destruct (RECORDCOUNT_word_decode H) as [_ Hvalue].
  destruct (RECORDCOUNT_word_control H) as [_ Hfailure].
  have Hbit : U.topbit64 (checked_word s) = true.
  { apply Hfailure. exists sf. exact Hr. }
  apply RECORDCOUNT_fails_iff in Hr. destruct Hr as [_ ->].
  destruct (failure_state_registers s) as [Ht _]. rewrite Ht. tauto.
Qed.
