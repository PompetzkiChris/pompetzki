(* Accumulator/cursor invariants at every reachable digit-prefix state. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From C2Link Require Import PmpCore ExecMono.
From RDNUM Require Import RDNUMSource RDNUMReaders RDNUMNumber RDNUMPolicy RDNUMWordBounds
  RDNUMRefusal RDNUMLexical RDNUMBuffer.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Theorem scan_state_accumulator_invariant ds s sd n :
  Forall (fun d=>0<=d<10) ds -> digit_segment s (vars s "pos") ds ->
  vars s "nd"=Z.of_nat n -> (n<=12)%coq_nat -> M.in_range (vars s "num") n ->
  scan_state ds s=Some sd ->
  exists n', vars sd "nd"=Z.of_nat n' /\ (n'<=12)%coq_nat /\ M.in_range (vars sd "num") n'.
Proof.
  induction ds as [|d ds IH] in s,sd,n |- *.
  - cbn [scan_state]. intros _ _ Hnd Hn Ha E;inversion E;subst sd. exists n;tauto.
  - cbn [digit_segment scan_state]. intros Hds [Hd Htail] Hnd Hn Ha Hscan.
    apply Forall_cons_iff in Hds;destruct Hds as [Hdigit Hrest].
    destruct (((vars s "nd" =? 0)&&(d =? 0))%bool) eqn:Hz.
    + apply (IH (number_lead_step s) sd n);try assumption.
      change (digit_segment (number_lead_step s) (vars s "pos"+1) ds).
      apply (@digit_segment_memory s (number_lead_step s) _ ds);[reflexivity|exact Htail].
    + destruct (vars s "nd" <? 12) eqn:Hlt;[|discriminate].
      apply Z.ltb_lt in Hlt. have Hnlt : (n<12)%coq_nat by rewrite Hnd in Hlt;lia.
      apply (IH (number_sig_step s) sd (S n)).
      * exact Hrest.
      * change (digit_segment (number_sig_step s) (vars s "pos"+1) ds).
        apply (@digit_segment_memory s (number_sig_step s) _ ds);[reflexivity|exact Htail].
      * change (vars s "nd"+1=Z.of_nat (S n));rewrite Hnd Nat2Z.inj_succ;lia.
      * lia.
      * change (M.in_range (vars s "num"*10+(peek s (vars s "pos") 1-48)) (S n)).
        rewrite Hd. replace (vars s "num"*10+(d+48-48)) with (10*vars s "num"+d) by ring.
        apply M.checked_step_range;assumption.
      * exact Hscan.
Qed.

Theorem source_prefix_next_arithmetic_fits ds s sd d n :
  Forall (fun x=>0<=x<10) ds -> digit_segment s (vars s "pos") ds ->
  vars s "nd"=Z.of_nat n -> (n<=12)%coq_nat -> M.in_range (vars s "num") n ->
  scan_state ds s=Some sd -> 0<=d<10 -> peek sd (vars sd "pos") 1=d+48 ->
  vars sd "nd"<12 ->
  0<=vars (number_mul_state sd) "num"<=999999999990 /\
  0<=vars (number_sig_step sd) "num"<=999999999999 /\
  signed64 (vars (number_mul_state sd) "num")=vars (number_mul_state sd) "num" /\
  signed64 (vars (number_sig_step sd) "num")=vars (number_sig_step sd) "num".
Proof.
  intros Hd Hseg Hnd Hn Ha Hscan Hdigit Hbyte Hcount.
  destruct (@scan_state_accumulator_invariant ds s sd n Hd Hseg Hnd Hn Ha Hscan) as [k [Hk [Hkb Hak]]].
  apply (@checked_source_accumulator_signed64 sd k).
  - rewrite Hk in Hcount;lia.
  - exact Hak.
  - rewrite Hbyte;lia.
Qed.

Lemma buffer_segment_readonly s t p raw :
  p+Z.of_nat (List.length raw)<=hp s ->
  (forall a,a<hp s->mem t a=mem s a) ->
  buffer_segment s p raw -> buffer_segment t p raw.
Proof.
  induction raw as [|b raw IH] in p |- *;cbn [buffer_segment];[tauto|].
  intros Hbound Hmem [Hbyte Htail]. split.
  - unfold peek in Hbyte|-*;cbn in Hbyte|-*. rewrite Hmem;[exact Hbyte|].
    rewrite List.length_cons Nat2Z.inj_succ in Hbound;lia.
  - apply IH;try assumption. rewrite List.length_cons Nat2Z.inj_succ in Hbound;lia.
Qed.

Theorem RDNUM_buffer_failure_input_unchanged s raw :
  buffer_segment s (vars s "pos") raw -> vars s "lim"=vars s "pos"+Z.of_nat (List.length raw) ->
  vars s "lim"<=hp s -> parse_buffer raw=None ->
  exists sf, evals Preader reader_stops pc_RDNUM [] s (OStop "FAIL" sf) /\
    readonly_old s sf /\ buffer_segment sf (vars s "pos") raw.
Proof.
  intros Hbuf Hlim Hhp Hparse.
  destruct (@RDNUM_buffer_parse_failure s raw Hbuf Hlim Hparse) as [sf [Hr Hreadonly]].
  exists sf. split;[exact Hr|]. split;[exact Hreadonly|].
  apply (@buffer_segment_readonly s sf (vars s "pos") raw);[lia|exact (proj2 Hreadonly)|exact Hbuf].
Qed.
Print Assumptions scan_state_accumulator_invariant.
Print Assumptions source_prefix_next_arithmetic_fits.
Print Assumptions RDNUM_buffer_failure_input_unchanged.
