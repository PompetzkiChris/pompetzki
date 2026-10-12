(* Arbitrary overlength digit sequences, composed from actual instruction steps. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono RunKit.
From RDNUM Require Import RDNUMSource RDNUMTools RDNUMReaders RDNUMNumber RDNUMPolicy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition readonly_old (s sf:state) :=
  hp s<=hp sf /\ forall a,a<hp s->mem sf a=mem s a.
Lemma readonly_frame_trans ns s t sf :
  reader_frame ns s t -> readonly_old t sf -> readonly_old s sf.
Proof. intros [Hm [Hhp _]] [Hbound Hread]. split;[congruence|].
  intros a Ha. rewrite Hm Hhp in Hbound,Hread. exact (Hread a Ha). Qed.
Lemma number_limit_readonly s : readonly_old s (number_limit s).
Proof.
  split.
  - unfold number_limit,number_prepare. rewrite text_new_hpE !setv_hp.
    have Hsize := Nat2Z.is_nonneg (size (bytes_of_str "a number has more than 12 significant digits")). lia.
  - intros a Ha. exact (proj2 (proj2 (proj2 (number_limit_no_accumulator_update s))) a Ha).
Qed.

Definition next_number (d:Z) (s:state) :=
  if ((vars s "nd" =? 0)&&(d =? 0))%bool then number_lead_step s else number_sig_step s.
Lemma next_number_continue d s ks r :
  vars s "pos"<vars s "lim" -> peek s (vars s "pos") 1=d+48 -> 0<=d<10 ->
  0<=vars s "nd"<12 ->
  evals Preader reader_stops pc_RDNUM1 ks (next_number d s) r ->
  evals Preader reader_stops pc_RDNUM1 ks s r.
Proof.
  intros Hp Hbyte Hd Hnd Hr. unfold next_number in Hr.
  destruct (((vars s "nd" =? 0)&&(d =? 0))%bool) eqn:Hz.
  - apply Bool.andb_true_iff in Hz;destruct Hz as [Hn Hd0].
    apply Z.eqb_eq in Hn,Hd0;subst d.
    eapply reader_prefix with (n:=17%N);[|exact Hr]. intro f.
    apply RDNUM_leading_zero;[exact Hp|rewrite Hbyte;lia|exact Hn].
  - destruct (Z.eq_dec (vars s "nd") 0) as [Hn|Hn].
    + have Hdpos : d<>0 by intro H;subst d;rewrite Hn in Hz;discriminate.
      eapply reader_prefix with (n:=24%N);[|exact Hr]. intro f.
      apply RDNUM_first_nonzero_digit;[exact Hp|rewrite Hbyte;lia|exact Hn].
    + eapply reader_prefix with (n:=23%N);[|exact Hr]. intro f.
      apply RDNUM_significant_digit;[exact Hp|rewrite Hbyte;lia|lia].
Qed.

Theorem RDNUM_source_sequence_refusal ds s ks :
  Forall (fun d=>0<=d<10) ds -> digit_segment s (vars s "pos") ds ->
  0<=vars s "nd"<=12 -> vars s "pos"+Z.of_nat (List.length ds)<=vars s "lim" ->
  scan_state ds s=None ->
  exists sf, evals Preader reader_stops pc_RDNUM1 ks s (OStop "FAIL" sf) /\ readonly_old s sf.
Proof.
  induction ds as [|d ds IH] in s |- *.
  - cbn [scan_state];discriminate.
  - cbn [scan_state digit_segment]. intros Hds [Hd Htail] Hnd Hb Hscan.
    apply Forall_cons_iff in Hds;destruct Hds as [Hdigit Hrest].
    have Hp : vars s "pos"<vars s "lim" by rewrite List.length_cons Nat2Z.inj_succ in Hb;lia.
    destruct (((vars s "nd" =? 0)&&(d =? 0))%bool) eqn:Hz.
    + destruct (IH (number_lead_step s)) as [sf [Hrun Hreadonly]].
      * exact Hrest.
      * change (digit_segment (number_lead_step s) (vars s "pos"+1) ds).
        apply (@digit_segment_memory s (number_lead_step s) _ ds);[reflexivity|exact Htail].
      * exact Hnd.
      * change (vars s "pos"+1+Z.of_nat (List.length ds)<=vars s "lim").
        rewrite List.length_cons Nat2Z.inj_succ in Hb;lia.
      * exact Hscan.
      * exists sf. split.
        -- apply Bool.andb_true_iff in Hz;destruct Hz as [Hn Hd0].
           apply Z.eqb_eq in Hn,Hd0;subst d.
           eapply reader_prefix with (n:=17%N);[|exact Hrun]. intro f.
           apply RDNUM_leading_zero;[exact Hp|rewrite Hd;lia|exact Hn].
        -- eapply readonly_frame_trans;[apply lead_frame|exact Hreadonly].
    + destruct (vars s "nd" <? 12) eqn:Hlt.
      * apply Z.ltb_lt in Hlt.
        destruct (IH (number_sig_step s)) as [sf [Hrun Hreadonly]].
        -- exact Hrest.
        -- change (digit_segment (number_sig_step s) (vars s "pos"+1) ds).
           apply (@digit_segment_memory s (number_sig_step s) _ ds);[reflexivity|exact Htail].
        -- change (0<=vars s "nd"+1<=12);lia.
        -- change (vars s "pos"+1+Z.of_nat (List.length ds)<=vars s "lim").
           rewrite List.length_cons Nat2Z.inj_succ in Hb;lia.
        -- exact Hscan.
        -- exists sf. split.
           ++ apply (@next_number_continue d s ks (OStop "FAIL" sf));try assumption.
              ** lia.
              ** unfold next_number;now rewrite Hz.
           ++ eapply readonly_frame_trans;[apply significant_frame|exact Hreadonly].
      * apply Z.ltb_ge in Hlt. have Htwelve : vars s "nd" = 12 by lia.
        have Hexec := @RDNUM_thirteenth_significant_refused s ks Hp.
        have Hdig : 0<=peek s (vars s "pos") 1-48<10 by rewrite Hd;lia.
        specialize (Hexec Hdig Htwelve).
        have Hnot : exec 18 Preader reader_stops pc_RDNUM1 ks s<>OFuel by rewrite Hexec;discriminate.
        exists (number_limit s). split.
        -- have Hrun := @evals_exec 18 Preader reader_stops pc_RDNUM1 ks s Hnot. now rewrite Hexec in Hrun.
        -- apply number_limit_readonly.
Qed.
Print Assumptions RDNUM_source_sequence_refusal.
