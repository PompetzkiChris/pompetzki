From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From NumericV5 Require DecimalSignificantV4.
From RDNUM Require Import RDNUMSource RDNUMTools RDNUMCalls RDNUMReaders RDNUMNumber.
Module M := DecimalSignificantV4.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Fixpoint digit_segment (st:state) (p:Z) (ds:list Z) : Prop :=
  match ds with [] => True | d::tail => peek st p 1 = d+48 /\ digit_segment st (p+1) tail end.
Lemma digit_segment_memory s t p ds : mem s = mem t -> digit_segment s p ds -> digit_segment t p ds.
Proof.
  intros Hm. induction ds in p |- *; cbn [digit_segment]; [tauto|].
  intros [Hd Hr]. split; [|apply IHds;exact Hr]. unfold peek in *;simpl in *;now rewrite -Hm.
Qed.
Definition number_locals : list string := [:: "pos";"t";"c";"d";"num";"nd";"nseen"].
Ltac number_frame := unfold reader_frame; repeat split; try reflexivity;
 intros x Hx; repeat rewrite setv_get;
 repeat match goal with |- context [String.eqb x ?name] =>
  let H:=fresh "Hname" in assert (H:String.eqb x name=false) by
   (apply String.eqb_neq; intro Heq; subst x; apply Hx; unfold number_locals; simpl; auto 12); rewrite H
 end; reflexivity.
Lemma lead_frame s : reader_frame number_locals s (number_lead_step s).
Proof. unfold number_lead_step,number_prepare,setv; number_frame. Qed.
Lemma significant_frame s : reader_frame number_locals s (number_sig_step s).
Proof. unfold number_sig_step,number_prepare,setv; number_frame. Qed.
Lemma step_lim s : vars (number_lead_step s) "lim" = vars s "lim" /\ vars (number_sig_step s) "lim" = vars s "lim".
Proof. split;reflexivity. Qed.
Fixpoint scan_state (ds:list Z) (st:state) : option state :=
  match ds with
  | [] => Some st
  | d::tail => if ((vars st "nd" =? 0) && (d =? 0))%bool
      then scan_state tail (number_lead_step st)
      else if (vars st "nd" <? 12) then scan_state tail (number_sig_step st) else None
  end.

Theorem RDNUM_source_sequence ds s sd ks r :
  Forall (fun d => 0<=d<10) ds -> digit_segment s (vars s "pos") ds ->
  0<=vars s "nd"<=12 -> vars s "pos"+Z.of_nat (List.length ds)<=vars s "lim" ->
  scan_state ds s = Some sd -> evals Preader reader_stops pc_RDNUM1 ks sd r ->
  evals Preader reader_stops pc_RDNUM1 ks s r.
Proof.
  induction ds as [|d ds IH] in s,sd |- *.
  - cbn [scan_state]. intros _ _ _ _ H Hr. inversion H;subst;exact Hr.
  - cbn [scan_state digit_segment]. intros Hdigits [Hd Htail] Hnd Hpos Hscan Hr.
    inversion Hdigits as [|? ? Hdigit Hrest];subst.
    have Hlt : vars s "pos"<vars s "lim" by rewrite List.length_cons Nat2Z.inj_succ in Hpos;lia.
    destruct (((vars s "nd" =? 0) && (d =? 0))%bool) eqn:Hz.
    + apply Bool.andb_true_iff in Hz. destruct Hz as [Hn Hd0].
      apply Z.eqb_eq in Hn,Hd0;subst d.
      eapply reader_prefix with (n:=17%N).
      * intro f; apply RDNUM_leading_zero; [exact Hlt|rewrite Hd;lia|exact Hn].
      * apply (IH (number_lead_step s) sd).
        -- exact Hrest.
        -- change (digit_segment (number_lead_step s) (vars s "pos"+1) ds).
           apply (@digit_segment_memory s (number_lead_step s) (vars s "pos"+1) ds);[reflexivity|exact Htail].
        -- change (0<=vars s "nd"<=12);exact Hnd.
        -- change (vars s "pos"+1+Z.of_nat (List.length ds)<=vars s "lim").
           rewrite List.length_cons Nat2Z.inj_succ in Hpos;lia.
        -- exact Hscan.
        -- exact Hr.
    + destruct (vars s "nd" <? 12) eqn:Hbound;try discriminate.
      apply Z.ltb_lt in Hbound.
      have Hrun : forall f, exec (24+f)%N Preader reader_stops pc_RDNUM1 ks s =
          exec f Preader reader_stops pc_RDNUM1 ks (number_sig_step s) \/
          exec (23+f)%N Preader reader_stops pc_RDNUM1 ks s = exec f Preader reader_stops pc_RDNUM1 ks (number_sig_step s).
      { intro f. destruct (Z.eq_dec (vars s "nd") 0) as [Hn|Hn].
        - left;apply RDNUM_first_nonzero_digit;[exact Hlt| |exact Hn]. rewrite Hd.
          assert (d<>0) by (intro H;subst d;rewrite Hn in Hz;discriminate). lia.
        - right;apply RDNUM_significant_digit;[exact Hlt|rewrite Hd;lia|lia]. }
      have Hcontinue : evals Preader reader_stops pc_RDNUM1 ks (number_sig_step s) r.
      { apply (IH (number_sig_step s) sd).
        - exact Hrest.
        - change (digit_segment (number_sig_step s) (vars s "pos"+1) ds).
          apply (@digit_segment_memory s (number_sig_step s) (vars s "pos"+1) ds);[reflexivity|exact Htail].
        - change (0<=vars s "nd"+1<=12);lia.
        - change (vars s "pos"+1+Z.of_nat (List.length ds)<=vars s "lim").
          rewrite List.length_cons Nat2Z.inj_succ in Hpos;lia.
        - exact Hscan.
        - exact Hr. }
      destruct (Z.eq_dec (vars s "nd") 0) as [Hn|Hn].
      * eapply reader_prefix with (n:=24%N);[|exact Hcontinue]. intro f.
        apply RDNUM_first_nonzero_digit;[exact Hlt| |exact Hn]. rewrite Hd.
        assert (d<>0) by (intro H;subst d;rewrite Hn in Hz;discriminate). lia.
      * eapply reader_prefix with (n:=23%N);[|exact Hcontinue]. intro f.
        apply RDNUM_significant_digit;[exact Hlt|rewrite Hd;lia|lia].
Qed.
Print Assumptions RDNUM_source_sequence.

Lemma of_nat_eqb_zero n : (Z.of_nat n =? 0) = Nat.eqb n 0.
Proof. destruct n;reflexivity. Qed.
Lemma of_nat_ltb_twelve n : (Z.of_nat n <? 12) = Nat.ltb n 12.
Proof.
  destruct (Z_lt_ge_dec (Z.of_nat n) 12) as [H|H].
  - have A : (Z.of_nat n <? 12) = true by apply Z.ltb_lt;exact H.
    have B : Nat.ltb n 12 = true by apply Nat.ltb_lt;lia. now rewrite A B.
  - have A : (Z.of_nat n <? 12) = false by apply Z.ltb_ge;lia.
    have B : Nat.ltb n 12 = false by apply Nat.ltb_ge;lia. now rewrite A B.
Qed.
Lemma digit_model_true d : 0<=d<10 -> M.digit d = true.
Proof.
  intros H. unfold M.digit. apply Bool.andb_true_iff;split;
    [apply Z.leb_le|apply Z.ltb_lt];lia.
Qed.

Theorem scan_state_decimal_correspondence ds st a n :
  Forall (fun d=>0<=d<10) ds -> digit_segment st (vars st "pos") ds ->
  vars st "num" = a -> vars st "nd" = Z.of_nat n ->
  omap (fun sf=>vars sf "num") (scan_state ds st) = M.parse_digits ds a n.
Proof.
  induction ds as [|d ds IH] in st,a,n |- *.
  - intros _ _ Ha _. change (Some (vars st "num") = Some a). f_equal;exact Ha.
  - cbn [digit_segment]. intros Hdigits [Hd Htail] Ha Hn.
    apply Forall_cons_iff in Hdigits. destruct Hdigits as [Hdig Hrest].
    have HT := digit_model_true Hdig.
    cbn [scan_state M.parse_digits]. rewrite HT Hn of_nat_eqb_zero of_nat_ltb_twelve.
    destruct (((Nat.eqb n 0) && (d =? 0))%bool) eqn:Hz.
    + apply IH.
      * exact Hrest.
      * change (digit_segment (number_lead_step st) (vars st "pos"+1) ds).
        apply (@digit_segment_memory st (number_lead_step st) (vars st "pos"+1) ds);[reflexivity|exact Htail].
      * exact Ha.
      * exact Hn.
    + destruct (Nat.ltb n 12) eqn:Hbound;[|reflexivity].
      apply IH.
      * exact Hrest.
      * change (digit_segment (number_sig_step st) (vars st "pos"+1) ds).
        apply (@digit_segment_memory st (number_sig_step st) (vars st "pos"+1) ds);[reflexivity|exact Htail].
      * change (vars st "num"*10+(peek st (vars st "pos") 1-48) = 10*a+d).
        rewrite Ha Hd;ring.
      * change (vars st "nd"+1 = Z.of_nat (S n)). rewrite Hn Nat2Z.inj_succ;lia.
Qed.
Print Assumptions scan_state_decimal_correspondence.

Theorem scan_state_success_properties ds s sd :
  0<=vars s "nd"<=12 -> scan_state ds s = Some sd ->
  reader_frame number_locals s sd /\
  vars sd "pos" = vars s "pos"+Z.of_nat (List.length ds) /\
  0<=vars sd "nd"<=12 /\
  vars sd "nseen" = (if ds is [] then vars s "nseen" else 1).
Proof.
  induction ds as [|d ds IH] in s,sd |- *.
  - cbn [scan_state List.length]. intros Hn Heq;inversion Heq;subst sd.
    split;[apply reader_frame_refl|]. repeat split;try lia;reflexivity.
  - cbn [scan_state]. intros Hn Hscan.
    destruct (((vars s "nd" =? 0) && (d =? 0))%bool) eqn:Hz.
    + have Hn' : 0<=vars (number_lead_step s) "nd"<=12 by exact Hn.
      destruct (IH (number_lead_step s) sd Hn' Hscan) as [Hf [Hp [Hnd Hseen]]].
      split;[eapply reader_frame_trans;[apply lead_frame|exact Hf]|].
      split.
      * rewrite Hp. change (vars s "pos"+1+Z.of_nat (List.length ds) = vars s "pos"+Z.of_nat (List.length (d::ds))).
        rewrite List.length_cons Nat2Z.inj_succ;lia.
      * split;[exact Hnd|]. destruct ds;exact Hseen.
    + destruct (vars s "nd" <? 12) eqn:Hlimit;try discriminate.
      apply Z.ltb_lt in Hlimit.
      have Hn' : 0<=vars (number_sig_step s) "nd"<=12 by change (0<=vars s "nd"+1<=12);lia.
      destruct (IH (number_sig_step s) sd Hn' Hscan) as [Hf [Hp [Hnd Hseen]]].
      split;[eapply reader_frame_trans;[apply significant_frame|exact Hf]|].
      split.
      * rewrite Hp. change (vars s "pos"+1+Z.of_nat (List.length ds) = vars s "pos"+Z.of_nat (List.length (d::ds))).
        rewrite List.length_cons Nat2Z.inj_succ;lia.
      * split;[exact Hnd|]. destruct ds;exact Hseen.
Qed.

Theorem RDNUM_source_refines_decimal ds s value :
  Forall (fun d=>0<=d<10) ds -> digit_segment s (vars s "pos") ds ->
  vars s "num" = 0 -> vars s "nd" = 0 ->
  vars s "pos"+Z.of_nat (List.length ds)<=vars s "lim" ->
  (vars s "pos"+Z.of_nat (List.length ds) = vars s "lim" \/
   whitespace (peek s (vars s "pos"+Z.of_nat (List.length ds)) 1)) ->
  M.parse_decimal ds = Some value ->
  exists sf, evals Preader reader_stops pc_RDNUM1 [::] s (OReturn sf) /\
    vars sf "num" = value /\ vars sf "pos" = vars s "pos"+Z.of_nat (List.length ds) /\
    mem sf = mem s /\ hp sf = hp s /\ 0<=value<=999999999999 /\ value<9223372036854775808.
Proof.
  intros Hd Hseg Hnum Hnd Hb Hdelim Hparse.
  have Hne : ds<>[] by intro He;subst ds;discriminate.
  have Hdigits : M.parse_digits ds 0 0 = Some value by destruct ds;[contradiction|exact Hparse].
  have Hmap := @scan_state_decimal_correspondence ds s 0 0 Hd Hseg Hnum Hnd.
  rewrite Hdigits in Hmap.
  destruct (scan_state ds s) as [sd|] eqn:Hscan;[|discriminate].
  cbn [omap] in Hmap;inversion Hmap as [Hvalue].
  have Hn : 0<=vars s "nd"<=12 by rewrite Hnd;lia.
  destruct (@scan_state_success_properties ds s sd Hn Hscan) as [Hf [Hp [Hnb Hseen]]].
  have Hlim : vars sd "lim" = vars s "lim".
  { apply (@reader_frame_var number_locals s sd "lim" Hf). unfold number_locals;simpl;intuition discriminate. }
  have Hseen' : vars sd "nseen"<>0 by destruct ds;[contradiction|rewrite Hseen;lia].
  have Hbound : vars sd "pos"<=vars sd "lim" by rewrite Hp Hlim;exact Hb.
  have Hstop : vars sd "pos" = vars sd "lim" \/ whitespace (peek sd (vars sd "pos") 1).
  { rewrite Hp Hlim. have Hmem := @reader_frame_byte number_locals s sd (vars s "pos"+Z.of_nat (List.length ds)) Hf.
    unfold byte_at in Hmem;rewrite Hmem;exact Hdelim. }
  destruct (@RDNUM_finish_success sd Hbound Hseen' Hstop) as [sf [Hrun Hfinish]].
  have Hfinalnum : vars sf "num" = vars sd "num".
  { apply (@reader_frame_var finish_locals sd sf "num" Hfinish). unfold finish_locals;simpl;intuition discriminate. }
  have Hfinalpos : vars sf "pos" = vars sd "pos".
  { apply (@reader_frame_var finish_locals sd sf "pos" Hfinish). unfold finish_locals;simpl;intuition discriminate. }
  have Hrange := @M.parse_decimal_bound ds value Hparse.
  exists sf. split.
  - apply (@RDNUM_source_sequence ds s sd [::] (OReturn sf));assumption.
  - rewrite Hfinalnum Hvalue Hfinalpos Hp. repeat split;try lia.
    + destruct Hfinish as [Hm _],Hf as [Hm' _];congruence.
    + destruct Hfinish as [_ [Hhp _]],Hf as [_ [Hhp' _]];congruence.
Qed.
Print Assumptions RDNUM_source_refines_decimal.
