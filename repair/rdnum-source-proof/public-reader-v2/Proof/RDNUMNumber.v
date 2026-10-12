(* The current extracted RDNUM instructions, executed in PmpCore.exec. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From RDNUM Require Import RDNUMSource RDNUMTools RDNUMCalls RDNUMReaders.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition number_prepare (s:state) : state :=
  let c := peek s (vars s "pos") 1 in
  setv (setv (setv (setv (setv s "t" (vars s "pos"-vars s "lim"))
   "c" c) "d" (c-48)) "t" (c-48-10)) "nseen" 1.
Definition number_lead_step (s:state) : state := setv (number_prepare s) "pos" (vars s "pos"+1).
Definition number_sig_step (s:state) : state :=
  let d := peek s (vars s "pos") 1-48 in
  setv (setv (setv (setv (setv (number_prepare s) "t" (vars s "nd"-12))
   "num" (vars s "num"*10)) "num" (vars s "num"*10+d))
   "nd" (vars s "nd"+1)) "pos" (vars s "pos"+1).
Definition number_limit (s:state) : state := text_new
  (setv (number_prepare s) "t" (vars s "nd"-12)) "WHY"
  (bytes_of_str "a number has more than 12 significant digits").

Theorem RDNUM_leading_zero s ks f :
  vars s "pos"<vars s "lim" -> peek s (vars s "pos") 1 = 48 -> vars s "nd" = 0 ->
  exec (17+f)%N Preader reader_stops pc_RDNUM1 ks s  = 
  exec f Preader reader_stops pc_RDNUM1 ks (number_lead_step s).
Proof.
  intros Hp Hc Hnd.
  have Hpos : (vars s "pos"-vars s "lim" <? 0) = true by apply Z.ltb_lt; lia.
  have Hlow : (peek s (vars s "pos") 1-48 <? 0) = false by rewrite Hc.
  have Hhigh : (peek s (vars s "pos") 1-48-10 <? 0) = true by rewrite Hc.
  have Hz : (vars s "nd" =? 0) = true by rewrite Hnd.
  have Hd : (peek s (vars s "pos") 1-48 =? 0) = true by rewrite Hc.
  cbn [addn Nat.add]. do 17 (rinstruction; rewrite ?Hpos ?Hlow ?Hhigh ?Hz ?Hd).
  reflexivity.
Qed.

Theorem RDNUM_significant_digit s ks f :
  vars s "pos"<vars s "lim" -> 0<=peek s (vars s "pos") 1-48<10 ->
  0<vars s "nd"<12 ->
  exec (23+f)%N Preader reader_stops pc_RDNUM1 ks s  = 
  exec f Preader reader_stops pc_RDNUM1 ks (number_sig_step s).
Proof.
  intros Hp Hd Hnd.
  have Hpos : (vars s "pos"-vars s "lim" <? 0) = true by apply Z.ltb_lt; lia.
  have Hlow : (peek s (vars s "pos") 1-48 <? 0) = false by apply Z.ltb_ge; lia.
  have Hhigh : (peek s (vars s "pos") 1-48-10 <? 0) = true by apply Z.ltb_lt; lia.
  have Hz : (vars s "nd" =? 0) = false by apply Z.eqb_neq; lia.
  have Hbound : (vars s "nd"-12 <? 0) = true by apply Z.ltb_lt; lia.
  cbn [addn Nat.add]. do 23 (rinstruction; rewrite ?Hpos ?Hlow ?Hhigh ?Hz ?Hbound).
  reflexivity.
Qed.

Theorem RDNUM_first_nonzero_digit s ks f :
  vars s "pos"<vars s "lim" -> 0<peek s (vars s "pos") 1-48<10 -> vars s "nd" = 0 ->
  exec (24+f)%N Preader reader_stops pc_RDNUM1 ks s  = 
  exec f Preader reader_stops pc_RDNUM1 ks (number_sig_step s).
Proof.
  intros Hp Hd Hnd.
  have Hpos : (vars s "pos"-vars s "lim" <? 0) = true by apply Z.ltb_lt; lia.
  have Hlow : (peek s (vars s "pos") 1-48 <? 0) = false by apply Z.ltb_ge; lia.
  have Hhigh : (peek s (vars s "pos") 1-48-10 <? 0) = true by apply Z.ltb_lt; lia.
  have Hz : (vars s "nd" =? 0) = true by rewrite Hnd.
  have Hd0 : (peek s (vars s "pos") 1-48 =? 0) = false by apply Z.eqb_neq; lia.
  have Hbound : (vars s "nd"-12 <? 0) = true by rewrite Hnd.
  cbn [addn Nat.add]. do 24 (rinstruction; rewrite ?Hpos ?Hlow ?Hhigh ?Hz ?Hd0 ?Hbound).
  reflexivity.
Qed.

Theorem RDNUM_thirteenth_significant_refused s ks :
  vars s "pos"<vars s "lim" -> 0<=peek s (vars s "pos") 1-48<10 -> vars s "nd" = 12 ->
  exec 18 Preader reader_stops pc_RDNUM1 ks s  =  OStop "FAIL" (number_limit s).
Proof.
  intros Hp Hd Hnd.
  have Hpos : (vars s "pos"-vars s "lim" <? 0) = true by apply Z.ltb_lt; lia.
  have Hlow : (peek s (vars s "pos") 1-48 <? 0) = false by apply Z.ltb_ge; lia.
  have Hhigh : (peek s (vars s "pos") 1-48-10 <? 0) = true by apply Z.ltb_lt; lia.
  have Hz : (vars s "nd" =? 0) = false by rewrite Hnd.
  have Hbound : (vars s "nd"-12 <? 0) = false by rewrite Hnd.
  do 18 (rinstruction; rewrite ?Hpos ?Hlow ?Hhigh ?Hz ?Hbound).
  reflexivity.
Qed.

Theorem number_step_fields s :
  vars (number_lead_step s) "num" = vars s "num" /\
  vars (number_lead_step s) "nd" = vars s "nd" /\
  vars (number_lead_step s) "nseen" = 1 /\
  vars (number_lead_step s) "pos" = vars s "pos"+1 /\
  vars (number_sig_step s) "num" = vars s "num"*10+(peek s (vars s "pos") 1-48) /\
  vars (number_sig_step s) "nd" = vars s "nd"+1 /\
  vars (number_sig_step s) "nseen" = 1 /\
  vars (number_sig_step s) "pos" = vars s "pos"+1.
Proof. repeat split; reflexivity. Qed.
Theorem number_limit_no_accumulator_update s :
  vars (number_limit s) "num" = vars s "num" /\
  vars (number_limit s) "nd" = vars s "nd" /\
  vars (number_limit s) "pos" = vars s "pos" /\
  forall a, a<hp s -> mem (number_limit s) a = mem s a.
Proof.
  unfold number_limit. repeat split; try (rewrite text_new_get; reflexivity).
  intros a Ha. rewrite text_new_mem_below; [reflexivity|exact Ha].
Qed.
Print Assumptions RDNUM_leading_zero.
Print Assumptions RDNUM_significant_digit.
Print Assumptions RDNUM_first_nonzero_digit.
Print Assumptions RDNUM_thirteenth_significant_refused.
Print Assumptions number_limit_no_accumulator_update.

Definition number_end s := setv (setv s "t" (vars s "pos"-vars s "lim")) "t" (vars s "pos"-vars s "lim").
Theorem RDNUM_end s : vars s "lim"<=vars s "pos" -> vars s "nseen"<>0 ->
  exec 12 Preader reader_stops pc_RDNUM1 [::] s = OReturn (number_end s).
Proof.
  intros Hp Hseen.
  have Hpos : (vars s "pos"-vars s "lim" <? 0) = false by apply Z.ltb_ge;lia.
  have Hcount : (vars s "nseen" =? 0) = false by apply Z.eqb_neq;exact Hseen.
  do 12 (rinstruction;rewrite ?Hpos ?Hcount). reflexivity.
Qed.
Definition number_byte_end s := setv (setv (setv s "t" (vars s "pos"-vars s "lim"))
   "c" (peek s (vars s "pos") 1)) "d" (peek s (vars s "pos") 1-48).
Theorem RDNUM_low_delimiter_prefix s ks f :
  vars s "pos"<vars s "lim" -> peek s (vars s "pos") 1<48 ->
  exec (7+f)%N Preader reader_stops pc_RDNUM1 ks s =
  exec f Preader reader_stops pc_RDNUM9 ks (number_byte_end s).
Proof.
  intros Hp Hd.
  have Hpos : (vars s "pos"-vars s "lim" <? 0) = true by apply Z.ltb_lt;lia.
  have Hlow : (peek s (vars s "pos") 1-48 <? 0) = true by apply Z.ltb_lt;lia.
  cbn [addn Nat.add]. do 7 (rinstruction;rewrite ?Hpos ?Hlow). reflexivity.
Qed.
Print Assumptions RDNUM_end.
Print Assumptions RDNUM_low_delimiter_prefix.

Definition finish_locals : list string := [:: "t";"c";"d"].
Lemma number_byte_end_frame s : reader_frame finish_locals s (number_byte_end s).
Proof. unfold number_byte_end,setv,finish_locals;rframe. Qed.
Lemma number_end_frame s : reader_frame finish_locals s (number_end s).
Proof. unfold number_end,setv,finish_locals;rframe. Qed.
Lemma frame_finish_weaken s t : reader_frame [:: "pos";"t";"c"] s t ->
  vars t "pos" = vars s "pos" -> reader_frame finish_locals s t.
Proof.
  intros [Hm [Hh Hv]] Hp. repeat split;try assumption.
  intros x Hx. destruct (String.eqb_spec x "pos") as [He|He].
  - subst x;exact Hp.
  - apply Hv. unfold finish_locals in Hx;simpl in Hx|-*. intuition.
Qed.
Theorem RDNUM_finish_success s : vars s "pos"<=vars s "lim" -> vars s "nseen"<>0 ->
  (vars s "pos" = vars s "lim" \/ whitespace (peek s (vars s "pos") 1)) ->
  exists sf, evals Preader reader_stops pc_RDNUM1 [::] s (OReturn sf) /\
    reader_frame finish_locals s sf.
Proof.
  intros Hb Hseen Hdelim.
  destruct (Z_lt_ge_dec (vars s "pos") (vars s "lim")) as [Hlt|Hge].
  - have Hw : whitespace (peek s (vars s "pos") 1) by destruct Hdelim;[lia|assumption].
    have Hlow : peek s (vars s "pos") 1<48 by unfold whitespace in Hw;lia.
    have Hpreframe := number_byte_end_frame s.
    have Hprepos : xpos (number_byte_end s) = vars s "pos" by reflexivity.
    have Hprelim : xlim (number_byte_end s) = vars s "lim" by reflexivity.
    have Hprebyte : byte_at (number_byte_end s) (xpos (number_byte_end s)) = peek s (vars s "pos") 1 by reflexivity.
    destruct (@ENDTOK_success (number_byte_end s)) as [sf [Hend [Hpos Hframe]]].
    + rewrite Hprepos Hprelim;lia.
    + right;now rewrite Hprebyte.
    + exists sf. split.
      * eapply reader_prefix with (n:=7%N).
        -- intro f;apply RDNUM_low_delimiter_prefix;assumption.
        -- have Hn : (vars (number_byte_end s) "nseen" =? 0) = false by apply Z.eqb_neq;exact Hseen.
           rs. rsw ltac:(rvars;rewrite Hn). rs.
           eapply evals_call;[exact Hend|]. rsn. reflexivity.
      * eapply reader_frame_trans;[exact Hpreframe|].
        apply frame_finish_weaken;[exact Hframe|exact Hpos].
  - exists (number_end s). split.
    + have Hle : vars s "lim"<=vars s "pos" by lia.
      have Hexec := @RDNUM_end s Hle Hseen.
      have Hnot : exec 12 Preader reader_stops pc_RDNUM1 [::] s<>OFuel by rewrite Hexec;discriminate.
      have Hrun := @evals_exec 12 Preader reader_stops pc_RDNUM1 [::] s Hnot. now rewrite Hexec in Hrun.
    + apply number_end_frame.
Qed.
Print Assumptions RDNUM_finish_success.
