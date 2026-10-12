(* Empty tokens and non-digit terminators, from current source instructions. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono RunKit.
From RDNUM Require Import RDNUMSource RDNUMTools RDNUMCalls RDNUMStops RDNUMReaders RDNUMNumber RDNUMRefusal.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition number_high_end s := setv (number_byte_end s) "t" (peek s (vars s "pos") 1-48-10).
Definition number_nondigit_end s := if (peek s (vars s "pos") 1 <? 48)
  then number_byte_end s else number_high_end s.
Definition number_expected s := text_new s "WHY" (bytes_of_str "a number was expected").

Lemma RDNUM_high_delimiter_prefix s ks f :
  vars s "pos"<vars s "lim" -> 58<=peek s (vars s "pos") 1 ->
  exec (10+f)%N Preader reader_stops pc_RDNUM1 ks s =
  exec f Preader reader_stops pc_RDNUM9 ks (number_high_end s).
Proof.
  intros Hp Hd.
  have Hpos : (vars s "pos"-vars s "lim" <? 0) = true by apply Z.ltb_lt;lia.
  have Hlow : (peek s (vars s "pos") 1-48 <? 0) = false by apply Z.ltb_ge;lia.
  have Hhigh : (peek s (vars s "pos") 1-48-10 <? 0) = false by apply Z.ltb_ge;lia.
  cbn [addn Nat.add]. do 10 (rinstruction;rewrite ?Hpos ?Hlow ?Hhigh). reflexivity.
Qed.
Lemma number_nondigit_frame s : reader_frame finish_locals s (number_nondigit_end s).
Proof.
  unfold number_nondigit_end. destruct (peek s (vars s "pos") 1 <? 48).
  - apply number_byte_end_frame.
  - unfold number_high_end,number_byte_end,setv,finish_locals;rframe.
Qed.
Lemma RDNUM_nondigit_prefix s ks r :
  vars s "pos"<vars s "lim" -> ~(48<=peek s (vars s "pos") 1<58) ->
  evals Preader reader_stops pc_RDNUM9 ks (number_nondigit_end s) r ->
  evals Preader reader_stops pc_RDNUM1 ks s r.
Proof.
  intros Hp Hd Hr. unfold number_nondigit_end in Hr.
  destruct (peek s (vars s "pos") 1 <? 48) eqn:Hlo.
  - apply Z.ltb_lt in Hlo. eapply reader_prefix with (n:=7%N);[|exact Hr].
    intro f;apply RDNUM_low_delimiter_prefix;assumption.
  - apply Z.ltb_ge in Hlo. eapply reader_prefix with (n:=10%N);[|exact Hr].
    intro f;apply RDNUM_high_delimiter_prefix;[exact Hp|lia].
Qed.
Lemma RDNUM9_empty s ks : vars s "nseen" = 0 ->
  evals Preader reader_stops pc_RDNUM9 ks s (OStop "FAIL" (number_expected s)).
Proof.
  intros Hseen. have Hzero : (vars s "nseen" =? 0) = true by rewrite Hseen.
  rs. rsw ltac:(rvars;rewrite Hzero). rs. rs. rsn. reflexivity.
Qed.
Lemma expected_readonly s : readonly_old s (number_expected s).
Proof.
  split.
  - unfold number_expected. rewrite text_new_hpE.
    have Hsize := Nat2Z.is_nonneg (size (bytes_of_str "a number was expected")). lia.
  - intros a Ha;unfold number_expected;apply text_new_mem_below;exact Ha.
Qed.

Theorem RDNUM_empty_refused s : vars s "pos"<=vars s "lim" -> vars s "nseen" = 0 ->
  (vars s "pos"=vars s "lim" \/ ~(48<=peek s (vars s "pos") 1<58)) ->
  exists sf, evals Preader reader_stops pc_RDNUM1 [] s (OStop "FAIL" sf) /\ readonly_old s sf.
Proof.
  intros Hb Hseen He. destruct (Z_lt_ge_dec (vars s "pos") (vars s "lim")) as [Hlt|Hge].
  - have Hnot : ~(48<=peek s (vars s "pos") 1<58) by destruct He;[lia|assumption].
    have Hpre := number_nondigit_frame s.
    have Hnseen : vars (number_nondigit_end s) "nseen" = 0.
    { rewrite (@reader_frame_var finish_locals s (number_nondigit_end s) "nseen" Hpre);[exact Hseen|].
      unfold finish_locals;simpl;intuition discriminate. }
    exists (number_expected (number_nondigit_end s)). split.
    + apply RDNUM_nondigit_prefix;[exact Hlt|exact Hnot|apply RDNUM9_empty;exact Hnseen].
    + eapply readonly_frame_trans;[exact Hpre|apply expected_readonly].
  - exists (number_expected (sw_limit s)). split.
    + have Hpos : (vars s "pos"-vars s "lim" <? 0) = false by apply Z.ltb_ge;lia.
      rs. rs. rsw ltac:(rvars;rewrite Hpos). rs.
      apply RDNUM9_empty;exact Hseen.
    + unfold sw_limit;split.
      * unfold number_expected;rewrite text_new_hpE setv_hp.
        have Hsize := Nat2Z.is_nonneg (size (bytes_of_str "a number was expected")). lia.
      * intros a Ha. unfold number_expected;rewrite text_new_mem_below;[reflexivity|exact Ha].
Qed.

Lemma token_failure_readonly s : readonly_old s (token_failure s).
Proof.
  split.
  - unfold token_failure,sw9,sw13,sw10,sw32,sw_byte,sw_limit.
    rewrite text_new_hpE !setv_hp.
    have Hsize := Nat2Z.is_nonneg (size (bytes_of_str "a token does not end in white space")). lia.
  - intros a Ha. unfold token_failure;rewrite text_new_mem_below;[reflexivity|exact Ha].
Qed.

Theorem RDNUM_bad_delimiter_refused s : vars s "pos"<vars s "lim" -> vars s "nseen"<>0 ->
  ~(48<=peek s (vars s "pos") 1<58) -> ~whitespace (peek s (vars s "pos") 1) ->
  exists sf, evals Preader reader_stops pc_RDNUM1 [] s (OStop "FAIL" sf) /\ readonly_old s sf.
Proof.
  intros Hp Hseen Hd Hw. have Hpre := number_nondigit_frame s.
  have Hprepos : vars (number_nondigit_end s) "pos" = vars s "pos".
  { apply (@reader_frame_var finish_locals s (number_nondigit_end s) "pos" Hpre). unfold finish_locals;simpl;intuition discriminate. }
  have Hprelim : vars (number_nondigit_end s) "lim" = vars s "lim".
  { apply (@reader_frame_var finish_locals s (number_nondigit_end s) "lim" Hpre). unfold finish_locals;simpl;intuition discriminate. }
  have Hpreseen : vars (number_nondigit_end s) "nseen"<>0.
  { rewrite (@reader_frame_var finish_locals s (number_nondigit_end s) "nseen" Hpre);[exact Hseen|]. unfold finish_locals;simpl;intuition discriminate. }
  have Hprebyte := @reader_frame_byte finish_locals s (number_nondigit_end s) (vars s "pos") Hpre.
  have Hend := @ENDTOK_failure (number_nondigit_end s).
  have Hendbound : xpos (number_nondigit_end s)<xlim (number_nondigit_end s).
  { unfold xpos,xlim;now rewrite Hprepos Hprelim. }
  have Hendwhite : ~whitespace (byte_at (number_nondigit_end s) (xpos (number_nondigit_end s))).
  { unfold xpos;rewrite Hprepos Hprebyte;exact Hw. }
  specialize (Hend Hendbound Hendwhite).
  exists (token_failure (number_nondigit_end s)). split.
  - apply RDNUM_nondigit_prefix;[exact Hp|exact Hd|].
    have Hzero : (vars (number_nondigit_end s) "nseen" =? 0) = false by apply Z.eqb_neq;exact Hpreseen.
    rs. rsw ltac:(rvars;rewrite Hzero). rs.
    apply (@evals_stop_extension Preader reader_stops pc_ENDTOK [] (number_nondigit_end s) "FAIL" _ [_]);exact Hend.
  - eapply readonly_frame_trans;[exact Hpre|apply token_failure_readonly].
Qed.
Print Assumptions RDNUM_empty_refused.
Print Assumptions RDNUM_bad_delimiter_refused.
