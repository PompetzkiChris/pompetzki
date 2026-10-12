(* Full source entry, including its SKIPWS call and counter reset. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From NumericV5 Require DecimalSignificantV4.
From RDNUM Require Import RDNUMSource RDNUMTools RDNUMCalls RDNUMReaders RDNUMNumber RDNUMPolicy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition number_reset (s:state) : state :=
  setv (setv (setv s "num" 0) "nd" 0) "nseen" 0.

Lemma RDNUM_reset_prefix s ks f :
  exec (3+f)%N Preader reader_stops (pc_RDNUM+2)%N ks s =
  exec f Preader reader_stops pc_RDNUM1 ks (number_reset s).
Proof. cbn [addn Nat.add]. do 3 rinstruction. reflexivity. Qed.

Lemma RDNUM_entry_call s sw r :
  evals Preader reader_stops pc_SKIPWS [] s (OReturn sw) ->
  evals Preader reader_stops pc_RDNUM1 [] (number_reset sw) r ->
  evals Preader reader_stops pc_RDNUM [] s r.
Proof.
  intros Hskip Hrun. rs. rs. eapply evals_call;[exact Hskip|].
  eapply reader_prefix with (n:=3%N);[intro f;apply RDNUM_reset_prefix|exact Hrun].
Qed.

Theorem RDNUM_entry_decimal_success s nw ds value :
  white_prefix s nw ->
  Forall (fun d=>0<=d<10) ds ->
  digit_segment s (vars s "pos"+Z.of_nat nw) ds ->
  vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)<=vars s "lim" ->
  (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)=vars s "lim" \/
   whitespace (peek s (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)) 1)) ->
  M.parse_decimal ds = Some value ->
  exists sf, evals Preader reader_stops pc_RDNUM [] s (OReturn sf) /\
    vars sf "num" = value /\
    vars sf "pos" = vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds) /\
    mem sf = mem s /\ hp sf = hp s /\
    0<=value<=999999999999 /\ value<9223372036854775808.
Proof.
  intros Hwhite Hdigits Hsegment Hb Hdelim Hparse.
  have Hne : ds<>[] by intro He;subst ds;discriminate.
  have Hwsend : ~whitespace (byte_at s (vars s "pos"+Z.of_nat nw)).
  { destruct ds as [|d ds];[contradiction|].
    apply Forall_cons_iff in Hdigits. destruct Hdigits as [Hd _].
    cbn [digit_segment] in Hsegment. destruct Hsegment as [Hbyte _].
    unfold byte_at,whitespace. rewrite Hbyte. lia. }
  have Hbwhite : xpos s+Z.of_nat nw<=xlim s by unfold xpos,xlim;lia.
  destruct (@SKIPWS_success s nw Hbwhite Hwhite (or_intror Hwsend)) as [sw [Hskip [Hp Hframe]]].
  have Hlim : vars sw "lim"=vars s "lim" by exact (@reader_frame_lim s sw Hframe).
  have Hmemory : mem s=mem (number_reset sw).
  { destruct Hframe as [Hm _]. unfold number_reset,setv;cbn;congruence. }
  have Hresetpos : vars (number_reset sw) "pos"=vars s "pos"+Z.of_nat nw by exact Hp.
  have Hresetlim : vars (number_reset sw) "lim"=vars s "lim" by exact Hlim.
  have Hresetdigits : digit_segment (number_reset sw) (vars (number_reset sw) "pos") ds.
  { rewrite Hresetpos. apply (@digit_segment_memory s (number_reset sw) _ ds Hmemory Hsegment). }
  have Hresetbound : vars (number_reset sw) "pos"+Z.of_nat (List.length ds)<=vars (number_reset sw) "lim".
  { now rewrite Hresetpos Hresetlim. }
  have Hresetend : vars (number_reset sw) "pos"+Z.of_nat (List.length ds)=vars (number_reset sw) "lim" \/
      whitespace (peek (number_reset sw) (vars (number_reset sw) "pos"+Z.of_nat (List.length ds)) 1).
  { rewrite Hresetpos Hresetlim. unfold peek;cbn. unfold peek in Hdelim;cbn in Hdelim.
    now rewrite -Hmemory. }
  have Hresetnum : vars (number_reset sw) "num" = 0 by reflexivity.
  have Hresetnd : vars (number_reset sw) "nd" = 0 by reflexivity.
  destruct (@RDNUM_source_refines_decimal ds (number_reset sw) value Hdigits Hresetdigits
      Hresetnum Hresetnd Hresetbound Hresetend Hparse) as [sf [Hrun [Hnum [Hpos [Hm [Hhp Hrange]]]]]].
  exists sf. split;[eapply RDNUM_entry_call;[exact Hskip|exact Hrun]|].
  split;[exact Hnum|]. split;[now rewrite Hpos Hresetpos|].
  split;[congruence|]. split.
  - destruct Hframe as [_ [Hh _]]. unfold number_reset,setv in Hhp;cbn in Hhp;congruence.
  - exact Hrange.
Qed.
Print Assumptions RDNUM_entry_decimal_success.
