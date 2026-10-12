(* Declarative decimal policy versus the actual entry and refusal paths. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From RDNUM Require Import RDNUMSource RDNUMTools RDNUMCalls RDNUMReaders RDNUMNumber
  RDNUMPolicy RDNUMEntry RDNUMRefusal RDNUMDelimiter.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Theorem RDNUM_loop_policy_refusal ds s :
  Forall (fun d=>0<=d<10) ds -> digit_segment s (vars s "pos") ds ->
  vars s "num" = 0 -> vars s "nd" = 0 -> vars s "nseen" = 0 ->
  vars s "pos"+Z.of_nat (List.length ds)<=vars s "lim" ->
  (vars s "pos"+Z.of_nat (List.length ds)=vars s "lim" \/
   ~(48<=peek s (vars s "pos"+Z.of_nat (List.length ds)) 1<58)) ->
  (M.parse_decimal ds=None \/
   (vars s "pos"+Z.of_nat (List.length ds)<vars s "lim" /\
    ~whitespace (peek s (vars s "pos"+Z.of_nat (List.length ds)) 1))) ->
  exists sf, evals Preader reader_stops pc_RDNUM1 [] s (OStop "FAIL" sf) /\ readonly_old s sf.
Proof.
  intros Hd Hseg Hnum Hnd Hseen Hb Hmax Hfail.
  destruct (M.parse_decimal ds) as [value|] eqn:Hparse.
  - have Hbad : vars s "pos"+Z.of_nat (List.length ds)<vars s "lim" /\
      ~whitespace (peek s (vars s "pos"+Z.of_nat (List.length ds)) 1).
    { destruct Hfail as [Hnone|Hbad];[discriminate|exact Hbad]. }
    have Hne : ds<>[] by intro He;subst ds;discriminate.
    have Hdigits : M.parse_digits ds 0 0=Some value by destruct ds;[contradiction|exact Hparse].
    have Hmap := @scan_state_decimal_correspondence ds s 0 0 Hd Hseg Hnum Hnd.
    rewrite Hdigits in Hmap.
    destruct (scan_state ds s) as [sd|] eqn:Hscan;[|discriminate].
    have Hnb : 0<=vars s "nd"<=12 by rewrite Hnd;lia.
    destruct (@scan_state_success_properties ds s sd Hnb Hscan) as [Hframe [Hp [Hns Hsaw]]].
    have Hlim : vars sd "lim"=vars s "lim".
    { apply (@reader_frame_var number_locals s sd "lim" Hframe). unfold number_locals;simpl;intuition discriminate. }
    have Hmem : peek sd (vars sd "pos") 1=peek s (vars s "pos"+Z.of_nat (List.length ds)) 1.
    { rewrite Hp;exact (@reader_frame_byte number_locals s sd _ Hframe). }
    have Hpbound : vars sd "pos"<vars sd "lim" by rewrite Hp Hlim;exact (proj1 Hbad).
    have Hsaw' : vars sd "nseen"<>0 by destruct ds;[contradiction|rewrite Hsaw;lia].
    have Hnondigit : ~(48<=peek sd (vars sd "pos") 1<58).
    { rewrite Hmem. destruct Hmax;[lia|assumption]. }
    have Hnonwhite : ~whitespace (peek sd (vars sd "pos") 1) by rewrite Hmem;exact (proj2 Hbad).
    destruct (@RDNUM_bad_delimiter_refused sd Hpbound Hsaw' Hnondigit Hnonwhite) as [sf [Hstop Hreadonly]].
    exists sf. split.
    + apply (@RDNUM_source_sequence ds s sd [] (OStop "FAIL" sf));assumption.
    + eapply readonly_frame_trans;[exact Hframe|exact Hreadonly].
  - destruct ds as [|d ds].
    + cbn [List.length] in Hb,Hmax. rewrite Z.add_0_r in Hb,Hmax.
      apply RDNUM_empty_refused;assumption.
    + have Hdigits : M.parse_digits (d::ds) 0 0=None by exact Hparse.
      have Hmap := @scan_state_decimal_correspondence (d::ds) s 0 0 Hd Hseg Hnum Hnd.
      rewrite Hdigits in Hmap.
      have Hnone : scan_state (d::ds) s=None.
      { destruct (scan_state (d::ds) s);[discriminate|reflexivity]. }
      have Hnb : 0<=vars s "nd"<=12 by rewrite Hnd;lia.
      exact (@RDNUM_source_sequence_refusal (d::ds) s [] Hd Hseg Hnb Hb Hnone).
Qed.

Definition entry_view (s:state) (nw:nat) (ds:list Z) : Prop :=
  white_prefix s nw /\
  (vars s "pos"+Z.of_nat nw=vars s "lim" \/
   ~whitespace (peek s (vars s "pos"+Z.of_nat nw) 1)) /\
  Forall (fun d=>0<=d<10) ds /\ digit_segment s (vars s "pos"+Z.of_nat nw) ds /\
  vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)<=vars s "lim" /\
  (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)=vars s "lim" \/
   ~(48<=peek s (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)) 1<58)).
Definition entry_delimiter (s:state) (nw:nat) (ds:list Z) : Prop :=
  vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)=vars s "lim" \/
  whitespace (peek s (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)) 1).
Lemma whitespace_dec b : {whitespace b}+{~whitespace b}.
Proof.
  unfold whitespace.
  destruct (Z.eq_dec b 32);[left;tauto|].
  destruct (Z.eq_dec b 10);[left;tauto|].
  destruct (Z.eq_dec b 13);[left;tauto|].
  destruct (Z.eq_dec b 9);[left;tauto|]. right;tauto.
Qed.
Lemma entry_delimiter_dec s nw ds : {entry_delimiter s nw ds}+{~entry_delimiter s nw ds}.
Proof.
  unfold entry_delimiter.
  destruct (Z.eq_dec (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)) (vars s "lim"));[left;tauto|].
  destruct (whitespace_dec (peek s (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)) 1));[left|right];tauto.
Qed.

Theorem RDNUM_entry_policy_refusal s nw ds : entry_view s nw ds ->
  (M.parse_decimal ds=None \/ ~entry_delimiter s nw ds) ->
  exists sf, evals Preader reader_stops pc_RDNUM [] s (OStop "FAIL" sf) /\ readonly_old s sf.
Proof.
  intros [Hw [Hws [Hd [Hseg [Hb Hmax]]]]] Hfail.
  have Hwb : xpos s+Z.of_nat nw<=xlim s by unfold xpos,xlim;lia.
  destruct (@SKIPWS_success s nw Hwb Hw Hws) as [sw [Hskip [Hp Hframe]]].
  have Hlim : vars sw "lim"=vars s "lim" by exact (@reader_frame_lim s sw Hframe).
  have Hmem : mem s=mem (number_reset sw) by destruct Hframe as [Hm _];unfold number_reset,setv;cbn;congruence.
  have Hpos : vars (number_reset sw) "pos"=vars s "pos"+Z.of_nat nw by exact Hp.
  have Hlim' : vars (number_reset sw) "lim"=vars s "lim" by exact Hlim.
  have Hseg' : digit_segment (number_reset sw) (vars (number_reset sw) "pos") ds.
  { rewrite Hpos;exact (@digit_segment_memory s (number_reset sw) _ ds Hmem Hseg). }
  have Hb' : vars (number_reset sw) "pos"+Z.of_nat (List.length ds)<=vars (number_reset sw) "lim" by now rewrite Hpos Hlim'.
  have Hmax' : vars (number_reset sw) "pos"+Z.of_nat (List.length ds)=vars (number_reset sw) "lim" \/
      ~(48<=peek (number_reset sw) (vars (number_reset sw) "pos"+Z.of_nat (List.length ds)) 1<58).
  { rewrite Hpos Hlim'. unfold peek in Hmax|-*;cbn in Hmax|-*;now rewrite -Hmem. }
  have Hfail' : M.parse_decimal ds=None \/
    (vars (number_reset sw) "pos"+Z.of_nat (List.length ds)<vars (number_reset sw) "lim" /\
     ~whitespace (peek (number_reset sw) (vars (number_reset sw) "pos"+Z.of_nat (List.length ds)) 1)).
  { destruct Hfail as [Hnone|Hbad];[left;exact Hnone|]. right.
    unfold entry_delimiter in Hbad. rewrite Hpos Hlim'.
    unfold peek in Hbad|-*;cbn in Hbad|-*;rewrite -Hmem. split;[lia|tauto]. }
  have Hnum : vars (number_reset sw) "num" = 0 by reflexivity.
  have Hnd : vars (number_reset sw) "nd" = 0 by reflexivity.
  have Hseen : vars (number_reset sw) "nseen" = 0 by reflexivity.
  destruct (@RDNUM_loop_policy_refusal ds (number_reset sw) Hd Hseg' Hnum Hnd Hseen Hb' Hmax' Hfail') as [sf [Hstop Hreadonly]].
  exists sf. split;[eapply RDNUM_entry_call;[exact Hskip|exact Hstop]|].
  destruct Hframe as [Hmemory [Hheap _]]. destruct Hreadonly as [Hhp Hread].
  split.
  - unfold number_reset,setv in Hhp;cbn in Hhp;congruence.
  - intros a Ha. rewrite Hmem. apply Hread. unfold number_reset,setv;cbn;congruence.
Qed.

Theorem RDNUM_entry_policy_iff s nw ds value : entry_view s nw ds ->
  (M.parse_decimal ds=Some value /\ entry_delimiter s nw ds <->
   exists sf, evals Preader reader_stops pc_RDNUM [] s (OReturn sf) /\
    vars sf "num"=value /\
    vars sf "pos"=vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds) /\
    mem sf=mem s /\ hp sf=hp s /\ 0<=value<=999999999999 /\ value<9223372036854775808).
Proof.
  intros Hview. split.
  - intros [Hparse Hdelim]. destruct Hview as [Hw [Hws [Hd [Hseg [Hb Hmax]]]]].
    exact (@RDNUM_entry_decimal_success s nw ds value Hw Hd Hseg Hb Hdelim Hparse).
  - intros [sf [Hrun [Hnum Hrest]]].
    destruct (M.parse_decimal ds) as [v|] eqn:Hparse.
    + destruct (entry_delimiter_dec s nw ds) as [Hdelim|Hbad].
      * have Hcopy := Hview. destruct Hcopy as [Hw [Hws [Hd [Hseg [Hb Hmax]]]]].
        destruct (@RDNUM_entry_decimal_success s nw ds v Hw Hd Hseg Hb Hdelim Hparse) as [sg [Hrun' [Hnum' Hrest']]].
        have Heq := @evals_fun Preader reader_stops pc_RDNUM [] s (OReturn sf) (OReturn sg) Hrun Hrun'.
        inversion Heq;subst sg. split;[f_equal;congruence|exact Hdelim].
      * destruct (@RDNUM_entry_policy_refusal s nw ds Hview (or_intror Hbad)) as [sg [Hstop _]].
        have Heq := @evals_fun Preader reader_stops pc_RDNUM [] s (OReturn sf) (OStop "FAIL" sg) Hrun Hstop. discriminate.
    + destruct (@RDNUM_entry_policy_refusal s nw ds Hview (or_introl Hparse)) as [sg [Hstop _]].
      have Heq := @evals_fun Preader reader_stops pc_RDNUM [] s (OReturn sf) (OStop "FAIL" sg) Hrun Hstop. discriminate.
Qed.
Print Assumptions RDNUM_loop_policy_refusal.
Print Assumptions RDNUM_entry_policy_refusal.
Print Assumptions RDNUM_entry_policy_iff.
