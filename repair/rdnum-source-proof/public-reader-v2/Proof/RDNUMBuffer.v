(* Complete finite readable-buffer correspondence to a pure decimal lexer. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From RDNUM Require Import RDNUMSource RDNUMReaders RDNUMPolicy RDNUMEntry RDNUMRefusal RDNUMComplete RDNUMLexical.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition suffix_good (raw:list Z) := match raw with []=>true | b::_=>whiteb b end.
Definition parse_buffer (raw:list Z) : option (Z*nat*list Z) :=
  let '(nw,after):=split_white raw in
  let '(ds,rest):=split_decimal after in
  if suffix_good rest then
    match M.parse_decimal ds with
    | Some v=>Some (v,(nw+List.length ds)%N,rest)
    | None=>None end
  else None.
Lemma buffer_segment_memory s t p raw : mem s=mem t -> buffer_segment s p raw -> buffer_segment t p raw.
Proof.
  intros Hmem. induction raw in p |- *;cbn [buffer_segment];[tauto|].
  intros [Hb Htail]. split;[unfold peek in *;cbn in *;now rewrite -Hmem|apply IHraw;exact Htail].
Qed.
Lemma suffix_good_delimiter s (raw:list Z) nw ds rest :
  vars s "lim"=vars s "pos"+Z.of_nat (List.length raw) ->
  buffer_segment s (vars s "pos"+Z.of_nat nw+Z.of_nat (List.length ds)) rest ->
  (nw+List.length ds+List.length rest=List.length raw)%coq_nat ->
  (suffix_good rest=true <-> entry_delimiter s nw ds).
Proof.
  intros Hlim Hbuf Hlen. unfold entry_delimiter.
  destruct rest as [|b rest].
  - cbn [suffix_good List.length] in Hlen|-*. rewrite Hlim -Hlen Nat2Z.inj_add. split;[intros _;left;lia|intros _;reflexivity].
  - cbn [suffix_good buffer_segment] in Hbuf|-*. rewrite whiteb_true.
    destruct Hbuf as [Hb _]. rewrite Hb. split;[tauto|]. intros [Heq|Hw];[|exact Hw].
    rewrite Hlim -Hlen !Nat2Z.inj_add List.length_cons Nat2Z.inj_succ in Heq. lia.
Qed.

Theorem RDNUM_buffer_parse_success s raw value consumed rest :
  buffer_segment s (vars s "pos") raw -> vars s "lim"=vars s "pos"+Z.of_nat (List.length raw) ->
  parse_buffer raw=Some (value,consumed,rest) ->
  exists sf, evals Preader reader_stops pc_RDNUM [] s (OReturn sf) /\
    vars sf "num"=value /\ vars sf "pos"=vars s "pos"+Z.of_nat consumed /\
    buffer_segment sf (vars sf "pos") rest /\ mem sf=mem s /\ hp sf=hp s /\
    0<=value<=999999999999 /\ value<9223372036854775808 /\
    (consumed+List.length rest=List.length raw)%coq_nat.
Proof.
  intros Hbuf Hlim Hparse. unfold parse_buffer in Hparse.
  destruct (split_white raw) as [nw after] eqn:Hw.
  destruct (split_decimal after) as [ds tail] eqn:Hd.
  destruct (suffix_good tail) eqn:Hg;[|discriminate].
  destruct (M.parse_decimal ds) as [v|] eqn:Hdecimal;[|discriminate].
  inversion Hparse;subst value consumed rest.
  destruct (@lexical_entry_view s raw nw after ds tail Hbuf Hlim Hw Hd) as [Hview [Htail Hlen]].
  have Hdelim := proj1 (@suffix_good_delimiter s raw nw ds tail Hlim Htail Hlen) Hg.
  have Hcopy := Hview. destruct Hcopy as [Hwhite [Hws [Hdigits [Hsegment [Hb Hmax]]]]].
  destruct (@RDNUM_entry_decimal_success s nw ds v Hwhite Hdigits Hsegment Hb Hdelim Hdecimal)
    as [sf [Hrun [Hnum [Hpos [Hmem [Hhp Hrange]]]]]].
  exists sf. split;[exact Hrun|]. split;[exact Hnum|]. split.
  - rewrite Hpos Nat2Z.inj_add;lia.
  - split.
    + rewrite Hpos. apply (@buffer_segment_memory s sf _ tail);[symmetry;exact Hmem|exact Htail].
    + split;[exact Hmem|]. split;[exact Hhp|]. destruct Hrange as [Ha Hbval].
      split;[exact Ha|]. split;[exact Hbval|exact Hlen].
Qed.

Theorem RDNUM_buffer_parse_failure s raw :
  buffer_segment s (vars s "pos") raw -> vars s "lim"=vars s "pos"+Z.of_nat (List.length raw) ->
  parse_buffer raw=None ->
  exists sf, evals Preader reader_stops pc_RDNUM [] s (OStop "FAIL" sf) /\ readonly_old s sf.
Proof.
  intros Hbuf Hlim Hparse. unfold parse_buffer in Hparse.
  destruct (split_white raw) as [nw after] eqn:Hw.
  destruct (split_decimal after) as [ds rest] eqn:Hd.
  destruct (@lexical_entry_view s raw nw after ds rest Hbuf Hlim Hw Hd) as [Hview [Hrest Hlen]].
  have Hdelim := @suffix_good_delimiter s raw nw ds rest Hlim Hrest Hlen.
  apply (@RDNUM_entry_policy_refusal s nw ds Hview).
  destruct (suffix_good rest) eqn:Hg.
  - left. destruct (M.parse_decimal ds);[discriminate|reflexivity].
  - right. intro Hwhite. have HT := proj2 Hdelim Hwhite. congruence.
Qed.

Theorem RDNUM_buffer_returns_iff s raw :
  buffer_segment s (vars s "pos") raw -> vars s "lim"=vars s "pos"+Z.of_nat (List.length raw) ->
  ((exists value consumed rest,parse_buffer raw=Some (value,consumed,rest)) <->
   exists sf,evals Preader reader_stops pc_RDNUM [] s (OReturn sf)).
Proof.
  intros Hbuf Hlim. split.
  - intros [v [n [rest Hparse]]]. destruct (@RDNUM_buffer_parse_success s raw v n rest Hbuf Hlim Hparse) as [sf [Hr _]].
    exists sf;exact Hr.
  - intros [sf Hr]. destruct (parse_buffer raw) as [[[v n] rest]|] eqn:Hparse.
    + exists v,n,rest;reflexivity.
    + destruct (@RDNUM_buffer_parse_failure s raw Hbuf Hlim Hparse) as [sg [Hs _]].
      have E := @evals_fun Preader reader_stops pc_RDNUM [] s (OReturn sf) (OStop "FAIL" sg) Hr Hs. discriminate.
Qed.

Theorem RDNUM_buffer_stops_iff s raw :
  buffer_segment s (vars s "pos") raw -> vars s "lim"=vars s "pos"+Z.of_nat (List.length raw) ->
  (parse_buffer raw=None <-> exists sf,evals Preader reader_stops pc_RDNUM [] s (OStop "FAIL" sf)).
Proof.
  intros Hbuf Hlim. split.
  - intro Hparse. destruct (@RDNUM_buffer_parse_failure s raw Hbuf Hlim Hparse) as [sf [Hrun _]]. exists sf;exact Hrun.
  - intros [sf Hstop]. destruct (parse_buffer raw) as [[[v n] rest]|] eqn:Hparse;[|reflexivity].
    destruct (@RDNUM_buffer_parse_success s raw v n rest Hbuf Hlim Hparse) as [sg [Hreturn _]].
    have E := @evals_fun Preader reader_stops pc_RDNUM [] s (OStop "FAIL" sf) (OReturn sg) Hstop Hreturn. discriminate.
Qed.
Print Assumptions RDNUM_buffer_parse_success.
Print Assumptions RDNUM_buffer_parse_failure.
Print Assumptions RDNUM_buffer_returns_iff.
Print Assumptions RDNUM_buffer_stops_iff.
