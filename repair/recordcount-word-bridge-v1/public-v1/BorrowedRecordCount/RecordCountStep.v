(* Actual eight-instruction RECORDCOUNT execution in unchanged PmpCore. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From RecordCount Require Import RecordCountSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition remaining (s:state) := vars s "lim"-vars s "pos".
Definition first_sub_state s := setv s "t" (remaining s).
Definition checked_state s := setv (first_sub_state s) "t" (remaining s-vars s "num").
Definition count_diagnostic := bytes_of_str "a record count exceeds remaining input bytes".
Definition failure_state s := text_new (checked_state s) "WHY" count_diagnostic.

Ltac rcvars := repeat progress (rewrite ?setv_get;cbn [String.eqb]).
Ltac rcjump := repeat match goal with
 | |- context [jumpo ?f Precord record_stops ?pc ?lab ?ks ?s] =>
   unfold jumpo;let stop := eval vm_compute in (has (String.eqb lab) record_stops) in
   change (has (String.eqb lab) record_stops) with stop;
   cbn beta iota;try (let target := eval vm_compute in (find_label Precord lab) in
     change (find_label Precord lab) with target;cbn beta iota)
 end.
Ltac rcinstruction := lazymatch goal with
 | |- context [exec ?fuel Precord record_stops ?pc ?ks ?s] =>
   let unfolded := eval compute in fuel in lazymatch unfolded with S ?f =>
   change fuel with unfolded;
   rewrite (@exec_S f Precord record_stops pc ks s);[|vm_compute;reflexivity];
   let term := eval vm_compute in (nth (STrace true) Precord pc) in
   change (nth (STrace true) Precord pc) with term;
   cbn [run_stmt ev test];rcjump;rcvars end
 end.

Theorem RECORDCOUNT_first_subtraction_prefix s ks f :
  exec (2+f)%N Precord record_stops pc_RECORDCOUNT ks s =
  exec f Precord record_stops 2%N ks (first_sub_state s).
Proof. cbn [addn Nat.add]. do 2 rcinstruction. reflexivity. Qed.
Theorem RECORDCOUNT_subtraction_prefix s ks f :
  exec (3+f)%N Precord record_stops pc_RECORDCOUNT ks s =
  exec f Precord record_stops 3%N ks (checked_state s).
Proof. cbn [addn Nat.add]. do 3 rcinstruction. reflexivity. Qed.

Theorem RECORDCOUNT_return_fuel s : vars s "num"<=remaining s ->
  exec 5 Precord record_stops pc_RECORDCOUNT [] s=OReturn (checked_state s).
Proof.
  intros Hn. have Htest : (vars s "lim"-vars s "pos"-vars s "num" <? 0)=false
    by apply Z.ltb_ge;unfold remaining in Hn;lia.
  do 5 (rcinstruction;rewrite ?Htest). reflexivity.
Qed.
Theorem RECORDCOUNT_failure_fuel s ks : vars s "num">remaining s ->
  exec 7 Precord record_stops pc_RECORDCOUNT ks s=OStop "FAIL" (failure_state s).
Proof.
  intros Hn. have Htest : (vars s "lim"-vars s "pos"-vars s "num" <? 0)=true
    by apply Z.ltb_lt;unfold remaining in Hn;lia.
  do 7 (rcinstruction;rewrite ?Htest). reflexivity.
Qed.
Lemma RECORDCOUNT_return_evals s : vars s "num"<=remaining s ->
  evals Precord record_stops pc_RECORDCOUNT [] s (OReturn (checked_state s)).
Proof.
  intros H. have E:=@RECORDCOUNT_return_fuel s H.
  have Hnot : exec 5 Precord record_stops pc_RECORDCOUNT [] s<>OFuel by rewrite E;discriminate.
  have Hr:=@evals_exec 5 Precord record_stops pc_RECORDCOUNT [] s Hnot. now rewrite E in Hr.
Qed.
Lemma RECORDCOUNT_failure_evals s ks : vars s "num">remaining s ->
  evals Precord record_stops pc_RECORDCOUNT ks s (OStop "FAIL" (failure_state s)).
Proof.
  intros H. have E:=@RECORDCOUNT_failure_fuel s ks H.
  have Hnot : exec 7 Precord record_stops pc_RECORDCOUNT ks s<>OFuel by rewrite E;discriminate.
  have Hr:=@evals_exec 7 Precord record_stops pc_RECORDCOUNT ks s Hnot. now rewrite E in Hr.
Qed.

Theorem RECORDCOUNT_returns_iff s sf :
  evals Precord record_stops pc_RECORDCOUNT [] s (OReturn sf) <->
  vars s "num"<=remaining s /\ sf=checked_state s.
Proof.
  split.
  - intros Hr. destruct (Z_le_gt_dec (vars s "num") (remaining s)) as [Hle|Hgt].
    + have Hactual:=@RECORDCOUNT_return_evals s Hle.
      have E:=@evals_fun Precord record_stops pc_RECORDCOUNT [] s (OReturn sf) (OReturn (checked_state s)) Hr Hactual.
      inversion E;subst sf;tauto.
    + have Hactual:=@RECORDCOUNT_failure_evals s [] Hgt.
      have E:=@evals_fun Precord record_stops pc_RECORDCOUNT [] s (OReturn sf) (OStop "FAIL" (failure_state s)) Hr Hactual. discriminate.
  - intros [Hle ->];apply RECORDCOUNT_return_evals;exact Hle.
Qed.
Theorem RECORDCOUNT_fails_iff s sf :
  evals Precord record_stops pc_RECORDCOUNT [] s (OStop "FAIL" sf) <->
  vars s "num">remaining s /\ sf=failure_state s.
Proof.
  split.
  - intros Hr. destruct (Z_le_gt_dec (vars s "num") (remaining s)) as [Hle|Hgt].
    + have Hactual:=@RECORDCOUNT_return_evals s Hle.
      have E:=@evals_fun Precord record_stops pc_RECORDCOUNT [] s (OStop "FAIL" sf) (OReturn (checked_state s)) Hr Hactual. discriminate.
    + have Hactual:=@RECORDCOUNT_failure_evals s [] Hgt.
      have E:=@evals_fun Precord record_stops pc_RECORDCOUNT [] s (OStop "FAIL" sf) (OStop "FAIL" (failure_state s)) Hr Hactual.
      inversion E;subst sf;tauto.
  - intros [Hgt ->];apply RECORDCOUNT_failure_evals;exact Hgt.
Qed.
Print Assumptions RECORDCOUNT_return_fuel.
Print Assumptions RECORDCOUNT_failure_fuel.
Print Assumptions RECORDCOUNT_returns_iff.
Print Assumptions RECORDCOUNT_fails_iff.
