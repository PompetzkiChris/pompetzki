(* Exact register, diagnostic, allocation and byte-memory effects. *)
From Stdlib Require Import List String ZArith Lia Init.Byte.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From RecordCount Require Import RecordCountSource RecordCountStep.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Lemma count_diagnostic_length : size count_diagnostic = 44%N.
Proof. vm_compute;reflexivity. Qed.
Theorem checked_state_effects s :
  vars (checked_state s) "t"=remaining s-vars s "num" /\
  mem (checked_state s)=mem s /\ hp (checked_state s)=hp s /\
  forall x,x<>"t"->vars (checked_state s) x=vars s x.
Proof.
  unfold checked_state,first_sub_state. repeat split;try reflexivity.
  intros x Hx. have Heq : String.eqb x "t"=false by apply String.eqb_neq;exact Hx.
  rewrite !setv_get Heq;reflexivity.
Qed.
Theorem failure_state_registers s :
  vars (failure_state s) "t"=remaining s-vars s "num" /\
  vars (failure_state s) "WHY"=hp s /\
  vars (failure_state s) "WHY_len" = 44 /\
  hp (failure_state s)=hp s+45 /\
  forall x,x<>"t"->x<>"WHY"->x<>"WHY_len"->vars (failure_state s) x=vars s x.
Proof.
  unfold failure_state.
  split;[rewrite text_new_get;reflexivity|].
  split;[rewrite text_new_get;reflexivity|].
  split.
  - rewrite text_new_get. change (Z.of_nat (size count_diagnostic) = 44).
    rewrite count_diagnostic_length;reflexivity.
  - split.
    + rewrite text_new_hpE count_diagnostic_length;change (hp s+44+1=hp s+45);lia.
    + intros x Ht Hw Hl. rewrite text_new_get.
      have El : String.eqb x (lenv "WHY")=false by apply String.eqb_neq;exact Hl.
      have Ew : String.eqb x "WHY"=false by apply String.eqb_neq;exact Hw.
      rewrite El Ew. apply (proj2 (proj2 (proj2 (checked_state_effects s))));exact Ht.
Qed.

Lemma write_bytes_index st a bs i : (i<size bs)%coq_nat ->
  mem (write_bytes st a bs) (a+Z.of_nat i)=nth x00 bs i.
Proof.
  induction bs as [|b bs IH] in st,a,i |- *;[cbn [size];lia|].
  intros Hi;destruct i as [|i].
  - cbn [write_bytes nth Z.of_nat]. rewrite Z.add_0_r.
    rewrite (@write_bytes_outside (setm st a b) (a+1) bs a);[|left;lia].
    unfold setm;cbn;rewrite Z.eqb_refl;reflexivity.
  - cbn [write_bytes nth]. rewrite Nat2Z.inj_succ.
    replace (a+Z.succ (Z.of_nat i)) with (a+1+Z.of_nat i) by lia.
    apply IH. cbn [size] in Hi;lia.
Qed.
Lemma text_new_memory_outside st x bs a :
  a<hp st \/ hp st+Z.of_nat (size bs)+1<=a -> mem (text_new st x bs) a=mem st a.
Proof.
  intros H. change (mem (write_bytes st (hp st) (rcons bs x00)) a=mem st a).
  rewrite write_bytes_outside;[reflexivity|]. rewrite size_rcons Nat2Z.inj_succ;lia.
Qed.
Lemma text_new_memory_index st x bs i : (i<S (size bs))%coq_nat ->
  mem (text_new st x bs) (hp st+Z.of_nat i)=nth x00 (rcons bs x00) i.
Proof.
  intros Hi. change (mem (write_bytes st (hp st) (rcons bs x00)) (hp st+Z.of_nat i)=nth x00 (rcons bs x00) i).
  apply write_bytes_index. rewrite size_rcons;exact Hi.
Qed.
Theorem failure_state_memory_outside s a : a<hp s \/ hp s+45<=a ->
  mem (failure_state s) a=mem s a.
Proof.
  intros H. unfold failure_state. rewrite text_new_memory_outside;[reflexivity|].
  rewrite count_diagnostic_length. change (a<hp s \/ hp s+44+1<=a);lia.
Qed.
Theorem failure_state_memory_content s i : (i<45)%coq_nat ->
  mem (failure_state s) (hp s+Z.of_nat i)=nth x00 (rcons count_diagnostic x00) i.
Proof.
  intros Hi. unfold failure_state.
  change (mem (text_new (checked_state s) "WHY" count_diagnostic) (hp (checked_state s)+Z.of_nat i)=nth x00 (rcons count_diagnostic x00) i).
  apply text_new_memory_index. rewrite count_diagnostic_length;exact Hi.
Qed.
Theorem failure_state_nul s : mem (failure_state s) (hp s+44)=x00.
Proof.
  change (mem (failure_state s) (hp s+Z.of_nat 44)=x00).
  rewrite (@failure_state_memory_content s 44);[|lia]. vm_compute;reflexivity.
Qed.

Theorem RECORDCOUNT_return_effects s sf :
  evals Precord record_stops pc_RECORDCOUNT [] s (OReturn sf) ->
  vars s "num"<=remaining s /\ vars sf "t"=remaining s-vars s "num" /\
  mem sf=mem s /\ hp sf=hp s /\ forall x,x<>"t"->vars sf x=vars s x.
Proof.
  intros Hr. apply RECORDCOUNT_returns_iff in Hr. destruct Hr as [Hle ->].
  split;[exact Hle|apply checked_state_effects].
Qed.
Theorem RECORDCOUNT_failure_effects s sf :
  evals Precord record_stops pc_RECORDCOUNT [] s (OStop "FAIL" sf) ->
  vars s "num">remaining s /\ vars sf "t"=remaining s-vars s "num" /\
  vars sf "WHY"=hp s /\ vars sf "WHY_len" = 44 /\ hp sf=hp s+45 /\
  (forall a,a<hp s \/ hp s+45<=a->mem sf a=mem s a) /\
  (forall i,(i<45)%coq_nat->mem sf (hp s+Z.of_nat i)=nth x00 (rcons count_diagnostic x00) i) /\
  forall x,x<>"t"->x<>"WHY"->x<>"WHY_len"->vars sf x=vars s x.
Proof.
  intros Hr. apply RECORDCOUNT_fails_iff in Hr. destruct Hr as [Hgt ->].
  destruct (failure_state_registers s) as [Ht [Hw [Hl [Hhp Hvars]]]].
  split;[exact Hgt|]. split;[exact Ht|]. split;[exact Hw|]. split;[exact Hl|]. split;[exact Hhp|].
  split;[apply failure_state_memory_outside|]. split;[apply failure_state_memory_content|exact Hvars].
Qed.
Print Assumptions checked_state_effects.
Print Assumptions failure_state_registers.
Print Assumptions failure_state_memory_outside.
Print Assumptions failure_state_memory_content.
Print Assumptions failure_state_nul.
Print Assumptions RECORDCOUNT_return_effects.
Print Assumptions RECORDCOUNT_failure_effects.
