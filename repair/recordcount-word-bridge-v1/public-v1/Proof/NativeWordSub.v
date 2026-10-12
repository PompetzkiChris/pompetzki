(* Bridge to preserved CX4 X86Native3.execute primitive semantics.
   No compiler-image, fetched step, JS decoding, or process execution identification. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From C2Link Require Import PmpCore.
From GrokRC Require GrokRecordCount GrokUnsigned64.
From RecordCount Require Import RecordCountStep RecordCountBounds.
From Native Require X86Native3.
From WordBridge Require Import PmpWordSub.
Import ListNotations.
Module N := X86Native3.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Lemma native_w64_encode z : N.w64 z = U.encode64 z.
Proof. reflexivity. Qed.
Lemma native_w64_idempotent z : N.w64 (N.w64 z) = N.w64 z.
Proof. unfold N.w64. rewrite Z.mod_mod; [reflexivity|unfold N.W64;lia]. Qed.
Lemma native_sub_word a b : N.aluvalue N.Sub a b = U.wsub64 a b.
Proof. reflexivity. Qed.
Lemma native_msb_topbit z : N.msb z = U.topbit64 (U.encode64 z).
Proof.
  unfold N.msb,U.topbit64. rewrite Z.testbit_eqb; [rewrite native_w64_encode;reflexivity|lia].
Qed.
Lemma native_reg_self d : N.reg_eqb d d = true.
Proof. destruct d;reflexivity. Qed.
Lemma native_reg_different q d : q <> d -> N.reg_eqb q d = false.
Proof. destruct q,d;intros H;try reflexivity;contradiction. Qed.
Lemma native_getreg_updated m d v : N.getreg (N.updreg m d v) d = N.w64 v.
Proof.
  unfold N.getreg,N.updreg;cbn. unfold N.setreg.
  rewrite native_reg_self native_w64_idempotent. reflexivity.
Qed.

Definition native_sub_state m dst src len :=
  N.updpc
    (N.updflags (N.updreg m dst (N.aluvalue N.Sub (N.getreg m dst) (N.val m src)))
       (N.subflags (N.getreg m dst) (N.val m src)))
    (N.w64 (N.rip m+Z.of_nat len)).

Theorem native_sub_exec m dst src len :
  N.execute (N.ALU N.Sub dst src) len m = Some (N.Continue (native_sub_state m dst src len)).
Proof. reflexivity. Qed.

Theorem native_sub_effects m dst src len :
  N.getreg (native_sub_state m dst src len) dst = U.wsub64 (N.getreg m dst) (N.val m src) /\
  N.sf (N.status (native_sub_state m dst src len)) =
    Some (U.topbit64 (U.wsub64 (N.getreg m dst) (N.val m src))) /\
  N.mem (native_sub_state m dst src len) = N.mem m /\
  N.rflags_other (native_sub_state m dst src len) = N.rflags_other m /\
  N.rip (native_sub_state m dst src len) = U.encode64 (N.rip m+Z.of_nat len) /\
  (forall q, q <> dst -> N.registers (native_sub_state m dst src len) q = N.registers m q).
Proof.
  split.
  - change (N.getreg (N.updreg m dst (N.aluvalue N.Sub (N.getreg m dst) (N.val m src))) dst =
      U.wsub64 (N.getreg m dst) (N.val m src)).
    rewrite native_getreg_updated native_sub_word. unfold U.wsub64.
    change (N.w64 (N.w64 (N.getreg m dst-N.val m src)) = N.w64 (N.getreg m dst-N.val m src)).
    apply native_w64_idempotent.
  - split.
    + change (Some (N.msb (N.w64 (N.getreg m dst-N.val m src))) =
        Some (U.topbit64 (U.wsub64 (N.getreg m dst) (N.val m src)))).
      rewrite native_msb_topbit. change (Some (U.topbit64 (N.w64 (N.w64 (N.getreg m dst-N.val m src)))) =
        Some (U.topbit64 (U.wsub64 (N.getreg m dst) (N.val m src)))).
      rewrite native_w64_idempotent. reflexivity.
    + split; [reflexivity|]. split; [reflexivity|]. split.
      * change (N.w64 (N.w64 (N.rip m+Z.of_nat len)) = U.encode64 (N.rip m+Z.of_nat len)).
        rewrite native_w64_idempotent. reflexivity.
      * intros q H. unfold native_sub_state,N.updpc,N.updflags,N.updreg;cbn.
        unfold N.setreg. rewrite (native_reg_different H). reflexivity.
Qed.

Theorem native_sub_PMP_value s m x a b dst src len :
  N.getreg m dst = U.encode64 (ev s a) ->
  N.val m src = U.encode64 (ev s b) ->
  G.fits64 (ev s a-ev s b) ->
  U.decode64 (N.getreg (native_sub_state m dst src len) dst) =
    vars (setv s x (ev s a-ev s b)) x /\
  N.sf (N.status (native_sub_state m dst src len)) =
    Some (test CNeg (vars (setv s x (ev s a-ev s b)) x)).
Proof.
  intros Ha Hb Hfit. destruct (native_sub_effects m dst src len) as [Hv [Hsf _]].
  rewrite Hv Hsf Ha Hb (PMP_sub_word_commutes s x a b).
  have Hupdated : G.fits64 (vars (setv s x (ev s a-ev s b)) x).
  { rewrite setv_get String.eqb_refl. exact Hfit. }
  rewrite (U.decode_encode64_fits _ Hupdated) (PMP_negative_word_commutes Hupdated).
  split;reflexivity.
Qed.

Definition native_test_self_state m r len :=
  N.updpc (N.updflags m (N.logicflags (Z.land (N.getreg m r) (N.getreg m r))))
    (N.w64 (N.rip m+Z.of_nat len)).

Theorem native_test_self_exec m r len :
  N.execute (N.Test r r) len m = Some (N.Continue (native_test_self_state m r len)).
Proof. reflexivity. Qed.

Theorem native_test_self_effects m r len :
  N.sf (N.status (native_test_self_state m r len)) = Some (U.topbit64 (N.getreg m r)) /\
  N.registers (native_test_self_state m r len) = N.registers m /\
  N.mem (native_test_self_state m r len) = N.mem m /\
  N.rflags_other (native_test_self_state m r len) = N.rflags_other m.
Proof.
  split.
  - change (Some (N.msb (Z.land (N.getreg m r) (N.getreg m r))) = Some (U.topbit64 (N.getreg m r))).
    rewrite Z.land_diag native_msb_topbit.
    change (Some (U.topbit64 (N.w64 (N.w64 (N.registers m r)))) = Some (U.topbit64 (N.getreg m r))).
    rewrite native_w64_idempotent. reflexivity.
  - split; [reflexivity|]. split;reflexivity.
Qed.

Theorem RECORDCOUNT_native_negative_flag s m len : count_address_contract s ->
  N.getreg m N.RAX = U.encode64 (vars (checked_state s) "t") ->
  N.execute (N.Test N.RAX N.RAX) len m = Some (N.Continue (native_test_self_state m N.RAX len)) /\
  N.sf (N.status (native_test_self_state m N.RAX len)) =
    Some (test CNeg (vars (checked_state s) "t")) /\
  N.sf (N.status (native_test_self_state m N.RAX len)) = Some (remaining s <? vars s "num").
Proof.
  intros H Hreg. destruct (native_test_self_effects m N.RAX len) as [Hsf _].
  destruct (RECORDCOUNT_words_exact s) as [_ Hword].
  destruct (RECORDCOUNT_word_test H) as [Htest Hnum].
  rewrite Hreg in Hsf. rewrite <- Hword in Hsf. rewrite Hsf.
  split; [apply native_test_self_exec|]. split;[rewrite Htest|rewrite Hnum];reflexivity.
Qed.

Theorem native_sub_opcode_decodes :
  N.decode [72;41;200] = Some (N.ALU N.Sub N.RAX (N.RegVal N.RCX),3%nat,[]).
Proof. reflexivity. Qed.
Theorem native_test_opcode_decodes :
  N.decode [72;133;192] = Some (N.Test N.RAX N.RAX,3%nat,[]).
Proof. reflexivity. Qed.
