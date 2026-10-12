(* Source addresses are integers; native LA48 canonicality and permission are separate.
   The existing source numeric contract is retained without strengthening its hypotheses. *)
From Stdlib Require Import List String ZArith Lia Bool Init.Byte.
From mathcomp Require Import all_ssreflect zify.
From C2Link Require Import PmpCore.
From RecordCount Require Import RecordCountStep RecordCountMemory RecordCountBounds.
From WordBridge Require Import PmpWordSub NativeWordSub.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Lemma source_nonnegative_word_identity z : 0 <= z < 4611686018427387904 ->
  U.encode64 z = z /\ U.decode64 (U.encode64 z) = z.
Proof.
  intros H. split.
  - unfold U.encode64. rewrite S.pow2_64. apply Z.mod_small;lia.
  - apply U.decode_encode64_fits. unfold G.fits64. rewrite G.pow2_63;lia.
Qed.

Theorem RECORDCOUNT_addresses_word_identity s : count_address_contract s ->
  U.encode64 (vars s "pos") = vars s "pos" /\
  U.decode64 (U.encode64 (vars s "pos")) = vars s "pos" /\
  U.encode64 (vars s "lim") = vars s "lim" /\
  U.decode64 (U.encode64 (vars s "lim")) = vars s "lim" /\
  U.encode64 (hp s) = hp s /\ U.decode64 (U.encode64 (hp s)) = hp s.
Proof.
  intros [Hnum [Hpos [Hhp Hcap]]].
  have Hp : 0 <= vars s "pos" < 4611686018427387904 by lia.
  have Hl : 0 <= vars s "lim" < 4611686018427387904 by lia.
  have Hh : 0 <= hp s < 4611686018427387904 by lia.
  destruct (source_nonnegative_word_identity Hp) as [Ap Bp].
  destruct (source_nonnegative_word_identity Hl) as [Al Bl].
  destruct (source_nonnegative_word_identity Hh) as [Ah Bh]. tauto.
Qed.

Lemma native_low_address_canonical a : 0 <= a < 140737488355328 -> N.canonical a = true.
Proof.
  intros [H0 Hlow]. unfold N.canonical,N.W64.
  have A : (0 <=? a) = true by apply Z.leb_le;exact H0.
  have B : (a <? 18446744073709551616) = true by apply Z.ltb_lt;lia.
  have C : (a <? 140737488355328) = true by apply Z.ltb_lt;exact Hlow.
  rewrite A B C. reflexivity.
Qed.

Definition noncanonical_source_state : state :=
  St (fun x => if String.eqb x "num" then 0 else 140737488355328)
     (fun _ => x00) 140737488355328.

Theorem RECORDCOUNT_numeric_contract_not_canonical :
  count_address_contract noncanonical_source_state /\
  N.canonical (hp noncanonical_source_state) = false.
Proof.
  split.
  - change (0 <= 0 <= 999999999999 /\
      0 <= 140737488355328 <= 140737488355328 /\
      140737488355328 <= 140737488355328 /\
      140737488355328 < 4611686018427387904). repeat split;lia.
  - reflexivity.
Qed.

Theorem RECORDCOUNT_low_input_canonical s a : count_address_contract s ->
  hp s < 140737488355328 -> vars s "pos" <= a < vars s "lim" ->
  N.canonical (U.encode64 a) = true.
Proof.
  intros [Hnum [Hpos [Hhp Hcap]]] Hlow Ha.
  have Hword : 0 <= a < 4611686018427387904 by lia.
  destruct (source_nonnegative_word_identity Hword) as [E _]. rewrite E.
  apply native_low_address_canonical;lia.
Qed.

Theorem RECORDCOUNT_low_diagnostic_canonical s : count_address_contract s ->
  hp s+45 < 140737488355328 ->
  N.canonical (vars (failure_state s) "WHY") = true /\
  N.canonical (hp (failure_state s)) = true /\
  (forall i, 0 <= i < 45 -> N.canonical (hp s+i) = true).
Proof.
  intros [Hnum [Hpos [Hhp Hcap]]] Hlow.
  destruct (failure_state_registers s) as [_ [Hw [_ [Halloc _]]]].
  rewrite Hw Halloc. split.
  - apply native_low_address_canonical;lia.
  - split.
    + apply native_low_address_canonical;lia.
    + intros i Hi. apply native_low_address_canonical;lia.
Qed.

Lemma native_readable_region_allowed nm a : N.canonical a = true ->
  (exists r, List.In r (N.regions nm) /\ N.readable r = true /\ N.lo r <= a < N.hi r) ->
  N.allowed N.readable nm a = true.
Proof.
  intros Hc [r [Hr [Hread [Hlo Hhi]]]]. unfold N.allowed. rewrite Hc. cbn.
  apply existsb_exists. exists r. split;[exact Hr|].
  apply Bool.andb_true_iff. split.
  - apply Bool.andb_true_iff. split;[exact Hread|apply Z.leb_le;exact Hlo].
  - apply Z.ltb_lt;exact Hhi.
Qed.

Definition native_cell nm a :=
  N.w8 (match N.ByteMap.find a (N.cells nm) with Some b => b | None => 0 end).
Definition byte_memory_agrees (s:state) (nm:N.memory) : Prop :=
  forall a, N.allowed N.readable nm a = true -> native_cell nm a = bz (mem s a).

Theorem native_readbyte_agrees s nm a : byte_memory_agrees s nm ->
  N.allowed N.readable nm a = true -> N.readbyte nm a = Some (bz (mem s a)).
Proof.
  intros Hmemory Hallowed. unfold N.readbyte. rewrite Hallowed.
  change (Some (native_cell nm a) = Some (bz (mem s a))). rewrite (Hmemory a Hallowed). reflexivity.
Qed.

Theorem RECORDCOUNT_native_input_byte s nm a : count_address_contract s ->
  hp s < 140737488355328 -> vars s "pos" <= a < vars s "lim" ->
  byte_memory_agrees s nm ->
  (exists r, List.In r (N.regions nm) /\ N.readable r = true /\ N.lo r <= a < N.hi r) ->
  N.readbyte nm (U.encode64 a) = Some (bz (mem s a)).
Proof.
  intros Hcontract Hlow Ha Hmemory Hregion.
  have Hc := RECORDCOUNT_low_input_canonical Hcontract Hlow Ha.
  destruct Hcontract as [Hnum [Hpos [Hhp Hcap]]].
  have Hword : 0 <= a < 4611686018427387904 by lia.
  destruct (source_nonnegative_word_identity Hword) as [E _]. rewrite E in Hc. rewrite E.
  apply native_readbyte_agrees;[exact Hmemory|].
  apply native_readable_region_allowed;assumption.
Qed.
