(* Remaining fixed-width operations under the readable-buffer/heap contract. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep.
From RDNUM Require Import RDNUMReaders RDNUMNumber RDNUMDelimiter RDNUMWordBounds.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Theorem source_cursor_increment_signed64 pos lim :
  0<=pos<lim -> lim<4611686018427387904 ->
  signed64 (pos+1)=pos+1 /\ 0<=pos+1<=lim.
Proof. intros Hpos Hlim;split;[apply signed64_identity|];lia. Qed.
Theorem source_scratch_operations_signed64 c nd :
  0<=c<256 -> 0<=nd<=12 ->
  signed64 (c-48)=c-48 /\ signed64 (c-48-10)=c-48-10 /\
  signed64 (c-32)=c-32 /\ signed64 (c-10)=c-10 /\
  signed64 (c-13)=c-13 /\ signed64 (c-9)=c-9 /\
  signed64 (nd-12)=nd-12 /\ signed64 (nd+1)=nd+1.
Proof. intros Hc Hn;repeat split;apply signed64_identity;lia. Qed.

Theorem source_diagnostic_heap_signed64 s : 0<=hp s<4611686018427387904 ->
  hp (number_limit s)=hp s+45 /\
  hp (number_expected s)=hp s+22 /\
  hp (token_failure s)=hp s+36 /\
  signed64 (hp (number_limit s))=hp (number_limit s) /\
  signed64 (hp (number_expected s))=hp (number_expected s) /\
  signed64 (hp (token_failure s))=hp (token_failure s).
Proof.
  intros Hhp.
  have HL : size (bytes_of_str "a number has more than 12 significant digits") = 44%N by vm_compute;reflexivity.
  have HE : size (bytes_of_str "a number was expected") = 21%N by vm_compute;reflexivity.
  have HT : size (bytes_of_str "a token does not end in white space") = 35%N by vm_compute;reflexivity.
  have HbL : hp (number_limit s)=hp s+45.
  { unfold number_limit,number_prepare;rewrite text_new_hpE !setv_hp HL;lia. }
  have HbE : hp (number_expected s)=hp s+22.
  { unfold number_expected;rewrite text_new_hpE HE;lia. }
  have HbT : hp (token_failure s)=hp s+36.
  { unfold token_failure,sw9,sw13,sw10,sw32,sw_byte,sw_limit;rewrite text_new_hpE !setv_hp HT;lia. }
  rewrite HbL HbE HbT. repeat split;try reflexivity;apply signed64_identity;lia.
Qed.
Print Assumptions source_cursor_increment_signed64.
Print Assumptions source_scratch_operations_signed64.
Print Assumptions source_diagnostic_heap_signed64.
