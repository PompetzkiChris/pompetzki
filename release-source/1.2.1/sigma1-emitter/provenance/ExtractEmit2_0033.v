(* ExtractEmit2_0033.v (ExtractEmit_0033.v failed: REGP lives in Bridge_0033, not imported) - lane L2R, 2026-10-10. Scheme extraction of the proved emitter CEmitFinal_0033.emit,
   so that Prop components (eq_rect casts, conj destructs on opaque proofs) are erased and the data runs. *)
From Stdlib Require Import List NArith Extraction.
From Cohen Require Import Syn Prov Ax Replay2.
From L2R Require L2RSent L2RAgree.
From L2R.b0033 Require Import Bridge_0033 CEmitFinal_0033 Prelude_0033.
From L2R.b0033 Require PfSent8_0033.
Extraction Language Scheme.
Definition A0 := L2RSent.feq (L2RSent.tnum 0) (L2RSent.tnum 0).
Definition A1 := L2RSent.feq (L2RSent.tadd (L2RSent.tnum 2) (L2RSent.tnum 2)) (L2RSent.tnum 4).
Extraction "emit2_0033.scm" emit PfSent8_0033.bp check_batch REGP A0 A1.
