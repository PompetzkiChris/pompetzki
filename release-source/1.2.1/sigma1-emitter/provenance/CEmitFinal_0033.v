(* CEmitFinal_0033.v - lane L2R, 2026-10-10. (c), the general emitter / check_batch correspondence, closed in Rocq:
     emit A  := PRB ++ [pf_thm (bp A)]      (the replay prelude, then one theorem compiled from the derivation bp A)
     emit_ok : EmitterOK emit
   that is: for every closed, bounded, well-formed sentence A of sigma1's language, check_batch REGP (emit A) = true,
   the last theorem has no hypotheses, and its statement is [A] if A is true, not [A] if A is false
   (L2RAgree.stmt_of A (evb [] A)); emit_prov gives prov Gam of that statement (CEmitSpec2.emitter_sound).
   emit is a Rocq function (bp computes: every data lemma of the port is transparent). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Ax Checks Sub Replay ReplayT Replay2 Replay3 RpInit RpInitOk Expand Pure.
From L2R Require L2RSent L2RAgree.
From L2R.b0033 Require Import BrB_0033 Bridge_0033 CEmitSpec2_0033 PreludeB_0033 Prelude_0033 CEmitPf11b_0033 CEmitThm4_0033.
From L2R.b0033 Require PfSent8_0033.
Import ListNotations.

Definition emit (A : L2RSent.fm) : list thm := PRB ++ [pf_thm (PfSent8_0033.bp A)].

Theorem emit_ok : EmitterOK emit.
Proof. apply emitter_from_pf. intros A Hw Hb. exact (PfSent8_0033.bp_ok A Hw Hb). Qed.

Theorem emit_prov A : L2RSent.wf 0 A -> L2RSent.bounded A -> prov Gam (L2RAgree.stmt_of A (L2RAgree.evb [] A)).
Proof. exact (emitter_sound emit emit_ok A). Qed.
