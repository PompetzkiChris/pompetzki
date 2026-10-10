(* CEmitSpec2_0033.v - lane L2R, 2026-10-10 (CEmitSpec_0033.v: Lia not imported). Part of (c): the general sigma1 emitter / check_batch correspondence, as a
   compiled Rocq statement. An emitter is a function from sentences of sigma1's language (L2RSent.fm) to batches of
   Replay2 theorems over the 677-entry registry REGP of every lane file.
     EmitterOK emit : for every closed bounded well-formed A, check_batch REGP (emit A) = true, the last theorem of
                      emit A has no hypotheses, and its statement is [A] if A is true, not [A] if A is false
                      (L2RAgree.stmt_of A (evb [] A)).
     emitter_sound  : EmitterOK emit -> for every such A, prov Gam (stmt_of A (evb [] A)).
   The remaining construction of (c) is a function emit with EmitterOK emit (and sigma1.rkt's generator replaced by,
   or proved equal to, it). bounded_complete (round 1) already gives the provability; EmitterOK is about the
   executable batches. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Replay2 Replay3 Expand Pure RpInit RpInitOk RpFinal.
From L2R Require Import L2RLogic L2RArith L2RSent L2RAgree.
From L2R.b0033 Require Import BrB_0033 Bridge_0033.
Import ListNotations.

Definition last_thm (B : list thm) : option thm := match rev B with t :: _ => Some t | [] => None end.

Definition EmitterOK (emit : fm -> list thm) : Prop :=
  forall A, wf 0 A -> bounded A ->
    check_batch REGP (emit A) = true /\
    exists t, last_thm (emit A) = Some t /\ t_hyps t = [] /\ tof (t_stmt t) = stmt_of A (evb [] A).

Lemma last_thm_split B t : last_thm B = Some t -> exists B', B = B' ++ [t].
Proof.
  unfold last_thm. intros H. destruct (rev B) as [|x r] eqn:E; [discriminate|]. injection H as <-.
  exists (rev r). rewrite <- (rev_involutive B), E. reflexivity.
Qed.

Theorem emitter_sound emit : EmitterOK emit -> forall A, wf 0 A -> bounded A -> prov Gam (stmt_of A (evb [] A)).
Proof.
  intros OK A Hw Hb. destruct (OK A Hw Hb) as [Hc [t [Ht [Hh Hs]]]].
  pose proof (check_batch_ok hypf REGP (emit A) REGP_ok Hc) as R.
  destruct (last_thm_split _ _ Ht) as [B' EB].
  assert (N : nth_error (REGP ++ map ent (emit A)) (length REGP + length B') = Some (t_stmt t, [])).
  { rewrite nth_error_app2 by lia. replace (length REGP + length B' - length REGP) with (length B') by lia.
    rewrite EB, map_app. rewrite nth_error_app2 by (rewrite length_map; lia).
    rewrite length_map, Nat.sub_diag. cbn. unfold ent. rewrite Hh. reflexivity. }
  pose proof (R _ _ _ N) as P. rewrite Hs in P.
  apply (prov_mono (AH hypf [])); [|exact P]. intros g [G|[h [[] _]]]. exact G.
Qed.
