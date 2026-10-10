(* RpC0.v - written by general/replay/mkchecks.sh: batch 0 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB0 RpInitOk.
Import ListNotations.
Definition REG1 : list entry := REG0 ++ E0.
Lemma E0_eq : E0 = map ent B0. Proof. vm_compute. reflexivity. Qed.
Lemma B0_ok : check_batch REG0 B0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG1_ok : reg_ok hypf REG1.
Proof. unfold REG1. rewrite E0_eq. exact (check_batch_ok hypf REG0 B0 REG0_ok B0_ok). Qed.
