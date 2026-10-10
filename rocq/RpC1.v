(* RpC1.v - written by general/replay/mkchecks.sh: batch 1 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB1 RpC0.
Import ListNotations.
Definition REG2 : list entry := REG1 ++ E1.
Lemma E1_eq : E1 = map ent B1. Proof. vm_compute. reflexivity. Qed.
Lemma B1_ok : check_batch REG1 B1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG2_ok : reg_ok hypf REG2.
Proof. unfold REG2. rewrite E1_eq. exact (check_batch_ok hypf REG1 B1 REG1_ok B1_ok). Qed.
