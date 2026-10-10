(* RpC2.v - written by general/replay/mkchecks.sh: batch 2 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB2 RpC1.
Import ListNotations.
Definition REG3 : list entry := REG2 ++ E2.
Lemma E2_eq : E2 = map ent B2. Proof. vm_compute. reflexivity. Qed.
Lemma B2_ok : check_batch REG2 B2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG3_ok : reg_ok hypf REG3.
Proof. unfold REG3. rewrite E2_eq. exact (check_batch_ok hypf REG2 B2 REG2_ok B2_ok). Qed.
