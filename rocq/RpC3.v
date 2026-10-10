(* RpC3.v - written by general/replay/mkchecks.sh: batch 3 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB3 RpC2.
Import ListNotations.
Definition REG4 : list entry := REG3 ++ E3.
Lemma E3_eq : E3 = map ent B3. Proof. vm_compute. reflexivity. Qed.
Lemma B3_ok : check_batch REG3 B3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG4_ok : reg_ok hypf REG4.
Proof. unfold REG4. rewrite E3_eq. exact (check_batch_ok hypf REG3 B3 REG3_ok B3_ok). Qed.
