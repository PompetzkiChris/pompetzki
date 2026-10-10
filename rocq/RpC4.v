(* RpC4.v - written by general/replay/mkchecks.sh: batch 4 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB4 RpC3.
Import ListNotations.
Definition REG5 : list entry := REG4 ++ E4.
Lemma E4_eq : E4 = map ent B4. Proof. vm_compute. reflexivity. Qed.
Lemma B4_ok : check_batch REG4 B4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG5_ok : reg_ok hypf REG5.
Proof. unfold REG5. rewrite E4_eq. exact (check_batch_ok hypf REG4 B4 REG4_ok B4_ok). Qed.
