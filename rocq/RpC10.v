(* RpC10.v - written by general/replay/mkchecks.sh: batch 10 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB10 RpC9.
Import ListNotations.
Definition REG11 : list entry := REG10 ++ E10.
Lemma E10_eq : E10 = map ent B10. Proof. vm_compute. reflexivity. Qed.
Lemma B10_ok : check_batch REG10 B10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG11_ok : reg_ok hypf REG11.
Proof. unfold REG11. rewrite E10_eq. exact (check_batch_ok hypf REG10 B10 REG10_ok B10_ok). Qed.
