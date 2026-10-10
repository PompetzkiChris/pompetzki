(* RpC5.v - written by general/replay/mkchecks.sh: batch 5 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB5 RpC4.
Import ListNotations.
Definition REG6 : list entry := REG5 ++ E5.
Lemma E5_eq : E5 = map ent B5. Proof. vm_compute. reflexivity. Qed.
Lemma B5_ok : check_batch REG5 B5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG6_ok : reg_ok hypf REG6.
Proof. unfold REG6. rewrite E5_eq. exact (check_batch_ok hypf REG5 B5 REG5_ok B5_ok). Qed.
