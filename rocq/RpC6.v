(* RpC6.v - written by general/replay/mkchecks.sh: batch 6 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB6 RpC5.
Import ListNotations.
Definition REG7 : list entry := REG6 ++ E6.
Lemma E6_eq : E6 = map ent B6. Proof. vm_compute. reflexivity. Qed.
Lemma B6_ok : check_batch REG6 B6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG7_ok : reg_ok hypf REG7.
Proof. unfold REG7. rewrite E6_eq. exact (check_batch_ok hypf REG6 B6 REG6_ok B6_ok). Qed.
