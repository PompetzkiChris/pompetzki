(* RpC7.v - written by general/replay/mkchecks.sh: batch 7 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB7 RpC6.
Import ListNotations.
Definition REG8 : list entry := REG7 ++ E7.
Lemma E7_eq : E7 = map ent B7. Proof. vm_compute. reflexivity. Qed.
Lemma B7_ok : check_batch REG7 B7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG8_ok : reg_ok hypf REG8.
Proof. unfold REG8. rewrite E7_eq. exact (check_batch_ok hypf REG7 B7 REG7_ok B7_ok). Qed.
