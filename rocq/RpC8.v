(* RpC8.v - written by general/replay/mkchecks.sh: batch 8 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB8 RpC7.
Import ListNotations.
Definition REG9 : list entry := REG8 ++ E8.
Lemma E8_eq : E8 = map ent B8. Proof. vm_compute. reflexivity. Qed.
Lemma B8_ok : check_batch REG8 B8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG9_ok : reg_ok hypf REG9.
Proof. unfold REG9. rewrite E8_eq. exact (check_batch_ok hypf REG8 B8 REG8_ok B8_ok). Qed.
