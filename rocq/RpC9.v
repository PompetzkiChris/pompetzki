(* RpC9.v - written by general/replay/mkchecks.sh: batch 9 checked, the registry extended. *)
From Stdlib Require Import List NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk RpB9 RpC8.
Import ListNotations.
Definition REG10 : list entry := REG9 ++ E9.
Lemma E9_eq : E9 = map ent B9. Proof. vm_compute. reflexivity. Qed.
Lemma B9_ok : check_batch REG9 B9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma REG10_ok : reg_ok hypf REG10.
Proof. unfold REG10. rewrite E9_eq. exact (check_batch_ok hypf REG9 B9 REG9_ok B9_ok). Qed.
