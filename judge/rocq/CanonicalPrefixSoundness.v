(* Soundness of prefixes of the generated embedded registry data. *)
From Stdlib Require Import List Arith NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInitOk.
From PMPRepair Require Import PrefixSoundness CanonicalRegistryData.
Import ListNotations.

Theorem canonical_data_eq_REG0 : canonical_data = REG0.
Proof. vm_compute. reflexivity. Qed.

Theorem canonical_data_length : length canonical_data = 706.
Proof. vm_compute. reflexivity. Qed.

Theorem canonical_data_ok : reg_ok hypf canonical_data.
Proof.
  rewrite canonical_data_eq_REG0. exact REG0_ok.
Qed.

Theorem canonical_data_prefix_ok (n : nat) :
  reg_ok hypf (firstn n canonical_data).
Proof.
  rewrite canonical_data_eq_REG0. apply REG0_prefix_ok.
Qed.

Theorem authenticated_canonical_prefix_ok (reg : list entry) (n : nat) :
  reg = firstn n canonical_data -> reg_ok hypf reg.
Proof.
  intros E. rewrite E. apply canonical_data_prefix_ok.
Qed.

Theorem authenticated_canonical_prefix_check_thm_ok
    (reg : list entry) (n : nat) (t : thm) :
  reg = firstn n canonical_data ->
  check_thm reg t = true ->
  prov (AH hypf (t_hyps t)) (tof (t_stmt t)).
Proof.
  intros E C.
  exact (check_thm_ok hypf reg t
    (authenticated_canonical_prefix_ok reg n E) C).
Qed.

Theorem authenticated_canonical_prefix_check_batch_ok
    (reg : list entry) (n : nat) (ts : list thm) :
  reg = firstn n canonical_data ->
  check_batch reg ts = true ->
  reg_ok hypf (reg ++ map ent ts).
Proof.
  intros E C.
  exact (check_batch_ok hypf reg ts
    (authenticated_canonical_prefix_ok reg n E) C).
Qed.
