(* Grok Bot addition (new file). A Gallina model of the judges' initial-registry gate:
   accept iff the submitted registry has at most 706 entries and agrees entrywise with REG0.
   Proves the gate decides exactly "reg = firstn n REG0 for some n", so the premise of the
   authenticated_* theorems is discharged by a boolean check. Executable correspondence
   (pmp/Racket bytes vs this function) is NOT addressed here. *)
From Stdlib Require Import List Arith NArith Bool Lia.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInitOk.
From PMPRepair Require Import PrefixSoundness CanonicalRegistryData CanonicalPrefixSoundness.
Import ListNotations.

Definition dform_eq_dec : forall a b : dform, {a = b} + {a <> b}.
Proof. decide equality; try apply N.eq_dec; apply (list_eq_dec N.eq_dec). Defined.

Definition entry_eq_dec : forall a b : entry, {a = b} + {a <> b}.
Proof. decide equality; [apply (list_eq_dec N.eq_dec)|apply dform_eq_dec]. Defined.

Fixpoint prefix_eqb (reg ref : list entry) : bool :=
  match reg, ref with
  | [], _ => true
  | x :: r, y :: s => if entry_eq_dec x y then prefix_eqb r s else false
  | _ :: _, [] => false
  end.

Definition auth_gate (reg : list entry) : bool := prefix_eqb reg REG0.

Lemma prefix_eqb_spec reg ref :
  prefix_eqb reg ref = true <-> reg = firstn (length reg) ref.
Proof.
  revert ref; induction reg as [|x r IH]; intros [|y s]; simpl; split; intro H;
    try reflexivity; try discriminate.
  - destruct (entry_eq_dec x y) as [->|]; [f_equal; apply IH; exact H|discriminate].
  - injection H as -> E. destruct (entry_eq_dec y y) as [_|C]; [apply IH; exact E|congruence].
Qed.

Theorem auth_gate_iff (reg : list entry) :
  auth_gate reg = true <-> exists n, reg = firstn n REG0.
Proof.
  unfold auth_gate; rewrite prefix_eqb_spec; split.
  - intro E; exists (length reg); exact E.
  - intros [n ->]. rewrite length_firstn.
    destruct (Nat.le_ge_cases n (length REG0)) as [L|L].
    + rewrite Nat.min_l by exact L. reflexivity.
    + rewrite Nat.min_r by exact L. rewrite !firstn_all2 by (exact L || apply Nat.le_refl). reflexivity.
Qed.

Theorem auth_gate_length (reg : list entry) : auth_gate reg = true -> length reg <= 706.
Proof.
  intros [n E]%auth_gate_iff. subst reg. rewrite length_firstn.
  rewrite <- canonical_data_eq_REG0, canonical_data_length. apply Nat.le_min_r.
Qed.

Theorem auth_gate_check_thm_ok (reg : list entry) (t : thm) :
  auth_gate reg = true -> check_thm reg t = true ->
  prov (AH hypf (t_hyps t)) (tof (t_stmt t)).
Proof.
  intros [n E]%auth_gate_iff C. exact (authenticated_REG0_prefix_check_thm_ok reg n t E C).
Qed.

Theorem auth_gate_check_batch_ok (reg : list entry) (ts : list thm) :
  auth_gate reg = true -> check_batch reg ts = true -> reg_ok hypf (reg ++ map ent ts).
Proof.
  intros [n E]%auth_gate_iff C. exact (authenticated_REG0_prefix_check_batch_ok reg n ts E C).
Qed.

Theorem auth_gate_REG0 : auth_gate REG0 = true.
Proof. vm_compute. reflexivity. Qed.
Theorem auth_gate_canonical : auth_gate canonical_data = true.
Proof. vm_compute. reflexivity. Qed.
