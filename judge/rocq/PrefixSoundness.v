(* Prefix soundness over the released canonical registry.
   Exact equality with firstn n REG0 is a premise of the authenticated results.
   These results concern Gallina check_thm and check_batch. *)
From Stdlib Require Import List Arith NArith.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInitOk.
Import ListNotations.

Lemma firstn_lookup_preserved {A : Type} (n : nat) (l : list A)
    (i : nat) (x : A) :
  nth_error (firstn n l) i = Some x -> nth_error l i = Some x.
Proof.
  revert l i. induction n as [|n IH]; intros l i E; simpl in E.
  - destruct i; discriminate.
  - destruct l as [|a r]; [destruct i; discriminate|].
    destruct i as [|i]; simpl in *; [exact E|apply IH; exact E].
Qed.

Theorem reg_ok_firstn (hf : N -> form) (reg : list entry) (n : nat) :
  reg_ok hf reg -> reg_ok hf (firstn n reg).
Proof.
  intros R i d h E. apply (R i d h).
  exact (firstn_lookup_preserved n reg i (d, h) E).
Qed.

Theorem REG0_prefix_ok (n : nat) :
  reg_ok hypf (firstn n REG0).
Proof.
  apply reg_ok_firstn. exact REG0_ok.
Qed.

Theorem authenticated_REG0_prefix_ok (reg : list entry) (n : nat) :
  reg = firstn n REG0 -> reg_ok hypf reg.
Proof.
  intros E. rewrite E. apply REG0_prefix_ok.
Qed.

Theorem authenticated_REG0_prefix_check_thm_ok
    (reg : list entry) (n : nat) (t : thm) :
  reg = firstn n REG0 ->
  check_thm reg t = true ->
  prov (AH hypf (t_hyps t)) (tof (t_stmt t)).
Proof.
  intros E C.
  exact (check_thm_ok hypf reg t
    (authenticated_REG0_prefix_ok reg n E) C).
Qed.

Theorem authenticated_REG0_prefix_check_batch_ok
    (reg : list entry) (n : nat) (ts : list thm) :
  reg = firstn n REG0 ->
  check_batch reg ts = true ->
  reg_ok hypf (reg ++ map ent ts).
Proof.
  intros E C.
  exact (check_batch_ok hypf reg ts
    (authenticated_REG0_prefix_ok reg n E) C).
Qed.
