# Canonical REG0 prefix proof receipt

The native Rocq compiler accepted `PrefixSoundness.v` and
`PrefixSoundnessReceipt.v`. The recursive kernel check exited 0 in 18.186913
seconds. No command timed out. All six results report `Closed under the global
context`. The kernel context reports no axioms, type-in-type dependencies,
unsafe fixpoints, or assumed positivity.

The released dependency sources used here belong to commit
`e8958a92d72c0b4cace72949510807b8a5b1320e`. All 17 checked dependency source
hashes match the public source hashes. Their compiled dependency hashes were
unchanged after the check. Commands, exact argument vectors, exit codes,
durations, hashes, and absolute log paths are recorded in
`prefix-run-20261011-210906-291/prefix-proof-result.json`.

```coq
REG0_prefix_ok :
  forall n : nat, reg_ok hypf (firstn n REG0)

authenticated_REG0_prefix_ok :
  forall (reg : list entry) (n : nat),
    reg = firstn n REG0 -> reg_ok hypf reg

authenticated_REG0_prefix_check_thm_ok :
  forall (reg : list entry) (n : nat) (t : thm),
    reg = firstn n REG0 ->
    check_thm reg t = true ->
    prov (AH hypf (t_hyps t)) (tof (t_stmt t))

authenticated_REG0_prefix_check_batch_ok :
  forall (reg : list entry) (n : nat) (ts : list thm),
    reg = firstn n REG0 ->
    check_batch reg ts = true ->
    reg_ok hypf (reg ++ map ent ts)
```

The source also proves lookup preservation through `firstn` and the generic
`reg_ok_firstn` theorem for any hypothesis function and any sound registry.
Each checker consequence supplies the released `Replay3.v` theorem with the
proved registry premise. Exact equality with a canonical prefix is an explicit
premise. Parser behavior and executable correspondence require separate proofs.

The code and run outputs are covered by
`prefix-run-20261011-210906-291/prefix-proof.sha256`.
The compiler is Rocq 9.1.0 with OCaml 4.14.2, running natively on
THEBIGMAGILLA, Alienware Area-51 AAT2265.
