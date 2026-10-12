# Generated canonical registry and prefix proof receipt

The kernel checked exact equality of the generated embedded registry data with
the released canonical initial registry:

```coq
canonical_data_eq_REG0 : canonical_data = REG0
canonical_data_length : length canonical_data = 706
```

Both proofs use `vm_compute; reflexivity`. `REG0` belongs to the released
`Cohen.RpInitOk` module. `CanonicalRegistryData.v` contains the generated
registry definition, and `CanonicalPrefixSoundness.v` contains the equality
proof and its soundness consequences. The new logical namespace is
`PMPRepair`.

The native Rocq compiler accepted `CanonicalRegistryData.v`,
`CanonicalPrefixSoundness.v`, and `CanonicalPrefixSoundnessReceipt.v` with exit
0. The recursive kernel check exited 0 in 15.214402 seconds. It checked these
results, the six generic prefix results, and their dependencies. No command
timed out. All seven added results report `Closed under the global context`.
The kernel context reports no axioms, type-in-type dependencies, unsafe
fixpoints, or assumed positivity.

The generated registry source retained SHA256
`9b149f5100921e9f6228041d1350ed45bc873b2ee936772ee8952ae4d26167aa` before
and after compilation. All 17 dependency source hashes match public commit
`e8958a92d72c0b4cace72949510807b8a5b1320e`. All 17 dependency compiled hashes
were unchanged after the check.

```coq
canonical_data_ok : reg_ok hypf canonical_data

canonical_data_prefix_ok :
  forall n : nat, reg_ok hypf (firstn n canonical_data)

authenticated_canonical_prefix_ok :
  forall (reg : list entry) (n : nat),
    reg = firstn n canonical_data -> reg_ok hypf reg

authenticated_canonical_prefix_check_thm_ok :
  forall (reg : list entry) (n : nat) (t : thm),
    reg = firstn n canonical_data ->
    check_thm reg t = true ->
    prov (AH hypf (t_hyps t)) (tof (t_stmt t))

authenticated_canonical_prefix_check_batch_ok :
  forall (reg : list entry) (n : nat) (ts : list thm),
    reg = firstn n canonical_data ->
    check_batch reg ts = true ->
    reg_ok hypf (reg ++ map ent ts)
```

Every prefix is covered, including the empty prefix and values of `n` at or
above the registry length. Each checker consequence supplies the released
`Replay3.v` theorem with the proved registry premise. Exact submitted-registry
prefix equality remains an explicit theorem premise. Parser behavior, token
comparison, and executable correspondence require separate proofs.

Commands, exact argument vectors, exit codes, durations, theorem types, source
hashes, and absolute log paths are recorded in
`canonical-prefix-run-20261011-211231-299/canonical-prefix-proof-result.json`.
The code and run outputs are covered by
`canonical-prefix-run-20261011-211231-299/canonical-prefix-proof.sha256`.
`Run-CanonicalPrefixSoundness.ps1` reproduces this run using the verified
compiled released dependencies. The compiler is Rocq 9.1.0 with OCaml 4.14.2,
running natively on THEBIGMAGILLA, Alienware Area-51 AAT2265.
