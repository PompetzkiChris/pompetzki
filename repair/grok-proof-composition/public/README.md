# Gallina registry-policy composition proof

`PMPRepair/GrokCompose47.v` is the received Grok Bot composition source, copied
without changes. It combines the existing Gallina initial-registry gate,
canonical registry proof, numeric digit-list policy and source checker soundness.
The project MIT license is included. `source-credit.json` records the credits
and exact hashes. Tool distributions and their libraries retain their own licenses.

This addendum freshly builds a minimal 24-module project dependency closure:
17 released Cohen core modules, the numeric policy model, and six proof modules.
The five main composition results are `REG0_policy_ok`,
`auth_gate_nums_within_policy`, `auth_gate_padded_spelling`,
`auth_gate_check_thm_ok_within_policy`, and
`auth_gate_check_batch_ok_within_policy`. The new decimal decoder lemmas
`decN_bound` and `decN_padded`, plus the `reg_nums_firstn` helper, are checked
as well. Exact `About` output and all eight `Print Assumptions` results are
preserved in `composition-types-and-assumptions.txt`.

The registry policy is a Gallina model over `list Z` digit values. Its maximum
is exactly 999999999999. Gate-accepted initial registries contain numbers within
that policy; their canonical decimal spellings and arbitrary leading-zero
padding decode to the same numbers. The checker consequences retain their
original `prov (AH hypf (t_hyps t)) (tof (t_stmt t))` or `reg_ok hypf` conclusions.
The numeric conjunct quantifies numbers in the initial registry, not theorem
bodies, theorem steps, or the appended output registry.

This is the theorem-level composition actually supplied by the source. It does
not prove that a character or byte parser constructs those entries or computes
`parse_decimal`; it does not establish executable gate or checker correspondence,
compiler preservation, or executable byte correspondence. No such theorem is
substituted for the received statements.

With Python 3 and Rocq plus its standard library installed, run:

```sh
python build-composition-proof.py --output "fresh composition build"
```

The output directory must be new. The builder copies and freshly compiles every
required source, prints exact statements and assumptions, then recursively checks
`PMPRepair.GrokCompositionReceipt` with `rocqchk -silent -o`, without `-admit` or
`-norec`. Explicit tools can be passed through `--coqc` and `--rocqchk`.

The integrated run is in `fresh-composition-result.json`, `run-output.txt`,
`composition-types-and-assumptions.txt` and `kernel-check-context.txt`. The public
manifest lists only source, provenance, these selected outputs and their hashes.
Compiled objects and private orchestration files are separate build artifacts.

The received archive manifest was checked against all 14 delivered payload
entries and available contextual files. Its 57 compiled-object entries were not
delivered. This addendum reports its own 24 fresh compilations and recursive
kernel check; it does not count the archive's broader 57-module claim as a local
result. `archive-manifest-verification.json` records the exact inventory and hashes.
