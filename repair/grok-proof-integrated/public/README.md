# Gallina authentication gate proof

The new `PMPRepair/GrokAuthGate.v` is the Grok Bot contribution from the
verified `rocq-proof-results.tar.gz` archive. Its bytes were copied unchanged.
It proves that a decidable boolean gate accepts exactly prefixes of the
706-entry canonical registry `Cohen.RpInitOk.REG0` and derives the Gallina
checker's theorem and batch soundness from that gate.

The original mathematical core sources and the existing prefix proof sources
were copied into this directory without modification. `source-credit.json`
records their hashes and credits. The project MIT license is included in
`LICENSE`, copyright 2026 Christopher Pompetzki. Grok Bot receives source
credit for `GrokAuthGate.v`; Codex added the verification receipt, portable
builder, manifest verification and integration documentation. This license
scope covers these project sources. It does not assign a project license to
Rocq, its standard library, OCaml, Python, or their separate tool distributions.

## Exact theorem statements

```coq
prefix_eqb_spec : forall reg ref : list entry,
  prefix_eqb reg ref = true <-> reg = firstn (length reg) ref

auth_gate_iff : forall reg : list entry,
  auth_gate reg = true <-> exists n : nat, reg = firstn n REG0

auth_gate_length : forall reg : list entry,
  auth_gate reg = true -> length reg <= 706

auth_gate_check_thm_ok : forall (reg : list entry) (t : thm),
  auth_gate reg = true -> check_thm reg t = true ->
  prov (AH hypf (t_hyps t)) (tof (t_stmt t))

auth_gate_check_batch_ok : forall (reg : list entry) (ts : list thm),
  auth_gate reg = true -> check_batch reg ts = true ->
  reg_ok hypf (reg ++ map ent ts)

auth_gate_REG0 : auth_gate REG0 = true
auth_gate_canonical : auth_gate canonical_data = true
```

The result remains relative to the released `prov`, `hypf`, statement
translation `tof`, and declared theorem hypotheses. The batch conclusion is
`reg_ok hypf` for the resulting registry. `Print Assumptions` is recorded for
all seven lemmas, together with the exact types from `About`.

## Reproduce the proof check

Install Python 3 and Rocq with its standard library, then run from this
directory:

```sh
python build-gate-proof.py --output "fresh proof build"
```

The output directory must not already exist. The builder copies all 17 core
and five proof source files to it, compiles every copy freshly, prints the
types and assumptions, and recursively checks `PMPRepair.GrokAuthGateReceipt`
with `rocqchk -silent -o`. It uses neither `-admit` nor `-norec`. Tool paths
can be selected with `--coqc` and `--rocqchk`. Existing source files and prior
builds are preserved.

The integrated fresh run is recorded in `run-output.txt`,
`fresh-gate-proof-result.json`, `gate-types-and-assumptions.txt`, and
`kernel-check-context.txt`. Build objects remain separate from the public
source whitelist.

## Correspondence boundaries

The proofs establish the Gallina gate and the conditional Gallina checker
results above. The following obligations remain separate:

1. JDG1 text parsing and its denotation as Gallina entries and theorems.
2. The executable registry comparison implementing `auth_gate`, including
   whitespace, leading zeros and the accepted numeric domain.
3. PMP and Racket checking logic computing `check_thm` and `check_batch`.
4. PMP compiler lowering preserving program semantics.
5. The shipped executable bytes corresponding to the reviewed sources and
   compiler output.

The gate proof does not discharge these obligations. Generator byte equality
and finite test runs are separate evidence.

## Archive manifest verification

`archive-manifest-verification.json` verifies the archive manifest against
every delivered payload file and available contextual source file. The
manifest names 134 entries: 16 delivered payload entries, 60 repository source
context entries, two aliases for delivered new source files, and 56 compiled
build object context entries. All 16 delivered payload hashes and all 62
available source context hashes match. All delivered files except the manifest
itself are listed. The 56 compiled objects named by the manifest were not
included in the delivered archive and were not compared to a remote object.
The integrated proof check generated and checked new local objects from source.

`PUBLIC-WHITELIST.json` lists the public integration files. The whitelist
excludes account records, archive delivery metadata, author machine paths,
private orchestration scripts and compiled build objects.
