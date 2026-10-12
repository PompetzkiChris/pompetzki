# Canonical registry proof sources

These sources prove exact equality between the generated 706-entry registry
`canonical_data` and the released canonical registry `Cohen.RpInitOk.REG0`.
They prove soundness of every prefix and derive the released Gallina
`check_thm` and `check_batch` soundness consequences under an explicit exact
prefix-equality premise. General executable/parser correspondence remains open.

The source package requires Python 3.11 or later and Rocq with its standard
library. The sources have been checked with Rocq 9.1.0 and OCaml 4.14.2. The
compiler and checker may be supplied through `PATH` or explicit executable
arguments.

From the extracted release root, run:

```sh
python judge/rocq/build-registry-proof.py --output "proof build"
```

The default core source directory is `../../rocq` relative to the builder.
To use a separately located core source directory, pass `--core`. To select
installed tools explicitly, use `--coqc` and `--rocqchk`:

```sh
python judge/rocq/build-registry-proof.py --core "released core sources" --output "fresh proof build" --coqc coqc --rocqchk rocqchk
```

`--output` must name a directory that does not yet exist. Without `--output`,
the builder creates a new temporary directory and prints its path. It copies
the 22 source files there, checks their hashes against
`public-source-inputs.json`, compiles all 17 core modules freshly, compiles the
five proof modules, and recursively kernel-checks the proof closure. The
kernel command uses neither `-admit` nor `-norec`. Sources and existing build
directories are preserved.

The build directory contains `build-result.json`, per-command stdout and
stderr logs, freshly compiled objects, copied source files, and
`SHA256SUMS.txt`. The JSON receipt records exact command arguments, exit codes,
timeouts, durations, source hashes before and after execution, the kernel
context, and the 6 plus 7 `Print Assumptions` results. The builder exits 0 only
after all 22 compilations and the recursive kernel check pass, both assumption
counts match, the kernel reports no added axioms or unsafe settings, and the
input source hashes remain unchanged.

The five proof modules are:

| Source | Result |
| --- | --- |
| `PrefixSoundness.v` | Generic `firstn` lookup preservation, prefix registry soundness, and conditional checker consequences for `REG0` |
| `PrefixSoundnessReceipt.v` | Types and assumptions for the six generic results |
| `CanonicalRegistryData.v` | Generated literal definition of the 706-entry registry |
| `CanonicalPrefixSoundness.v` | Exact generated-data equality, computed length, prefix soundness, and conditional checker consequences |
| `CanonicalPrefixSoundnessReceipt.v` | Types and assumptions for the seven generated-data results |

The required core modules, in build order, are `Syn`, `Prov`, `Kal`, `Val`,
`Inv`, `Parse`, `Data`, `Checks`, `Ax`, `Sub`, `Expand`, `Replay`, `ReplayT`,
`Replay2`, `Replay3`, `RpInit`, and `RpInitOk`. Their `.v` files come from
published source commit `e8958a92d72c0b4cace72949510807b8a5b1320e`. Exact
source filenames, hashes, the public whitelist, and provenance mapping appear
in `public-source-inputs.json`.

`CanonicalRegistryData.v` was generated from the initial registry of released
`replay-all.jdg`, whose SHA256 is
`a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae`.
The kernel proves equality of the resulting registry AST with `REG0`. The
proof does not establish parser or generated executable correspondence.

The package uses the candidate release's MIT license in `LICENSE`, with
copyright 2026 Christopher Pompetzki. Include that license with these sources.
The public proof source whitelist consists of the five `.v` proof files, this
README, the Python builder, `public-source-inputs.json`, and the 17 required
core `.v` files. Build receipts, compiled objects, logs, caches, and prior
machine-specific run scripts are separate build outputs.
