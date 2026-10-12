The corrected NASM runtime accepts every signed 64-bit decimal and hexadecimal machine-word literal, including -9223372036854775808, and rejects magnitudes outside that range. It accumulates the magnitude negatively, checks every multiplication and subtraction, and checks the final negation of a positive literal. The console interpreter, window interpreter, and emitted programs use that parser.

Build the corrected binaries from the single authoritative runtime source:

```powershell
python repair/runtime/build-monolithic.py repaired
```

This requires NASM and a MinGW-w64 gcc on PATH. It writes the console and window binaries to `repair/runtime/build/repaired/` and a build receipt with commands, PE metadata, source hash, and binary hashes. The linker uses `--no-insert-timestamp`. A second build in `build/repaired-repeat/` produced byte-identical binaries.

The public `Abschluss-1.0-source.zip` contains the cockpit's native.asm but omits the NASM interpreter source. The separately downloaded public `pompetzki-source-20261010.zip`, verified against its SHA256SUMS, also omits it. `source-download.json` records that download. The baseline runtime source was copied from `C:\ClaudeOutput\pompetzki\pompetzki.asm`, preserving the original. The local executable is byte-identical to the audited public executable.

The baseline source rebuild has the same PE data, constants, imports, bss, and relocation sections as the public executable. Its .text bytes differ because code blocks have a different layout. Comparing the disassembly by named block gives 1293/1293 matching instruction sequences after removing instruction addresses and resolved symbolic branch/RIP target displacements. Integer immediates, instructions, and target symbols are retained. The source rebuild also matches all eight previously captured exact-tool stdout records, including the original literal rejection. Evidence is in `build/baseline-monolithic/symbolic-code-comparison.json` and `tests/baseline-behavior-comparison.json`.

The copied parts and the first attempted parts concatenation are preserved in `baseline-source/` and `build/baseline/`. That concatenation failed NASM with duplicate labels and concatenated directives; it is not the corrected runtime's source or build route. The preserved historical source search and its 43 rebuild results are in `baseline-search/`. `source/pompetzki.asm` is the corrected runtime's authoritative source.

Exact regression results:

| Target | Independent exact tool cases | Literal boundary cases | Emitted valid literals | Emitted invalid literals |
|---|---:|---:|---:|---:|
| Corrected console | 918/918 | 32/32 | 12/12 | 20/20 |
| Corrected window | 918/918 | 32/32 | 12/12 | 20/20 |

The tool cases use Python integers and fractions.Fraction with no floating arithmetic or tolerance. The original direct minimum literals are used in the modular matrix and CRT cases. Both corrected targets pass all 95 modular matrix cases and all 138 CRT cases. The 150-case strx suite passes against the corrected top-level library, including embedded NUL bytes and direct input-preservation checks. Its seven missing conversion-site length bindings have been supplied in `repair/libraries/strx/strx.pmp`. The historical nested include is generated as a byte-identical copy from that canonical source by `repair/libraries/strx/strx-byte-build.rkt`.

The portable oracle generators preserve the mathematical expectations and create test code, expected output, actual output, and count receipts:

```powershell
python repair/runtime/oracles/generate-exact.py
python repair/runtime/oracles/generate-strx.py
```

Their fixtures and outputs are under `tests/generated/`. `tests/exact-suite-results.json` contains both corrected target runs and the reconstructed baseline run. `tests/numeric-boundary-corrected-results.json` contains the literal results, and `tests/emitted-invalid-results.json` contains all 40 emitted rejection tests. The first literal-result classification excluded the expected unknown-name errors for +1 and quoted tokens; that original classification and its outputs remain alongside the corrected classification. No runtime implementation change was required for that test correction.

`reproducibility.json` records the identical repeat-build hashes and identical canonical/generated library hashes. `SHA256SUMS.txt` lists the files in this runtime repair and its library repair, excluding the manifest itself.
