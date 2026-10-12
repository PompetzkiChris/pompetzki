# Matrix batch recovery: math-workbench-v2 at 2f78feb (Grok Bot accountability)
Source checkout: anonymous clone, codex/exact-release-repair 2f78feb (branch later moved to c886685; exact.rkt, gui.rkt and engine.rkt are byte-identical at c886685). Harness: `matrix.py` (my own; exact Python Fraction oracle, no floats). Rerun: `python3 matrix.py OUTDIR REPO/repair [compiled-engine]`.
Mixed batch = 7 valid jobs (det 2x2, det 3x3 with fractions, transpose, mul, rref, inv, solve) interleaved with 11 malformed items (null, 7, "bad", [], {}, missing op, missing a, unknown op, wrong dims, 1.5 entry, numeric a).

| Claim | Command | Actual output | Verified outcome |
|---|---|---|---|
| Old corrected engine fails the whole batch on a malformed item | `racket math-workbench-corrected/engine.rkt --batch corrected-mixed.json` | exit 1, stdout 0 bytes, `hash-ref: contract violation expected: hash? given: 'null` | **DEFECT REPRODUCED** |
| Corrected: all-malformed batch | same, corrected-allbad.json | exit 1, same contract violation | **DEFECT REPRODUCED** |
| Corrected: empty batch | `--batch []` | exit 0, `[]` | PASS |
| v2 keeps valid jobs and rejects each malformed item | `racket math-workbench-v2/engine.rkt --batch v2-racket-mixed.json` | exit 0, 18 records; each malformed item exit 1, status rejected, own id, reason; all 7 valid answers match the oracle (e.g. det -2, solve 4/5, 7/5) | **PASS (FIXED)** |
| v2: all-malformed batch | v2-racket-allbad.json | exit 0, 11 records, all rejected | PASS |
| v2: empty batch | `--batch []` | exit 0, `[]` | PASS |
| Compiled route | `build.py` / `raco exe` | build exit 1; my minimal Racket install has no `raco exe` / GUI libraries (raw/*build*.txt) | **NOT RUN** (blocked by my toolchain, not shown to be a product defect) |
| exact.rkt / gui.rkt (arithmetic, GUI) unchanged corrected to v2 | sha256sum (raw/source-compare.txt) | exact.rkt eaa5917f… IDENTICAL; gui.rkt 07fd6e0f… IDENTICAL; test-gui.rkt, build.py IDENTICAL; engine.rkt DIFFERS (2cf5af81… to 99084a40…) | **CLAIM HOLDS** (the change is limited to engine.rkt plus docs/tests) |

Harness note: the first run used op name `inverse`, which v2 correctly rejected as unknown. The engine's op is `inv`. I fixed my harness and reran. Only the final run is kept.

Separate finite byte comparison, carried forward from book-v5-453afa6/raw/strip-compare.txt: after `objcopy --strip-all`, my built judge-v5-linux and the committed binary were compared by sha256. That result stays a byte comparison of two files and proves no source correspondence.

Finite tests do NOT establish executable/Gallina correspondence, parser denotation, or compiler preservation.
