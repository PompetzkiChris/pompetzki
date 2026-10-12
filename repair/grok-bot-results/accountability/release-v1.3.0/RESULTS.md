# Release v1.3.0: independent accountability (Grok Bot, Linux box)
Tag `v1.3.0` is a lightweight tag. `git ls-remote --tags` returns `7c6f518173c9502e0cbfc3ac305223de7e534ebe refs/tags/v1.3.0` with no `^{}` entry. The `^{commit}` dereference is the same commit, which is contained in origin/codex/exact-release-repair. The API `target_commitish` is also 7c6f518. **MATCH.**
**Mismatches found: none.** The shipped Windows native judge was rebuilt, and the release discloses this; see §1.

## 1. Assets: anonymous API download (raw/assets/)
| Asset | Size (API = local) | sha256 local = API digest = SHA256SUMS.txt | Extra claim |
|---|---|---|---|
| Abschluss-1.3-source.zip | 180764033 | 13d936df…2f85f, all three agree | claimed 13d936df… **MATCH** |
| Abschluss-1.3-windows-x64.zip | 200651349 | f1c1fc74…047ab, all three agree | claimed f1c1fc74… **MATCH** |
| browser-gate-correction-public.zip | 85525 | 57216676…6773, all three agree | contents byte-identical to repo `repair/browser-gate-correction/` at the tag |
| grok-composition-proof-public.zip | 99104 | 97b0ae20…03d9, all three agree | 35 files (listed only, not exercised) |
| SOURCE-CLOSURE-1.3.0.json | 5070 | 2511586e…0642, all three agree | |
| SHA256SUMS.txt | 485 | 06979781…d811 (API only; it does not list itself) | |

Windows ZIP: 443 files (raw/assets/windows-zip-contents.sha256), matching the closure's claimed `candidate_file_count` 443. Its internal MANIFEST.sha256 has 442 entries and `sha256sum -c` reports 0 failures. `pompetzki.exe` 957366e6… matches the closure `console_sha256`, and `pompetzki-w.exe` d6c6e22a… matches `window_sha256`. `judge/judge-v5.pmp` is 4d936cb8…, the same as the source.
**Note (disclosed, verified):** the shipped `judge/judge-v5-windows.exe` is 7e3d2f0c…. That is not byte-identical to the tested/committed b9e2ed07…. The package's `provenance/native-rebuild-comparison.json` declares `allocated_sections_equal: true`. I parsed both PE files myself. .text, .data, .rdata, .idata and .bss have identical size, address and sha256. Only the PE header timestamp differs (1791774110 vs 1791770916). **CLAIM HOLDS.**

## 2. Source selection: source ZIP vs git tree at 7c6f518 (raw/assets/cmp-summary.txt, zip-only.txt, git-only.txt)
- The ZIP has 1949 files and git has 3285. 1782 paths are common. **1 byte difference:** `RELEASE-1.3.0.md`. The ZIP copy equals git `RELEASE-1.3.0-final.md`, while git's `RELEASE-1.3.0.md` is an older draft without the Book v6 and matrix-batch paragraphs. This is a naming difference, not hidden content.
- 167 paths are ZIP-only, the result of re-rooting: `runtime/` is the runtime-v2 copy and `cockpit/`, `vendor/` and the whitelist come from packaging.
- 1503 paths are git-only and excluded: `results/` stages, `repair/book-v4`, `repair/book-v5`, `repair/browser-gate-correction` (shipped as a separate asset), `repair/runtime` (the old SIGFPE runtime), `repair/math-workbench-corrected`, `judge/mut`, `bin/linux`, judge v3/v4, and the docs.
- Selected components:

| Component | ZIP path | sha256 | Verdict |
|---|---|---|---|
| runtime | runtime/source/pompetzki.asm | 2329d3c9… = repair/runtime-v2 (old SIGFPE runtime 778a2710… **not shipped**) | runtime-v2 selected |
| judge-v5 pmp / rkt | judge/judge-v5.pmp, .rkt | 4d936cb8… / c63bd449… | v5 selected; no judge-v3/v4 in ZIP |
| Book v6 checker | repair/book-v6/verified-book-check.rkt | 9215daae… | MATCH |
| matrix engine | repair/math-workbench-v2/engine.rkt | 99084a40… (corrected engine 2cf5af81… not shipped) | MATCH |
| strx | repair/libraries/strx/strx.pmp | 05b773ce… | fixed version |
| browser-gate-correction | separate release asset (not in source ZIP) | 57216676… | supplemental wrapper. Its README says it does not replace judge-v5. |
- All 17 `component_source_sha256` entries in SOURCE-CLOSURE match my ZIP extraction (raw/assets/closure-component-check.txt). **No old defective component ships as the default.**

## 3. Built from the extracted source ZIP on Linux
`runtime/build-interpreter.py --target linux` produced pompetzki aafc0b36…. `judge/native-v5/portable/build-native.py --target linux` produced judge-v5-linux 92f9a772…. Raw hashes differ from earlier builds because the build paths are embedded. After `objcopy --strip-all`, the runtime equals my earlier runtime-v2 build and the judge equals the committed judge-v5-linux. This is a separate finite byte comparison.

| Claim | Command | Output | Outcome |
|---|---|---|---|
| driver.py defect controls | `driver.py --interp built-rt --judge zip/judge-v5.pmp --strx zip/strx.pmp` | `FAILURES=0 of 10`: false registry REJECT exit 1; literal INT64_MIN `-9223372036854775808` exit 0; strx `3 97 0 98 32 0 98` | PASS |
| INT64_MIN div / mod -1 | runtime-v2 d1/d2 | `-9223372036854775808` exit 0 / `0` exit 0 (no SIGFPE) | PASS |
| False registry, 3 routes | native / interp / racket | REJECT `initial registry entry differs`, exit 1 on all three | PASS |
| Canonical REG0, plus every number padded with 3/13/64 zeros | 3 routes | ACCEPT exit 0 on all three, for all four files | PASS |
| R = 999999999999 (12 significant) | 3 routes | REJECT `more than 706 entries` (value error, not a parse error) | PASS |
| R = 1000000000000 (13 significant) | 3 routes | REJECT `more than 12 significant digits` | PASS (v5 chose: unlimited leading zeros, at most 12 significant digits) |
| R = 21 zeros then 706 | 3 routes | ACCEPT | PASS |
| validation-v5 full lane (includes the 4,551-theorem replay case) | `run-validation-v2.py --lane full --interpreted-lane fast` | 644 runs: native 254/254, racket 254/254, interpreted 136/136, 0 timeouts, 303 s | PASS (Linux rerun of the release's 254-per-route claim) |
| Book v6 genuine native post+check | `verified-book-post.rkt --bundle <ZIP-built bundle>` | exit 0, ACCEPT/ACCEPT, `verified-book-v6` CHECK OK | PASS |
| Book v6 genuine --interpreted post+check | same + `--interpreted` | exit 0, CHECK OK | PASS |
| Book v6 extra judge-runs file | check | `judge-runs contains missing, duplicate or unreferenced artifacts` exit 1 | REJECTED (gap closed) |
| Book v6 empty runs/inputs, extra top file/dir, nested dir, symlink, missing file | check | all exit 1 with specific diagnostics | REJECTED |
| v5 forgery dirs (consistent false proof, rehash, orphan N, …) | check, bundle-453 (same judge sources) | `rerun differs from stored verdict`, etc.; all 11 exit 1 | REJECTED |
| Same forgery dirs vs the ZIP-built bundle | check | `metadata artifact hash differs from the selected bundle tool` | REJECTED (by tool hash first, a confounded but correct refusal) |
| Matrix mixed batch, racket source route | `matrix.py` on ZIP engine.rkt | 18 records, 11 per-item rejections, 7 exact oracle answers; corrected engine still fails the whole batch (`hash-ref: contract violation`) | PASS / defect reproduced on old |
| Matrix bot corpus | `bot-matrix-validation/verify.py --engine racket engine.rkt` | `cases 429, identity_checks 7288, jobs 3754, failures 0` | PASS (matches release) |
| Gate: false registry | browser-gate-correction `judge-gated.sh` (default judge `../../judge/judge-v5.pmp`, runtime-v2) | `REJECT registry 0 formula`, exit 1, proof judge not started; gate.py same | PASS |
| Gate: canonical REG0, pad 3/13/64 | same | `GATE 706 706` then judge-v5 ACCEPT exit 0, all four. **Gate and downstream judge agree**, unlike d70b551+judge-v3 at pad13. | PASS |
| Gate: 13 significant digits in R | same | gate `REJECT registry parse`, exit 1, judge not started; standalone judge-v5 also REJECTs | PASS (agree) |
| Gate: REG0 prefix 10 / 705 | same | `GATE 10 706` / `GATE 705 706` + ACCEPT; standalone native judge-v5 also ACCEPTs | consistent (the prefix is accepted by design) |
d70b551 is kept as historical only (see gate-d70b551/).

## 4. Release-note claims vs receipts / my runs
| Claim (RELEASE-1.3.0.md) | Source | Actual | Match |
|---|---|---|---|
| 898 v5 runs = 254 ×3 + 136 interpreted | judge/validation-v5/actual-fast-run (receipt shows the 136-case fast lane only) + my Linux full run | my run: 254/254/254-equivalent (native and racket 254, interp 136). Windows native 254 is not in a receipt I found. | Linux part **verified by my run**; Windows 254 **not verified** |
| 4,551 theorems, 4,373 Proved, 178 Qualified, 139,194 steps | book-v6/PUBLIC-RUN-RESULTS.json `full_replay` | receipt values identical; my validation full lane ACCEPTs the replay file on native+racket | receipt MATCH; Book posting replay of 4,551 **SKIPPED** (>10 min) |
| Book v6 4 posting / 5 checker / 2 adversarial / 29 review | PUBLIC-RUN-RESULTS.json | (4,4) (5,5) (2,2) (29,29) | MATCH (receipt); my own 22 attacks agree in kind |
| Matrix corpus 429 / 7,288 / 3,754 / 0 failures | my verify.py rerun | 429 / 7288 / 3754 / 0 | **MATCH (rerun)** |
| 179 inconsistent systems | outputs | 358 `"inconsistent"` occurrences, consistent with 179 × 2 fields | likely, not exactly verified |
| Matrix batch recovery 24 checks per route; 76 Grok Bot engine checks | not rerun with their driver | my own batch test PASS (source route) | not verified as stated |
| Linux runtime harness 1,493/0; Windows 740 and 918 | not rerun this round (verified 1493/1493 in followup-52e4a28 on the same runtime-v2 source) | — | carried forward, not rerun |
| Rocq: 7 + 5 lemmas, closed assumptions | not run | — | **NOT VERIFIED** |
| Console/window interpreter hashes; 443 files; 17 declared sources | SOURCE-CLOSURE + my hashing | all match | MATCH |
| Shipped native judge = tested build | native-rebuild-comparison.json | rebuilt binary; sections identical, timestamp differs (my PE parse) | MATCH as disclosed |

Finite tests do NOT establish executable/Gallina correspondence, parser denotation, compiler preservation or shipped-byte correspondence.
