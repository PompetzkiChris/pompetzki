# Follow-up: codex/exact-release-repair at 52e4a28 + Linux runtime lane recheck

Run 2026-10-11 ~21:40-21:50 EDT on the Linux box. Fresh checkout `/workspace/acct-52e4`, HEAD `52e4a28ecf47c9e06b230d975c04a174272a3cdf`.

52e4a28 adds `judge/portable-interpreter/` (source sha256 `778a2710...89db`, **identical** to `repair/runtime/source/pompetzki.asm`), workbench and proof-build files. It does not change `judge-v4.pmp`, `repair/runtime/source/pompetzki.asm`, or strx.

Builds (all exit 0; `raw/small-captures.txt`): `build-interpreter.py --target linux` -> `00f3e9a6...1baf`; `nasm -DLINUX` + `ld` of repair runtime -> `b8725cbd...7fcc`; native judge-v4 -> `ece313c9...c48a`.

| Claim | Command | Actual output | Verified outcome |
|---|---|---|---|
| 52e4a28 fixes (a)(b)(c) | `driver.py` with {portable interp, repair runtime} x {native judge-v4, judge-v4.pmp}, strx at 52e4a28 | `FAILURES=0 of 10`, exit 0, all four | PASS (no regression vs 63f45bb) |
| judge-v4.rkt rejects forged registry | `racket judge/judge-v4.rkt inputs/a1...` | `REJECT initial registry 0: entry differs from canonical REG0`, exit 1 | PASS |
| Lane: original 1491/1493 | `run_tests.py <rebuilt original> strx.pmp WORK` (copy in /workspace/acct-linuxcheck; also prebuilt `build/pompetzki-linux`) | `PASS=1491 FAIL=2`, exit 1; failures `div -9223372036854775808 -1` and `mod ... -1`, both `rc=-8` | CONFIRMED (rebuilt and prebuilt) |
| Lane: fixed 1493/1493 | same on `fixed/pompetzki.asm` build (and prebuilt `pompetzki-linux-fixed`) | `PASS=1493 FAIL=0`, exit 0 | CONFIRMED |
| INT64_MIN div -1 SIGFPE | `inputs/d1-min-div-neg1.pmp`, `d2-min-mod-neg1.pmp` | original lane build, **52e4a28 portable interp and repair runtime**: rc=-8 (SIGFPE), empty stdout/stderr. Lane fixed: `-9223372036854775808` / `0`, rc 0 | CONFIRMED; **the defect is still present at 52e4a28** (the lane fix is not on the branch) |
| Semantics note | `d3` (MIN mul -1), `d4` (0 sub MIN) | `-9223372036854775808`, rc 0 on all builds | word ops wrap mod 2^64; the lane's div fix matches that wrapping convention. It does not emit the "value left the 64-bit integers" refusal. Whether wrapping or refusal is intended for `div` is a design decision for the owner. |

`/workspace/pomp-linux` was not modified (`diff -rq` vs the copy: identical; builds written outside the tree).

Finite tests do NOT establish executable/Gallina correspondence.
