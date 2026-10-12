# Accountability results: pompetzki v1.2.0 vs codex/exact-release-repair

Run on a Linux x86-64 box (not the Windows machine), 2026-10-11 ~21:30-21:50 EDT, by Grok Bot for Christopher Pompetzki.

## What was tested

| Item | Identity |
|---|---|
| Branch `codex/exact-release-repair` | initial source commit and remote HEAD at test time are both `63f45bbcaa88e370827d2dd2e95a6d422fb8c589` (no newer HEAD) |
| v1.2.0 release | `Abschluss-1.2-windows-x64.zip` sha256 `1cdf2868...ab86`, `Abschluss-1.2-math.zip` sha256 `5c904638...28dd`: both `OK` against the release's `SHA256SUMS.txt` |
| v1.2.0 judge-v3.pmp | sha256 `bf147194d415d0ab6991b5912c718c772f4bcb285ea027326fc5a108a81e6ce7` (byte-identical to the branch's `judge/judge-v3.pmp` and to the v2026.10.10 Linux zip) |
| v1.2.0 racket judge | `judge/racket/judge.rkt` sha256 `d6cf694c...79ca` |
| v1.2.0 strx | `tools/strx/strx.pmp` (top-level) sha256 `44328e84...900e`; its nested `tools/strx/lib/strx.pmp` = `05b773ce...702f` (identical to the branch's repaired `repair/libraries/strx/strx.pmp`) |
| Public Linux interpreter | **v1.2.0 has no Linux artifacts** (only Windows + math zips). The public Linux ELF used is `bin/linux/pompetzki` from release `v2026.10.10` (`pompetzki-linux-x64-20261010.zip`, `OK` against that release's SHA256SUMS), sha256 `414e976b...82a7`; identical to `bin/linux/pompetzki` at 63f45bb. Wine is unavailable, so `pompetzki.exe` of v1.2.0 was **not** executed. |
| Branch interpreter | `nasm -DLINUX -f elf64 repair/runtime/source/pompetzki.asm && ld` (NASM 2.16.03 built from source, GNU ld). The repair README only documents a Windows/MinGW build; the source's own `%ifdef LINUX` path was used. |
| Branch native judge | `python3 judge/native/portable/build-native.py --source judge/judge-v4.pmp --output ... --target linux` (Racket 8.14 CS minimal). Build receipt in `raw/build-native-judge-v4/` (generated .asm/.o/binary removed; hashes kept in its SHA256SUMS-build.txt). |

Observation: two builds at different paths gave different binary hashes (interpreter `caaec8e5...` vs `afa4471a...`; native judge `cdfdaf28...` vs `f6bb54b3...`), consistent with build-path strings embedded by the Linux toolchain. Byte-identical repeat builds were not shown on Linux here; behaviour was identical.

## Results (driver tables in `raw/driver-*.table.txt`, raw stdout/stderr/exit in `raw/*.capture.txt`)

| Claim | Command | Actual output | Verified outcome |
|---|---|---|---|
| (a) v1.2.0 accepts a forged initial registry `forall x, not(x=x)` (`a n q 0 0 0`) | `pompetzki judge-v3.pmp inputs/a1-false-registry-only.jdg` (and `a2`, which also derives the false formula as theorem 0 via `U 0`) | `ACCEPT` / `1 0 0 1`, exit 0; a2: `ACCEPT` `1 1 1 2`, exit 0 | **REPRODUCED** (v1.2.0 judge-v3.pmp on public Linux ELF; same result on repaired interpreter, so the defect is in the judge) |
| (a) v1.2.0 Racket judge same defect | `racket judge.rkt inputs/a1...jdg` | `ACCEPT registry 1 theorems 0 steps 0 final-registry 1`, exit 0; a2 `ACCEPT registry 1 theorems 1 steps 1 final-registry 2`, exit 0 | **REPRODUCED** |
| (a) branch v4 rejects it | `judge-v4-linux inputs/a1...jdg`; `pompetzki-repaired judge/judge-v4.pmp ...`; `racket judge/judge-v4.rkt ...` | `REJECT` / `initial registry entry differs from canonical REG0`, exit 1 (all three, a1 and a2); Racket: `REJECT initial registry 0: entry differs from canonical REG0`, exit 1 | **FIXED** |
| (a) control: canonical REG0 still accepted | same commands on `inputs/ctl-canonical-reg0.jdg` | `ACCEPT`, exit 0 (all judges; Racket v4 `ACCEPT registry 706 theorems 0 steps 0 final-registry 706`) | PASS |
| (b) public interpreter refuses literal INT64_MIN | `pompetzki inputs/b1-literal-min.pmp` (`set A const -9223372036854775808`) | `line 1: Menschenwerk: a value left the 64-bit integers. Nothing was rounded; the program stops.`, exit 1 | **REPRODUCED** on the public Linux ELF (v2026.10.10). Not run on v1.2.0's Windows exe (no Wine). |
| (b) calculated INT64_MIN works | `pompetzki inputs/b2-computed-min.pmp` (`-9223372036854775807 - 1`) | `-9223372036854775808`, exit 0 | REPRODUCED (asymmetry confirmed) |
| (b) branch parses INT64_MIN, still rejects out-of-range | repaired interpreter on b1..b5 | b1 `-9223372036854775808` exit 0; b3 `9223372036854775807` exit 0; b4 (`9223372036854775808`) and b5 (`-9223372036854775809`) overflow message, exit 1 | **FIXED**, bounds preserved |
| (c) v1.2.0 top-level tools/strx loses bytes after embedded NUL | `pompetzki c1-trim-nul.pmp` with v1.2.0 `tools/strx/strx.pmp`: SX_TRIM of bytes `32 97 0 98 32` | `3 97 0 0 32 0 98` (len 3 correct, but byte `98` replaced by `0`; input preserved) | **REPRODUCED** (content wrong after NUL; reported length is right for TRIM) |
| (c) same, SX_PAD_RIGHT of `0 97` to width 4 with `.` | `c2-pad-nul.pmp` | `4 0 0 0 0` (expected `4 0 97 46 46`) | **REPRODUCED** (everything after a leading NUL lost) |
| (c) branch strx | same with `repair/libraries/strx/strx.pmp` | c1 `3 97 0 98 32 0 98`; c2 `4 0 97 46 46` | **FIXED** (on both interpreters: the fix is in the library's `_len` bindings) |
| Driver summary | `driver.py` x4 | v1.2.0: `FAILURES=5 of 10` exit 1; branch native: `FAILURES=0 of 10` exit 0; branch judge-v4.pmp interpreted: `FAILURES=0 of 10` exit 0; v1.2.0 judge+strx on repaired interpreter: `FAILURES=4 of 10` (b fixed, a/c not) | consistent |
| Browser Grok Build conversation claims | WebFetch / curl of `https://grok.com/c/f249614d-b9e3-48e5-943b-e0b6e50daf6f` | HTTP 200, 357 KB app shell, title `Grok`, no conversation text (0 matches for INT64/REG0/strx) | **UNREADABLE** (private conversation needs sign-in); no claims extracted or checked |

Inputs were built from the JDG1 parser in `judge/racket/judge.rkt` (`a`=forall, `n`=not, `q i j`=equality of de Bruijn variables, list = count then items) and the pmp syntax in `repair/libraries/strx/strx-test.pmp`; no prior report was used as evidence.

## Limits

- **Finite tests do NOT establish executable/Gallina correspondence.** These 10 cases (plus controls) show behaviour on specific inputs only. They do not prove the native judge, the interpreter, or `judge-v4.pmp` implements the Rocq/Gallina `check_batch` checker, nor that the canonical-prefix soundness theorems apply to these bytes. That obligation remains open, as the branch README itself states.
- v1.2.0's Windows binaries were not executed; defect (b) was reproduced on the public Linux interpreter, (a) and (c) with the v1.2.0 files byte-for-byte.
- The branch's larger claimed suites (918 tool cases, 150 strx cases, 3,538 registry checks, 4,551-theorem replay) were not rerun here; the generators referenced in `repair/runtime/README.md` (`build-monolithic.py`, `oracles/`, `tests/`) are not present in the 63f45bb tree.
- No theorem statements or prior artifacts were changed; this directory only adds files.

## Rerun

```
cd <checkout>/repair/grok-bot-results/accountability
./rerun.sh                     # downloads+verifies releases, builds branch, runs driver (exit 0 iff branch passes)
python3 driver.py --interp PMP_INTERP --judge JUDGE(.pmp or native) --strx STRX.pmp [--rawdir DIR --label NAME]
sha256sum -c MANIFEST.sha256
```
