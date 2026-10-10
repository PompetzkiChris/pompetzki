# Quickstart for the public repository tree

Bound to public commit `fea61442a6665be6089bb137a553696162281654` of `PompetzkiChris/pompetzki`. Start in the repository root. This guide uses the actual `judge/`, `certificates/`, `bin/`, and `rocq/` paths. The historical package quickstart uses a different layout.

The small arithmetic example and its mutant were tested from independently downloaded pinned public bytes on 2026-10-10. Eight files were checked against the pinned manifest's SHA256, Git blob identities, byte counts, and local readback before execution. All eight runtime cases passed, each with a 30-second hard subprocess limit. No Theorem 29 replay was run during this validation.

## Start with the small positive and refusal cases

The positive file is `certificates/stage2-sigma1/out/01-numerals.jdg`; the mutant is `certificates/stage2-sigma1/out/mut/01-numerals-taut-goal.jdg`. The mutant is an expected refusal and must not be treated as a tool failure.

### Windows PowerShell

The interpreter is bundled. The independent Racket judge requires an installed Racket command on PATH; the validation used `C:\Program Files\Racket\racket.exe`, Racket 9.3 [cs]. Print each exit code immediately after its command.

```powershell
Set-Location .\judge
& ..\bin\windows\pompetzki.exe judge-v3.pmp ..\certificates\stage2-sigma1\out\01-numerals.jdg
$LASTEXITCODE
& ..\bin\windows\pompetzki.exe judge-v3.pmp ..\certificates\stage2-sigma1\out\mut\01-numerals-taut-goal.jdg
$LASTEXITCODE
& racket .\racket\judge.rkt ..\certificates\stage2-sigma1\out\01-numerals.jdg
$LASTEXITCODE
& racket .\racket\judge.rkt ..\certificates\stage2-sigma1\out\mut\01-numerals-taut-goal.jdg
$LASTEXITCODE
Set-Location ..
```

### Linux or WSL

Validation used Ubuntu-24.04 under WSL2 on x86-64. The Git tree stores the Linux binaries with mode `100644`, so give them execute permission. The following bounded commands use GNU `timeout`; each has a 27-second limit and a 1-second kill grace. The subshell returns to the repository root.

```bash
chmod +x bin/linux/pompetzki bin/linux/jdgchk
(
  cd judge || exit 2
  timeout -k 1s 27s ../bin/linux/pompetzki judge-v3.pmp ../certificates/stage2-sigma1/out/01-numerals.jdg
  printf 'pmp positive exit: %s\n' "$?"
  timeout -k 1s 27s ../bin/linux/pompetzki judge-v3.pmp ../certificates/stage2-sigma1/out/mut/01-numerals-taut-goal.jdg
  printf 'pmp mutant exit: %s\n' "$?"
  timeout -k 1s 27s ../bin/linux/jdgchk < ../certificates/stage2-sigma1/out/01-numerals.jdg
  printf 'native positive exit: %s\n' "$?"
  timeout -k 1s 27s ../bin/linux/jdgchk < ../certificates/stage2-sigma1/out/mut/01-numerals-taut-goal.jdg
  printf 'native mutant exit: %s\n' "$?"
)
```

### Recorded results of this validation

| Runtime | Positive verdict / exit | Mutant verdict / exit | Positive registry / theorems / steps / final registry | Mutant theorem / step |
| --- | --- | --- | --- | --- |
| Windows pmp | ACCEPT / 0 | REJECT / 1 | 677 / 73 / 1679 / 750 | 0 / 0 |
| Installed Racket 9.3 [cs] | ACCEPT / 0 | REJECT / 1 | 677 / 73 / 1679 / 750 | 0 / 0 |
| WSL Linux pmp | ACCEPT / 0 | REJECT / 1 | 677 / 73 / 1679 / 750 | 0 / 0 |
| WSL Linux native checker | ACCEPT / 0 | REJECT / 1 | 677 / 73 / 1679 / 750 | 0 / 0 |

The recorded table above summarizes the pinned-byte validation. The full local validation receipt records stdout, stderr, exact arguments, process IDs, timings, byte bindings, and dependency observations; it is an owner integration input and is not a file in this public tree. No case timed out. This establishes these two finite files on these four runtimes; it does not establish a whole-stage proof or whole-release acceptance.

## Larger recorded replay: Theorem 29

The pinned README records acceptance of `certificates/theorem29/replay-all.jdg`: initial registry 706, 4,551 theorems, 139,194 steps, final registry 5,257. This larger replay was not downloaded or run for the small-case validation. The following paths match the pinned public tree; the commands are retained as the larger recorded example.

Windows, beginning at the repository root:

```powershell
Set-Location .\judge
& ..\bin\windows\pompetzki.exe judge-v3.pmp ..\certificates\theorem29\replay-all.jdg
$LASTEXITCODE
& racket .\racket\judge.rkt ..\certificates\theorem29\replay-all.jdg
$LASTEXITCODE
Set-Location ..
```

Linux, after granting the execute permissions above:

```bash
(
  cd judge || exit 2
  ../bin/linux/pompetzki judge-v3.pmp ../certificates/theorem29/replay-all.jdg
  printf 'pmp exit: %s\n' "$?"
  racket racket/judge.rkt ../certificates/theorem29/replay-all.jdg
  printf 'Racket exit: %s\n' "$?"
  ../bin/linux/jdgchk < ../certificates/theorem29/replay-all.jdg
  printf 'native exit: %s\n' "$?"
)
```

The Linux Racket command requires Racket installed on Linux; Linux Racket was not exercised in this small-case validation. An explicit `REJECT` is a refused derivation. Stops such as `gosub: too deep` or `LIMIT a memory block is full` are resource stops. A Racket acceptance alongside a pmp resource stop does not establish a completed pmp replay. Retain and compare the current outputs, counts, and exit codes.

## Hashes and sources

From the repository root on Linux or WSL:

```bash
sha256sum -c MANIFEST.sha256
```

The pinned manifest has 1,256 rows. It excludes itself and `results/stage1-conservativity-CX3/MANIFEST.sha256` and `results/stage2-lrat-AG5/MANIFEST.sha256`. The small-case validation checked the eight downloaded files against their pinned manifest or manifest-object binding; it did not download or check every public file. Checksum success establishes listed bytes, not proof acceptance.

| Object | Actual repository path |
| --- | --- |
| pmp judge | `judge/judge-v3.pmp` |
| Independent Racket judge | `judge/racket/judge.rkt` |
| Rocq checker definition | `rocq/Replay2.v` |
| Rocq checker soundness | `rocq/Replay3.v` |
| Initial registry proof | `rocq/RpInitOk.v` |
| JDG1 format | `docs/JDG1-FORMAT.md` |
| Soundness documentation | `docs/SOUNDNESS.md` |
| Recorded receipts | `docs/RECEIPTS.md` |

The public tree contains no `.asm` files. This guide supplies no build command from an absent assembly source or unvalidated Rocq build recipe. The public repository and release `408490141`, an unpublished draft/prerelease package set, have distinct scopes. Neither this finite runtime check nor repository publication establishes completion of the ten-stage objective.
