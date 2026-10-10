# Quickstart: Running the pmp Judges (Revision 2 — Post-Reboot Final)

This guide provides instructions for verifying JDG1 proof transcripts using both production judges on **Windows** and **Linux / WSL**.

Under the project release criteria (`RELEASE-DAY-ORDERS-2026-10-09.md` Rule 4), a derivation is valid **only when both independent judges ACCEPT the JDG1 file with identical counts**, and mutated copies reject with exit code 1.

---

## 1. Package File Layout and Binary Locations

All paths below are package-relative:

```text
pompetzki/
├── bin/
│   ├── windows/
│   │   ├── pompetzki.exe    (Windows x64 interpreter, SHA-256: ccf835920e...)
│   │   └── bookdesk.exe     (Book ledger desktop runner)
│   └── linux/
│       ├── pompetzki        (Linux x86-64 static ELF interpreter)
│       └── jdgchk           (Native Linux x86-64 ELF judge, SHA-256: 4d153bea47...)
├── src/
│   └── judge/
│       ├── judge-v3.pmp     (Primary judge in PmpCore assembly)
│       └── racket/
│           └── judge.rkt    (Clean-room reference judge in Racket)
└── data/
    └── certificates/
        ├── judge/
        │   └── replay-all.jdg (Pinned Cohen forcing replay, SHA-256: a202ed9949...)
        └── stage2/
            └── 01-numerals.jdg (Standard arithmetic numerals derivation)
```

---

## 2. Running on Windows (PowerShell)

Ensure working directory is the package root:

```powershell
Set-Location "C:\ClaudeOutput\pompetzki"
```

### 2.1 The pmp Judge (`judge-v3.pmp`)
```powershell
& ".\bin\windows\pompetzki.exe" ".\src\judge\judge-v3.pmp" ".\data\certificates\stage2\01-numerals.jdg"
```
**Real Output:**
```text
ACCEPT
registry entries at the start, theorems accepted, steps checked, registry entries at the end:
677
73
1679
750
```
- **Exit Code:** `0` on success (`judge-v3.pmp:16`).
- **Timing:** ~7.35 seconds on Intel Core i9 / AMD Ryzen workstation.

### 2.2 The Reference Racket Judge (`judge.rkt`)
Requires Racket v9.3+ on PATH or specified directly:
```powershell
& "C:\Program Files\Racket\racket.exe" ".\src\judge\racket\judge.rkt" ".\data\certificates\stage2\01-numerals.jdg"
```
**Real Output:**
```text
ACCEPT registry 677 theorems 73 steps 1679 final-registry 750
```
- **Exit Code:** `0` on success (`judge.rkt:488`).
- **Timing:** ~0.32 seconds.

---

## 3. Running on Linux / WSL (Bash)

Navigate to the package root and ensure execute permissions on Linux binaries:

```bash
cd /path/to/pompetzki
chmod +x bin/linux/pompetzki bin/linux/jdgchk
```

### 3.1 The Linux pmp Judge
```bash
./bin/linux/pompetzki src/judge/judge-v3.pmp data/certificates/stage2/01-numerals.jdg
```
**Output:**
```text
ACCEPT
registry entries at the start, theorems accepted, steps checked, registry entries at the end:
677
73
1679
750
```
- **Exit Code:** `0`.

### 3.2 The Linux Reference Racket Judge
```bash
racket src/judge/racket/judge.rkt data/certificates/stage2/01-numerals.jdg
```
**Output:**
```text
ACCEPT registry 677 theorems 73 steps 1679 final-registry 750
```
- **Exit Code:** `0`.

### 3.3 The Native Linux ELF Judge (`jdgchk`)
The standalone Linux binary directly consumes JDG1 data via standard input:
```bash
./bin/linux/jdgchk < data/certificates/stage2/01-numerals.jdg
```
- **Exit Code:** `0`.

---

## 4. Understanding the Execution Metrics

Both judges verify and output four synchronized counters (`judge-v3.pmp:19-20`, `judge.rkt:487`):

| Counter | Observed Value | Mathematical Meaning |
| :--- | :--- | :--- |
| **Initial Registry Entries** | `677` | Pure ZFC base theory: 7 axioms (`AX0`, `RpInitOk.v:28`) + 670 closed definitions (`DEF0`, `RpInitOk.v:29`). |
| **Theorems Accepted** | `73` | Sequence of theorems verified in this derivation batch (`Replay2.v:168-170`). |
| **Steps Checked** | `1679` | Individual proof steps executed across all 73 theorems (`Replay2.v:145-149`). |
| **Final Registry Entries** | `750` | $677 + 73 = 750$. Each accepted theorem enters the registry for subsequent citations (`Replay2.v:169`, `judge.rkt:477`). |

**Consensus Requirement:** A derivation is accepted iff both judges exit `0` with identical counts across all 4 metrics.

---

## 5. Negative Testing: Rejection of Mutants

To verify soundness and rule out vacuous checkers, mutated derivations must reject with exit code `1`.

### Example: Running a Mutated Derivation (`01-numerals-taut-goal.jdg`)
In this mutant, step 0 of theorem 0 has an invalid goal formula.

#### Windows pmp Execution:
```powershell
& ".\bin\windows\pompetzki.exe" ".\src\judge\judge-v3.pmp" ".\data\certificates\stage2\mut\01-numerals-taut-goal.jdg"
```
**Output:**
```text
REJECT
taut: not a tautology
theorem and step (counted from 0):
0
0
line 340: check zero failed: not the zero vector
```
- **Exit Code:** `1`.

#### Windows Racket Execution:
```powershell
& "C:\Program Files\Racket\racket.exe" ".\src\judge\racket\judge.rkt" ".\data\certificates\stage2\mut\01-numerals-taut-goal.jdg"
```
**Output:**
```text
REJECT theorem 0 step 0 (step T)
```
- **Exit Code:** `1`.

Both independent judges identify the exact failure location: **theorem 0, step 0 (`step T`)**.

---

## 6. Distinguishing Logical Rejection from Interpreter Resource Limits

The pmp interpreter enforces two concrete execution limits (`lanes/FINDINGS-pmp-interpreter-bounds-20261009.md`):

1. **Call Depth Bound:** Formulas nesting numerals $> 38$ produce `line 386: gosub: too deep`.
2. **Registry Memory Bound:** Cumulative final registries $> 1,091$ entries produce `LIMIT a memory block is full`.

**Diagnostic Table:**

| Outcome | Exit Code | Terminal Output | Meaning |
| :--- | :---: | :--- | :--- |
| **ACCEPT** | `0` | `ACCEPT ...` | The derivation is soundly verified. |
| **REJECT** | `1` | `REJECT ... theorem X step Y` | The derivation is mathematically invalid. |
| **RESOURCE LIMIT** | `1` | `LIMIT a memory block is full` / `gosub: too deep` | The interpreter hit an execution bound. *(The Racket judge accepts these files).* |

---

## 7. Clean Build Prerequisites and Compile Instructions

For users building from source:

### 7.1 Windows Interpreter (`pompetzki.exe`)
- **Prerequisites:** Netwide Assembler (`nasm` 2.16+), Microsoft Visual C++ Build Tools (`link.exe`).
- **Build Command:**
  ```powershell
  nasm -f win64 src\pmp-language\pompetzki.asm -o pompetzki.obj
  link /SUBSYSTEM:CONSOLE /ENTRY:start /LARGEADDRESSAWARE pompetzki.obj kernel32.lib /OUT:bin\windows\pompetzki.exe
  ```

### 7.2 Linux Static Interpreter (`pompetzki`)
- **Prerequisites:** `nasm`, GNU `ld` / `gcc`.
- **Build Command:**
  ```bash
  nasm -f elf64 src/pmp-language/pompetzki.asm -o pompetzki.o
  ld -s pompetzki.o -o bin/linux/pompetzki
  ```

### 7.3 Reference Judge (`judge.rkt`)
- **Prerequisites:** Racket v9.3+ [cs]. No compilation required; executed directly from source.

### 7.4 Formal Rocq Proofs
- **Prerequisites:** Rocq Prover 9.0+ / Coq 8.19+.
- **Verification Command:**
  ```bash
  coqc -Q forcing-src/general Cohen forcing-src/general/Replay3.v
  coqchk -silent -admit-opaque=false -o -Q forcing-src/general Cohen Cohen.Replay3
  ```
  Expected output: `Axioms: <none>`.

*(Note: Legacy interpreter build scripts emit auxiliary tools whose `.pmp` sources are omitted in the release; the core `pompetzki` interpreter builds cleanly as specified above).*
