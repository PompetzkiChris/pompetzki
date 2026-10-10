# AG5 Results: LRAT Certificate Corpus for Lane L2D

**Execution Date / Time**: `2026-10-09T20:23:15-04:00`  
**Host Machine**: Area-51  
**Operating System**: Windows 11  
**Racket Version**: Welcome to Racket v9.3 [cs]  
**SAT Solver**: CaDiCaL (Lean v4.28.0 toolchain, `~/.elan/toolchains/leanprover--lean4---v4.28.0/bin/cadical.exe`)  
**Checker**: `C:\ClaudeOutput\pompetzki\lanes\AG5\check-lrat.rkt` (pure Racket exact-integer checker)  
**Consumer**: Lane L2D (`lrat-v4.rkt` emitting JDG1 files)  
**Judges**:
- Native judge: `C:\ClaudeOutput\pompetzki\pompetzki.exe judge-v3.pmp`
- Racket judge: `"C:\Program Files\Racket\racket.exe" racket\judge.rkt`

---

## 1. Corpus Summary Numbers

- **Total CNF instances generated**: 35
- **Total LRAT certificates produced**: 35
- **Total CNF variables across corpus**: 623
- **Total CNF clauses across corpus**: 2999
- **Total LRAT proof steps checked**: 2673
- **Total addition steps (RUP derivations)**: 2133
- **Total deletion steps (clause garbage collection)**: 540
- **Racket LRAT Checker Verdict**: 35 ACCEPT, 0 REJECT, 0 LIMIT
- **Negative Mutant Robustness**: 9 / 9 REJECTED (0 accepted)
- **Two-Judge End-to-End Verification on L2D Emitted JDG1 Files**:
  - `php-2-1.jdg`: `pompetzki.exe judge-v3.pmp` ACCEPT, `judge.rkt` ACCEPT
  - `tseitin-c3.jdg`: `pompetzki.exe judge-v3.pmp` ACCEPT, `judge.rkt` ACCEPT
  - `rand3-v15-s101.jdg`: `pompetzki.exe judge-v3.pmp` ACCEPT, `judge.rkt` ACCEPT

---

## 2. Complete Corpus Verification Table

All timings in exact integer milliseconds (`(current-milliseconds)`).

| Family | Instance Name | Vars | Clauses | Total Steps | Additions | Deletions | CaDiCaL (ms) | Checker (ms) | Checker Verdict |
|---|---|---|---|---|---|---|---|---|---|
| **Pigeonhole** | `php-2-1` | 2 | 3 | 1 | 1 | 0 | 0 | 0 | **ACCEPT** |
| **Pigeonhole** | `php-3-2` | 6 | 9 | 7 | 7 | 0 | 0 | 0 | **ACCEPT** |
| **Pigeonhole** | `php-4-3` | 12 | 22 | 15 | 15 | 0 | 0 | 0 | **ACCEPT** |
| **Pigeonhole** | `php-5-4` | 20 | 45 | 55 | 48 | 7 | 0 | 0 | **ACCEPT** |
| **Pigeonhole** | `php-6-5` | 30 | 81 | 193 | 156 | 37 | 0 | 2 | **ACCEPT** |
| **Pigeonhole** | `php-7-6` | 42 | 133 | 1426 | 1099 | 327 | 0 | 15 | **ACCEPT** |
| **Tseitin** | `tseitin-c3` | 3 | 6 | 4 | 4 | 0 | 0 | 0 | **ACCEPT** |
| **Tseitin** | `tseitin-c5` | 5 | 10 | 6 | 6 | 0 | 0 | 0 | **ACCEPT** |
| **Tseitin** | `tseitin-c7` | 7 | 14 | 8 | 8 | 0 | 0 | 1 | **ACCEPT** |
| **Tseitin** | `tseitin-k4` | 6 | 16 | 14 | 12 | 2 | 0 | 0 | **ACCEPT** |
| **Tseitin** | `tseitin-k33` | 9 | 24 | 30 | 24 | 6 | 0 | 0 | **ACCEPT** |
| **Tseitin** | `tseitin-prism3` | 9 | 24 | 25 | 19 | 6 | 0 | 0 | **ACCEPT** |
| **Tseitin** | `tseitin-petersen` | 15 | 40 | 100 | 69 | 31 | 0 | 1 | **ACCEPT** |
| **Tseitin** | `tseitin-ladder3` | 7 | 16 | 9 | 9 | 0 | 0 | 0 | **ACCEPT** |
| **Tseitin** | `tseitin-ladder4` | 10 | 24 | 13 | 12 | 1 | 0 | 1 | **ACCEPT** |
| **Tseitin** | `tseitin-wheel4` | 8 | 24 | 34 | 24 | 10 | 0 | 1 | **ACCEPT** |
| **Tseitin** | `tseitin-wheel5` | 10 | 36 | 76 | 48 | 28 | 0 | 8 | **ACCEPT** |
| **Tseitin** | `tseitin-cube` | 12 | 32 | 50 | 36 | 14 | 0 | 1 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v15-s101` | 15 | 75 | 17 | 12 | 5 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v15-s103` | 15 | 75 | 13 | 11 | 2 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v20-s201` | 20 | 100 | 28 | 22 | 6 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v20-s203` | 20 | 100 | 25 | 21 | 4 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v20-s205` | 20 | 100 | 24 | 19 | 5 | 426 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v25-s251` | 25 | 125 | 32 | 25 | 7 | 0 | 1 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v25-s252` | 25 | 125 | 32 | 27 | 5 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v25-s253` | 25 | 125 | 37 | 32 | 5 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v30-s301` | 30 | 150 | 50 | 42 | 8 | 0 | 2 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v30-s302` | 30 | 150 | 42 | 34 | 8 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v30-s303` | 30 | 150 | 38 | 34 | 4 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v35-s351` | 35 | 175 | 54 | 44 | 10 | 0 | 1 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v35-s352` | 35 | 175 | 52 | 42 | 10 | 0 | 0 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v40-s401` | 40 | 200 | 48 | 41 | 7 | 0 | 2 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v40-s402` | 40 | 200 | 69 | 59 | 10 | 0 | 2 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v50-s501` | 50 | 250 | 77 | 66 | 11 | 0 | 1 | **ACCEPT** |
| **Random 3-CNF** | `rand3-v50-s502` | 50 | 250 | 119 | 97 | 22 | 0 | 1 | **ACCEPT** |

---

## 3. Negative Mutant Test Suite Results

Base instance: `php-3-2` (6 variables, 9 clauses, 7 LRAT steps).

| Mutant ID | Mutation Injected | Expected | Actual | Specific Diagnostic Message |
|---|---|---|---|---|
| `mutant-1-wrong-hint` | Substitute valid hint with unrelated clause 999 | REJECT | **REJECT** | `check-lrat: Step 10: Hint clause 999 not found in DB` |
| `mutant-2-missing-conflict-hint` | Drop conflict hint from step | REJECT | **REJECT** | `check-lrat: Step 10: Hints did not produce a conflict` |
| `mutant-3-flipped-literal` | Flip polarity of literal in derived clause | REJECT | **REJECT** | `check-lrat: Step 10: Hint clause 8 has 2 non-falsified literals (expected <= 1)` |
| `mutant-4-non-increasing-id` | Non-monotonic clause ID sequence (9 <= 10) | REJECT | **REJECT** | `check-lrat: Clause ID not strictly increasing: 9 <= 10` |
| `mutant-5-use-deleted-clause` | Delete clause 1, then use clause 1 as hint | REJECT | **REJECT** | `check-lrat: Step 10: Hint clause 1 not found in DB` |
| `mutant-6-truncated-before-empty` | Truncate proof before empty clause | REJECT | **REJECT** | `Proof ended without deriving empty clause` |
| `mutant-7-non-empty-final-clause` | Add literal to final step (no empty clause) | REJECT | **REJECT** | `Proof ended without deriving empty clause` |
| `mutant-8-nonexistent-hint` | Substitute hint with non-existent ID 99999 | REJECT | **REJECT** | `check-lrat: Step 10: Hint clause 99999 not found in DB` |
| `mutant-9-non-unit-hint` | Hint with multiple open literals inserted | REJECT | **REJECT** | `check-lrat: Step 10: Hint clause 1 has 2 non-falsified literals (expected <= 1)` |

---

## 4. Two-Judge Verification Receipts

Derivations emitted using Lane L2D's emitter (`C:\ClaudeOutput\pompetzki\lanes\L2D\lrat-v4.rkt`) from the AG5 corpus:

```
Instance 1: php-2-1.jdg
  pompetzki.exe judge-v3.pmp:
    ACCEPT
    registry entries at the start, theorems accepted, steps checked, registry entries at the end:
    677, 12, 191, 689
  racket\judge.rkt:
    ACCEPT registry 677 theorems 12 steps 191 final-registry 689

Instance 2: tseitin-c3.jdg
  pompetzki.exe judge-v3.pmp:
    ACCEPT
    registry entries at the start, theorems accepted, steps checked, registry entries at the end:
    677, 12, 229, 689
  racket\judge.rkt:
    ACCEPT registry 677 theorems 12 steps 229 final-registry 689

Instance 3: rand3-v15-s101.jdg
  pompetzki.exe judge-v3.pmp:
    ACCEPT
    registry entries at the start, theorems accepted, steps checked, registry entries at the end:
    677, 12, 828, 689
  racket\judge.rkt:
    ACCEPT registry 677 theorems 12 steps 828 final-registry 689
```

Both judges agree on all verdicts across all evaluated instances.
