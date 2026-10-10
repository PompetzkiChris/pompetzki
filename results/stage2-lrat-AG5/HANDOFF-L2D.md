# AG5 to Lane L2D: LRAT Certificate Corpus Integration Handoff

**Timestamp**: 2026-10-09T20:23:15-04:00  
**Author**: Antigravity AG5  
**Consumer**: Lane L2D (Derived rules as JDG emitters: LRAT)

---

## 1. Overview and Corpus Summary

AG5 has produced and verified a complete corpus of 35 unsatisfiable CNFs and their corresponding CaDiCaL LRAT refutation certificates for lane L2D. Every certificate in this corpus has been verified by the standalone Racket LRAT checker (`check-lrat.rkt`) using exact integer arithmetic.

The corpus covers all three mandated families:
1. **Pigeonhole Formulas**: $\text{PHP}(n+1, n)$ for all $n \in \{1, 2, 3, 4, 5, 6\}$ (6 instances).
2. **Tseitin Formulas**: Parity contradiction formulas over 12 diverse graph topologies with odd total charge (12 instances: cycles $C_3, C_5, C_7$, complete graph $K_4$, complete bipartite $K_{3,3}$, triangular prism, Petersen graph, ladders $L_3, L_4$, wheel graphs $W_4, W_5$, and 3-cube $Q_3$).
3. **Random 3-CNF at Ratio 5**: Satisfiability threshold refutations across 15, 20, 25, 30, 35, 40, and 50 variables (17 distinct instances).

All files, certificates, and check receipts are indexed in `C:\ClaudeOutput\pompetzki\lanes\AG5\INDEX.tsv` and cryptographic checksums are provided in `C:\ClaudeOutput\pompetzki\lanes\AG5\MANIFEST.sha256`.

---

## 2. Directory Layout

- **CNF Sources**: `C:\ClaudeOutput\pompetzki\lanes\AG5\cnf\*.cnf` (DIMACS format)
- **LRAT Proofs**: `C:\ClaudeOutput\pompetzki\lanes\AG5\lrat\*.lrat` (Standard CaDiCaL linear RUP format)
- **Checker**: `C:\ClaudeOutput\pompetzki\lanes\AG5\check-lrat.rkt`
- **Mutant Suite**: `C:\ClaudeOutput\pompetzki\lanes\AG5\mutants\*.lrat` (9 adversarial mutants, all verified REJECTED)
- **Master Index**: `C:\ClaudeOutput\pompetzki\lanes\AG5\INDEX.tsv`
- **Manifest**: `C:\ClaudeOutput\pompetzki\lanes\AG5\MANIFEST.sha256`

---

## 3. How Lane L2D Emits and Judges Derivations

Lane L2D's emitter `lrat-v4.rkt` transforms any CNF and LRAT pair into a verified JDG1 derivation file:

```pwsh
# 1. Emit JDG1 derivation
& "C:\Program Files\Racket\racket.exe" "C:\ClaudeOutput\pompetzki\lanes\L2D\lrat-v4.rkt" emit `
    "C:\ClaudeOutput\pompetzki\lanes\AG5\cnf\<NAME>.cnf" `
    "C:\ClaudeOutput\pompetzki\lanes\AG5\lrat\<NAME>.lrat" `
    "C:\ClaudeOutput\pompetzki\lanes\AG5\<NAME>.jdg"

# 2. Run Native Judge (from judge directory)
cd "C:\ClaudeOutput\pompetzki\judge"
& "C:\ClaudeOutput\pompetzki\pompetzki.exe" judge-v3.pmp "C:\ClaudeOutput\pompetzki\lanes\AG5\<NAME>.jdg"

# 3. Run Racket Judge (from judge directory)
& "C:\Program Files\Racket\racket.exe" racket\judge.rkt "C:\ClaudeOutput\pompetzki\lanes\AG5\<NAME>.jdg"
```

---

## 4. End-to-End Integration Receipts

Representative instances from each family were emitted using `lrat-v4.rkt` and evaluated against both judges:

### Instance 1: Pigeonhole `php-2-1`
- **CNF**: 2 variables, 3 clauses
- **LRAT**: 1 addition step, 3 hints
- **L2D Derivation**: `php-2-1.jdg` (12 theorems, 191 steps, sha256 `356bc4d51e294305d69707541f1706b56196f4a84c267dbb6c513aefc5295334`)
- **Mutant Robustness**: 14/14 internal L2D mutants REJECTED
- **Native Judge (`pompetzki.exe judge-v3.pmp`)**: `ACCEPT` (677 initial registry, 12 theorems, 191 steps, 689 final registry)
- **Racket Judge (`racket\judge.rkt`)**: `ACCEPT registry 677 theorems 12 steps 191 final-registry 689`

### Instance 2: Tseitin Cycle `tseitin-c3`
- **CNF**: 3 variables, 6 clauses
- **LRAT**: 4 addition steps, 10 hints
- **L2D Derivation**: `tseitin-c3.jdg` (12 theorems, 229 steps, sha256 `93bc93f8b1b84eb19c4d57b6ca36551b0a1387e9a3ebd2c4ab02ec815466d5ca`)
- **Mutant Robustness**: 14/14 internal L2D mutants REJECTED
- **Native Judge (`pompetzki.exe judge-v3.pmp`)**: `ACCEPT` (677 initial registry, 12 theorems, 229 steps, 689 final registry)
- **Racket Judge (`racket\judge.rkt`)**: `ACCEPT registry 677 theorems 12 steps 229 final-registry 689`

### Instance 3: Random 3-CNF `rand3-v15-s101`
- **CNF**: 15 variables, 75 clauses
- **LRAT**: 12 addition steps, 39 hints
- **L2D Derivation**: `rand3-v15-s101.jdg` (12 theorems, 828 steps, sha256 `0c001258c3ba67cdbb05097fac185cc54788ca7a8a6be4da149d1e3731eb7994`)
- **Mutant Robustness**: 14/14 internal L2D mutants REJECTED
- **Native Judge (`pompetzki.exe judge-v3.pmp`)**: `ACCEPT` (677 initial registry, 12 theorems, 828 steps, 689 final registry)
- **Racket Judge (`racket\judge.rkt`)**: `ACCEPT registry 677 theorems 12 steps 828 final-registry 689`

The entire corpus is ready for immediate consumption by Lane L2D.
