# AG12 (Antigravity, Area-51): set.mm axioms and definitions mapped to the judge's registry, for lane L5

Rules: `C:\ClaudeOutput\pompetzki\lanes\RULES-ROUND2-2026-10-09.md`.

**Context.**
- Lane L5 (`C:\ClaudeOutput\pompetzki\lanes\L5\`, read-only for you) translates Metamath set.mm into JDG1 files for the pmp judge.
- The judge's registry is the 677 entries AX0 (7 ZF axioms) ++ DEF0 (670 definitions) of `C:\ClaudeOutput\pompetzki\forcing-src\general\RpInit.v`. The symbol table and formula syntax are in `Syn.v` and `Ax.v` in the same folder.
- set.mm is at `C:\ClaudeOutput\formalization-toolchain-20260924\libraries\metamath-set-mm-28167ed89a49\set.mm`.
- Lane AG8 (`lanes\AG8\`) listed 50,912 assertions. 5,757 of its theorems are free of class abstractions.

**Task.** In Racket, with exact integers:
1. For every set.mm `ax-*` and `df-*` used by at least one of the 5,757 class-free theorems, find the registry entry that expresses the same axiom or definition, if there is one. Record:
   - set.mm label;
   - set.mm statement;
   - registry index and name;
   - registry formula, printed;
   - match class: identical up to variable renaming / equivalent by a short derivation (name it) / no counterpart.
2. For each "no counterpart", give the exact formula a new registry definition would need, with arity.
3. Coverage: how many of the 5,757 class-free theorems use only labels that have a counterpart, listed in set.mm order.

**Output:** in `C:\ClaudeOutput\pompetzki\lanes\AG12-setmm-registry\`:
- `MAP.tsv`;
- `COVERAGE.tsv`;
- RESULTS.md and STATUS.txt.

L5 reads them.
