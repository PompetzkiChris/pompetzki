# G2 (Grok Build, Area-51): Farkas certificate corpus for lanes L7 and L2D

Rules: `C:\ClaudeOutput\pompetzki\lanes\RULES-ROUND2-2026-10-09.md`.

**Context.** Lane L7 (`C:\ClaudeOutput\pompetzki\lanes\L7\`) emits judge derivations for linear arithmetic from Farkas certificates. Lane L2D (`lanes\L2D\farkas-v1.rkt`) has a Farkas format. Both folders are read-only for you. Use L2D's format exactly; if the two lanes differ, produce both formats.

**Task.**
1. In Racket with exact rationals, write:
   - a generator of infeasible linear systems Ax ≤ b over Q, with their Farkas certificates y ≥ 0, yA = 0, yb < 0;
   - a separate, independent checker.
2. Build the corpus:
   - small dense systems: 2–12 variables, 3–40 constraints, coefficients in [-50, 50];
   - integer-infeasible-but-rationally-feasible cases, marked as such and with no certificate, as negative controls;
   - structured families: pigeonhole-style LP relaxations, cyclic inequality chains x1 < x2 < … < xk < x1, and transportation problems with total supply below total demand.
3. Find certificates by exact rational elimination (Fourier–Motzkin with multiplier tracking) or by an exact simplex. Never use floats.
4. Negative controls: 1,000 mutated certificates (sign flip, perturbed multiplier, dropped row), each rejected by the checker.
5. An `INDEX.tsv` per system: n vars, m rows, certificate path and sha256, bit size of the largest numerator and denominator.

**Output:** in `C:\ClaudeOutput\pompetzki\lanes\G2-farkas\`:
- the generator, the checker and the corpus;
- `INDEX.tsv`;
- RESULTS.md and STATUS.txt.
