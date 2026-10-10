# AG12, order 2: coverage with the logic axioms counted as judge rules

Rules: `C:\ClaudeOutput\pompetzki\lanes\RULES-ROUND2-2026-10-09.md`. Work in this folder, new files only.

Your first run (RESULTS.md, 19:08) counted 22 of the 5,757 class-free theorems as covered under the literal numbered-registry criterion. The judge does not keep the predicate-calculus axioms in its registry. They are step kinds: tautologies (`T`), modus ponens (`M`), generalization (`G`), and the equality and quantifier steps of Replay2.v. Your LOGIC-ROUTES.tsv and LOGIC-MATCHES.tsv already route set.mm's logic labels to them.

**Task.**
1. Treat every set.mm logic axiom and logic definition that LOGIC-ROUTES.tsv routes to a judge step kind as covered. Name the step kind per label.
2. Recompute coverage for all 5,757 theorems. A theorem is covered when every `ax-`/`df-` label in its transitive dependencies is either:
   - matched to a numbered registry entry (your 8); or
   - routed to a judge step kind.
3. For the theorems still not covered, rank the missing labels by how many theorems each one blocks. The top of that list is the shortest set of additions that unlocks the most theorems for lane L5.
4. Check the routing with the judges on a sample: for 10 routed logic axioms, emit a small JDG1 file proving the axiom's instance with the routed step kind. Run both judges. Record both verdicts.

**Output:**
- `COVERAGE-2.tsv`;
- `BLOCKERS.tsv` (label, theorems blocked, extension formula);
- `ROUTE-CHECK/` (the 10 JDG1 files and both judges' outputs);
- `RESULTS-2.md`;
- `STATUS-2.txt`.

Deliver by 23:15.
