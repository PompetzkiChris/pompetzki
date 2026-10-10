| file | pmp | pmp time | Racket | Racket time | Racket's count (registry, theorems, steps, final registry) |
|---|---|---:|---|---:|---|
| L7-4-omega-laws.jdg | ACCEPT, exit 0 | 46.0 s | ACCEPT, exit 0 | 0.6 s | 677, 102, 2360, 779 |
| L7-1-equality.jdg | ACCEPT, exit 0 | 117.8 s | ACCEPT, exit 0 | 0.5 s | 677, 98, 7057, 775 |
| L7-1-eqchain-pmp.jdg | ACCEPT, exit 0 | 137.9 s | ACCEPT, exit 0 | 0.7 s | 677, 40, 1720, 717 |
| L7-2-tautologies.jdg | ACCEPT, exit 0 | 20.7 s | ACCEPT, exit 0 | 0.6 s | 677, 17, 79, 694 |
| L7-2-direct-control.jdg | ACCEPT, exit 0 | 102.8 s | ACCEPT, exit 0 | 0.8 s | 677, 5, 5, 682 |
| L7-3-quantifiers.jdg | ACCEPT, exit 0 | 40.1 s | ACCEPT, exit 0 | 0.8 s | 677, 47, 10690, 724 |

sums over these files: pmp 465522 ms, Racket 4370 ms

| mutant | pmp | Racket | pmp: theorem step, reason | Racket: theorem step (rule) |
|---|---|---|---|---|
| mut/L7-4-omega-laws-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 101 6: the last line is not the statement renamed by sig | 101 6 (final: last line is not the statement) |
| mut/L7-4-omega-laws-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 14 10: exel: the side conditions of existential elimination fail | 14 10 (step L) |
| mut/L7-4-omega-laws-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 20 37: exi: the formula is not an existential introduction | 20 37 (step E) |
| mut/L7-4-omega-laws-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 14 4: leib: the formula is not Leibniz's law for the given formula | 14 4 (step Z) |
| mut/L7-4-omega-laws-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 20 42: mp: the second line is not an implication | 20 42 (step M) |
| mut/L7-4-omega-laws-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 101 7: the last line is not the statement renamed by sig | 101 7 (final: last line is not the statement) |
| mut/L7-4-omega-laws-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 26 13: taut: not a tautology | 26 13 (step T) |
| mut/L7-4-omega-laws-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 14 9: taut: not a tautology | 14 9 (step T) |
| mut/L7-4-omega-laws-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 101 7: the last line is not the statement renamed by sig | 101 7 (final: last line is not the statement) |
| mut/L7-4-omega-laws-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 14 1: spec: the line has no leading All to instantiate | 14 1 (step S) |
| mut/L7-1-equality-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 102: the last line is not the statement renamed by sig | 97 102 (final: last line is not the statement) |
| mut/L7-1-equality-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 2: leib: the formula is not Leibniz's law for the given formula | 0 2 (step Z) |
| mut/L7-1-equality-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 103: the last line is not the statement renamed by sig | 97 103 (final: last line is not the statement) |
| mut/L7-1-equality-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 7: taut: not a tautology | 11 7 (step T) |
| mut/L7-1-equality-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 1: taut: not a tautology | 0 1 (step T) |
| mut/L7-1-equality-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 103: the last line is not the statement renamed by sig | 97 103 (final: last line is not the statement) |
| mut/L7-1-equality-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 12 15: taut: not a tautology | 12 15 (step T) |
| mut/L7-1-eqchain-pmp-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 39 81: the last line is not the statement renamed by sig | 39 81 (final: last line is not the statement) |
| mut/L7-1-eqchain-pmp-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 2: leib: the formula is not Leibniz's law for the given formula | 0 2 (step Z) |
| mut/L7-1-eqchain-pmp-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 39 82: the last line is not the statement renamed by sig | 39 82 (final: last line is not the statement) |
| mut/L7-1-eqchain-pmp-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 1: taut: not a tautology | 0 1 (step T) |
| mut/L7-1-eqchain-pmp-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 39 82: the last line is not the statement renamed by sig | 39 82 (final: last line is not the statement) |
| mut/L7-2-direct-control-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 0: the theorem has no lines | 4 0 (final: no lines) |
| mut/L7-2-direct-control-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 1: the last line is not the statement renamed by sig | 4 1 (final: last line is not the statement) |
| mut/L7-2-direct-control-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0: taut: not a tautology | 0 0 (step T) |
| mut/L7-2-direct-control-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 1: the last line is not the statement renamed by sig | 4 1 (final: last line is not the statement) |
| mut/L7-2-tautologies-ax-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0: ax: not an axiom shape | 0 0 (step Y) |
| mut/L7-2-tautologies-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 16 1: the last line is not the statement renamed by sig | 16 1 (final: last line is not the statement) |
| mut/L7-2-tautologies-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 7: mp: the second line is not an implication | 1 7 (step M) |
| mut/L7-2-tautologies-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 16 2: the last line is not the statement renamed by sig | 16 2 (final: last line is not the statement) |
| mut/L7-2-tautologies-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 1: taut: not a tautology | 0 1 (step T) |
| mut/L7-2-tautologies-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 16 2: the last line is not the statement renamed by sig | 16 2 (final: last line is not the statement) |
| mut/L7-3-quantifiers-alli-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 28: alli: the side conditions of universal introduction fail | 0 28 (step H) |
| mut/L7-3-quantifiers-ax-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 5: ax: not an axiom shape | 0 5 (step Y) |
| mut/L7-3-quantifiers-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 46 103: the last line is not the statement renamed by sig | 46 103 (final: last line is not the statement) |
| mut/L7-3-quantifiers-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 25: exel: the side conditions of existential elimination fail | 0 25 (step L) |
| mut/L7-3-quantifiers-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 58: exi: the formula is not an existential introduction | 2 58 (step E) |
| mut/L7-3-quantifiers-gen-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 6: mp: the antecedent differs from the first line | 0 6 (step M) |
| mut/L7-3-quantifiers-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 6: mp: the second line is not an implication | 0 6 (step M) |
| mut/L7-3-quantifiers-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 46 104: the last line is not the statement renamed by sig | 46 104 (final: last line is not the statement) |
| mut/L7-3-quantifiers-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0: taut: not a tautology | 0 0 (step T) |
| mut/L7-3-quantifiers-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 46 104: the last line is not the statement renamed by sig | 46 104 (final: last line is not the statement) |

counts: files 6 (6 ACCEPT by both), mutants 42 (42 REJECT by both)
