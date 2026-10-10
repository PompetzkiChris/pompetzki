# The pmp judge (Stage 1 of PMP-BUILDOUT-2026-10-09)

The posting checker of the Book, written in pmp: `check_batch` of `forcing-src/general/Replay2.v` (Theorem 29's replay checker, proved sound for `prov` in `Replay3.v`), as a pmp program that uses only statement forms with a Rocq semantics: PmpCore (`set const/add/sub/mul/peek/alloc`, `poke`, `text` literal, `when zero/nonzero/negative`, `goto`, `gosub`, `return`, `label`, `trace`) and from PmpFull `read`, `text … arg`, `say`/`show`/`print` (output only) and `check zero`.

## Files

| file | what |
|---|---|
| `judge.pmp` | first cut, 2026-10-09; its registry copy looped to its body and crashed the interpreter (kept unchanged) |
| `judge-v2.pmp` | the loop fixed, one atom table at the start; left a stray `set ATL const ar` in `TAUTCHK` (kept unchanged) |
| `judge-v3.pmp` | the stray line removed: the current judge |
| `rocq2jdg.rkt` | converter from the Rocq replay data (`RpInit.v`, `RpB0.v` … `RpB10.v`) to the input format JDG1; not trusted |
| `replay-B0.jdg`, `replay-all.jdg` | Theorem 29's registry (7 axioms, 670 definitions, 29 hypotheses) with batch 0 / all 11 batches |
| `t5.jdg` | registry plus the first five theorems |
| `mut/` | one accept case and fault cases built from `t5.jdg` and line 4197 of `replay-all.jdg` |
| `probe-*.pmp`, `judge-dbg1.pmp` | the probes that located the crash of the first cut |

Run: `..\pompetzki.exe judge-v3.pmp FILE.jdg` (exit 0 and ACCEPT, or REJECT / LIMIT with exit 1).

## Results, 2026-10-09 (pompetzki.exe of 2026-09-18, 109,473 bytes)

- `t5.jdg`: ACCEPT, 5 theorems, 64 steps, 0.56 s.
- `replay-B0.jdg`: ACCEPT, 823 theorems, 24,968 steps, registry 706 → 1,529, 100 s.
- `replay-all.jdg`: see `run-v3-all.txt`.
- Fault cases (`mut/`), each REJECT with exit 1 and the reason shown:

| case | fault | reason printed |
|---|---|---|
| m1-refl | `Y q 0 1` as an axiom | ax: not an axiom shape |
| m2-taut | taut from line 1 only | taut: not a tautology |
| m3-stmt | statement with the equation reversed | the last line is not the statement renamed by sig |
| m4-genvar | gen over the wrong variable | the last line is not the statement renamed by sig |
| m5-leib | wrong right-hand side of Leibniz's law | leib: the formula is not Leibniz's law for the given formula |
| m6-line | gen from line 9 of 2 | a step names a line that is not yet there |
| m7-use | use of registry entry 99999 | use: no such registry entry |
| m8-hyp | hypothesis 22 used, not declared | a hypothesis used by the steps is not among the theorem's |

  `ok-thm0` and `ok-hyp` (the theorem of line 4197, which uses hypothesis entry 699 and declares hypothesis 22): ACCEPT.

## Still to do in Stage 1

- The Rocq theorem: the statements of `judge-v3.pmp`, read from its bytes with the tokenizer of `pompetzki.asm` (as `C2Link.SourceBind` did for `verify_run2.pmp`), run under the PmpCore/PmpFull semantics, compute `check_batch`; with `Replay3.v`, acceptance implies `prov` over Gam with the declared hypotheses.
- The Racket copy by another session (proposed, not started).
