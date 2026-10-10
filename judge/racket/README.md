# judge.rkt — the Racket copy of the judge

`judge.rkt` is a second implementation of `check_batch` from `forcing-src/general/Replay2.v`, which Replay3.v proves sound for `prov`. It reads the JDG1 format written by `../rocq2jdg.rkt`.

It was written only from the Rocq definitions:

- Syn.v: form, ren, up, scons, free, form_eqb, Kf, Df, Qf, Xf
- Replay.v: absk, findf, addat, topf
- ReplayT.v: bf, mkN, mkI, subst, somevar, taut_bf, tobf, tautchk2
- Checks.v: skip1, ins2, SepF, CollF, Bot
- Ax.v: closedk
- Replay2.v: dform, tof, step, axshape, isSep, isColl, isSepN, isCollN, sstep, run, check_thm, check_batch
- One definition line each from Prov.v (`sid`) and Kal.v (`pform`)

`judge.pmp`, `judge-v2.pmp`, `judge-v3.pmp` and the other `.pmp` files in `..` were not read. All arithmetic uses exact integers.

## Usage

```
"C:\Program Files\Racket\racket.exe" judge.rkt FILE.jdg
```

- On success it prints `ACCEPT registry <initial entries> theorems <n> steps <total> final-registry <entries>` and exits 0.
- On failure it prints `REJECT theorem <i> step <j> (<rule or final check>)` and exits 1. Indices start at 0.
- If a theorem fails its final check (last line against the statement, sig repeats, closedness, hypotheses, or no lines), `step` is that theorem's step count.
- Malformed input prints `REJECT parse error at byte <b>: ...` and exits 1.

## Results, 2026-10-09 (Racket v9.3 [cs], wall clock per run, startup and in-memory compile included)

| input | result | time |
|---|---|---|
| replay-B0.jdg | ACCEPT registry 706 theorems 823 steps 24968 final-registry 1529 | 0.64–0.66 s (3 runs) |
| replay-all.jdg | ACCEPT registry 706 theorems 4551 steps 139194 final-registry 5257 | 3.32–3.53 s (3 runs) |
| t5.jdg | ACCEPT registry 706 theorems 5 steps 64 final-registry 711 | 0.26 s |
| mut/m1-refl.jdg | REJECT theorem 0 step 1 (step Y) | 0.25 s |
| mut/m2-taut.jdg | REJECT theorem 0 step 2 (step T) | 0.27 s |
| mut/m3-stmt.jdg | REJECT theorem 0 step 5 (final: last line is not the statement) | 0.25 s |
| mut/m4-genvar.jdg | REJECT theorem 0 step 5 (final: last line is not the statement) | 0.26 s |
| mut/m5-leib.jdg | REJECT theorem 0 step 0 (step Z) | 0.26 s |
| mut/m6-line.jdg | REJECT theorem 0 step 3 (step G) | 0.24 s |
| mut/m7-use.jdg | REJECT theorem 2 step 0 (step U) | 0.26 s |
| mut/m8-hyp.jdg | REJECT theorem 0 step 1 (final: a hypothesis used is not claimed) | 0.24 s |
| mut/ok-hyp.jdg | ACCEPT registry 706 theorems 1 steps 1 final-registry 707 | 0.24 s |
| mut/ok-thm0.jdg | ACCEPT registry 706 theorems 1 steps 5 final-registry 707 | 0.25 s |

The timed runs ran from 13:59:40 to 13:59:52 on the system clock. The judge.rkt that was run is 22718 bytes, SHA-256 `D6CF694C294A829172976EBD6741D15E39D91F5CB2FEB09951421E5212C079CA`.

## Implementation choices that leave check_batch's value unchanged

1. **Hash-consed forms.** Forms are interned, with a fresh table for each theorem, so `form_eqb` (structural equality) becomes `eq?`. Registry statements are kept as parsed dforms, and `tof` builds them again inside each theorem's table.
2. **Free-variable bound.** Each form stores `fvb`, one more than its largest free variable (0 when closed).
   - `ren s f` returns `f` unchanged under `k` binders when `fvb f <= k` (ren_free, Ax.v).
   - `free n f` is false when `n >= fvb f`.
3. **Memoization.** `ren`, `free`, `closedk`, `topf`, `tobf` and `subst` are memoized on DAG nodes within each call. The Q, K and X expansions share subterms, and all of these functions are pure.
4. **addat.** A membership set sits beside the list (`existsb form_eqb` is membership). N and I nodes already walked are skipped, because their atoms are already in the list, so `addat` would leave the list unchanged.
5. **Short-circuit.** `andb` / `orb` are evaluated left to right and stop at the first decisive value.
6. **taut_bf.** Runs with the fuel exactly as defined: the length of `addat [] f`.

## Input policy where the Rocq definitions say nothing

Comparing the pmp judge's behaviour on malformed input is a separate check. On those points this copy:

- Requires the token `JDG1`, then `R`, then `T`.
- Takes tags to be single-character tokens.
- Takes numbers to be decimal digit strings; leading zeros are read as decimal.
- Accepts space, tab, CR and LF as white space.
- Rejects any token after the last theorem.
- Parses each theorem and checks it before reading the next one. A parse error after a failing theorem is therefore never reached, and the theorem's REJECT is what gets reported.
