# L2R round 2: LCH obligations O8 = GoedelCH.LSEP Mf and O9 = GoedelCH.LCOLL Mf

Written 2026-10-09, times from `date`; last reading 20:33:43 EDT. Folder: `C:\ClaudeOutput\pompetzki\lanes\L2R\`.

## Outcome

O8 and O9 are reduced, not discharged.
- The reduction is kernel-checked. The coqchk -o receipt `coqchk-r4b.log` reports Axioms: <none>, exit 0.
- LSEP Mf and LCOLL Mf follow from:
  - four single statements about a hierarchy of levels Lev: STR, SSUB, SIN, SCOV;
  - two schemas: GREFL (reflection) and DSEP0 (Delta_0 separation closure).
- None of these six is proved. Each needs O0, the definition of Mf (the formula of L) and of its levels. O0 is undefined in LCH.
- `goedel_final_red_d0` is VLred.goedel_final_red with O8 and O9 replaced by these six hypotheses. All other premises (O1 to O7, O10, O11) are unchanged.

## Theorem statements (M, Lev pure formulas, closedk 1 M = true, closedk 1 Lev = true)

- `L2RSepL.lsep_from_levels`: prov ZFpure (STR Lev) -> REFLsep schema -> DEFsep schema -> LSEP M.
- `L2RSepL.lcoll_from_levels`: STR, SSUB, SIN -> REFLcoll schema -> LCOLL M.
- `L2RRefl.reflsep_from_grefl`, `L2RRefl.reflcoll_from_grefl`: SCOV, GREFL -> REFLsep g n and REFLcoll g n for every pure g.
- `L2RRefl.lsep_from_grefl`: STR, SCOV, GREFL, DEFsep -> LSEP M.
- `L2RRefl.lcoll_from_grefl`: STR, SSUB, SIN, SCOV, GREFL -> LCOLL M.
- `L2RDefR4.relU_d0`: syms g = [] -> d0 (relU w g). This is the Delta_0 case that Abs2.d0 covers.
- `L2RDefR4.defsep_from_dsep0`: SIN, SSUB, (forall psi n, d0 psi -> closedk (S (S n)) psi = true -> DSEP0 M psi n) -> DEFsep M Lev g n for every pure g.
- `L2RDefR4.lsep_from_grefl_dsep0`: STR, SSUB, SIN, SCOV, GREFL, DSEP0 -> LSEP M.
- `L2RGoedel.goedel_final_red_levels`: LEX Mf, HT 0..5, rel Mf (axf 6), STR, SSUB, SIN, SCOV, GREFL, DEFsep, rel Mf VL, ZFE VL |- pi ch -> (prov GamCH Bot -> prov ZFpure Bot).
- `L2RGoedelD0R4b.goedel_final_red_d0`: the same with DEFsep replaced by DSEP0.

Definitions:
- GREFL: L2RRefl.v:40.
- SCOV: L2RRefl.v:44.
- DSEP0: L2RDefR4.v:34.
- STR, SSUB, SIN, REFLsep, REFLcoll, DEFsep: L2RSepL.v.

## Line counts

| file | lines | Lemma/Theorem |
|---|---:|---:|
| L2RLogicA.v | 168 | 42 |
| L2RSepL.v | 324 | 28 |
| L2RRefl.v | 132 | 7 |
| L2RDefR4.v | 92 | 5 |
| L2RGoedel.v | 25 | 1 |
| L2RGoedelD0R4b.v | 25 | 1 |

`L2RDef.v` has the same text as L2RDefR4.v except line 1. Its `.vo`, written 19:30:38, was cut by the outage: 641 non-NUL bytes out of 26610. It is left in place and not used.

## Receipts

- `coqchk-2.log`: `coqchk -R ... L2R.L2RSepL`, 19:23:44 to 19:27:50, Axioms: <none>, exit 0.
- `compile-r4b.log`: coqc of L2RDefR4.v, L2RGoedelD0R4b.v and PrintAx5r4.v, each exit 0, 20:26:44 to 20:27:09. Seven theorems are "Closed under the global context".
- `coqchk-r4.log`: `coqchk <LP> L2R.L2RGoedel L2R.L2RGoedelD0R4b`, 20:27:21 to 20:30:45, real 3m23.838s, "Modules were successfully checked", exit 0. It was run without -o, so it has no axiom summary.
- `coqchk-r4b.log`: `coqchk -o <LP> L2R.L2RGoedel L2R.L2RGoedelD0R4b`, 20:30:56 to 20:33:36, real 2m39.576s, exit 0. The two modules depend on L2RDefR4, L2RRefl, L2RSepL, L2RLogicA, LCH (Rel2, GoedelCH, LAXred2, VLred, Abs2) and Cohen. Context summary:

```
Modules were successfully checked

CONTEXT SUMMARY
===============

* Theory: Set is predicative
* Theory: Rewrite rules are not allowed
* Axioms: <none>
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
* Inductives whose positivity is assumed: <none>

real	2m39.576s
exit 0
```

`<LP>` = `-R /c/ClaudeOutput/pompetzki/forcing-src/general Cohen -R /c/ClaudeOutput/pompetzki/lanes/LCH/rocq LCH -R /c/ClaudeOutput/pompetzki/lanes/L2R L2R`.

The SHA-256 of every file is in HANDOFF-R4.md and HANDOFF-R4-FINAL.md.

## Open

- GREFL Mf Lev
- DSEP0 Mf psi n, for every d0 psi
- STR Lev, SSUB Mf Lev, SIN Mf Lev, SCOV Mf Lev
- O0, the definition of Mf and Lev

Proving GREFL in ZFpure needs recursion along omega of definable class functions, which is the standard proof of the reflection principle.
