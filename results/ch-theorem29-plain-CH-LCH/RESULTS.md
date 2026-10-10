# Lane LCH: Gödel's half of the independence of CH — results, 2026-10-09

Written 18:50 (`date`). Rules of RELEASE-DAY-ORDERS-2026-10-09.md kept: new files only, all in this folder; Racket for the generators; times from `date`.

## Status in one line

- **Cohen's half, now over the plain statement:** `AlignCH.con_zfc_con_notch_plain : prov (GamE (Neg ch)) Bot -> prov ZFpure Bot`, no premise.
- **Gödel's half:** reduced in Rocq, kernel-checked, to the eleven obligations O1–O11 below. They are not discharged, so CH over ZFC is **not yet closed as independent**.

## 1. The plain statement and the alignment

`ch_text` (GoedelCH.v), parsed by Theorem 29's own parser `pstmt symtab`:

    A w A x A p I K K Om1 w A u Q E u p Sub2 u w Sub2 x p D Le2 x w Le2 p x

- Reading: for w = ω, p = P(ω) and x ⊆ p, either x injects into ω or p injects into x.
- For x ⊆ P(ω), "p injects into x" is |x| = 2^ℵ₀ by Cantor–Schröder–Bernstein.
- ¬CH is `Neg ch`. Both halves now concern this one text.

Theorem 29's notCH* (Pure.v) is ∃w∃x∃y [Om1 w ∧ ∀u(u∈x → u⊆w) ∧ ∀u(u∈y → u⊆w) ∧ ¬Le2(x,w) ∧ ¬Le2(y,x)]. Its equivalence with `Neg ch` is derived in `out4/01-align.jdg`; both judges ACCEPT. The file has five theorems:

| # | key | statement |
|---|---|---|
| 677 | LeSub | Sub2(y,p) → (Le2(p,x) → Le2(y,x)): the same injection, total on the smaller set |
| 678 | PowEx | ∀w ∃p ∀u (u∈p ↔ Sub2(u,w)): from Power (entry 3) and one Separation instance |
| 679 | NotchPlain | notCH* → ¬CH (witness p = P(w); y ⊆ p and LeSub) |
| 680 | PlainNotch | ¬CH → notCH* (witness y := p) |
| 681 | NotchIff | notCH* ↔ ¬CH |

In Rocq, AlignCH.v replays this file by `Replay2.check_batch` (vm_compute) over REGP, the first 677 entries of `RpInitOk.REG0`. `Replay3.check_batch_ok` turns acceptance into derivability: prov Gam (notch → ¬ch) and prov Gam (¬ch → notch). The 647 definitions after ZB_BASE are then eliminated, carrying one extra axiom whose symbols they avoid. Hence:

- `gam0_neg_ch : prov Gam0 (Neg ch)`
- `gamnch_notch : prov (GamE (Neg ch)) notch`
- `notch_plain_equiv : prov (GamE (Neg ch)) Bot <-> prov Gam0 Bot`
- `con_zfc_con_notch_plain : prov (GamE (Neg ch)) Bot -> prov ZFpure Bot`, from `RpFinal.cohen_relative_consistency_closed`

`GamE E` = the seven axioms, every Separation and Collection instance (any symbols), the 23 ZB_BASE definitions in every renaming, and E. So `GamE notch` is Theorem 29's Gam0, `GamE (Neg ch)` its plain form, and `GamE ch` = `GamCH` below.

## 2. Gödel's half, in the form of Theorem 29

Rocq theorems. Every one prints "Closed under the global context" (`print-assumptions-2.txt`), and coqchk reports Axioms: <none> (§4).

| file | theorem | statement |
|---|---|---|
| Rel2.v | `rel_sound`, `rel_closed`, `rel_con` | relativization of `prov` derivations to any class formula M (closedk 1 M); details below |
| GoedelCH.v | `pi_prov` | every derivation from GamE E purifies (ZB_BASE unfolded, every other symbol to Top) into pure ZFC + pi E |
| GoedelCH.v | `goedel_relative_consistency` | ∀M, closedk 1 M → LEX M → LAX M → LSEP M → LCOLL M → LCH M → prov GamCH Bot → prov ZFpure Bot |
| LAXred2.v | `lax_reduced` | for a pure class formula Mf, i < 6: ZFpure ⊢ HT i[Mf] → ZFpure ⊢ rel Mf (axf i) |
| LAXred2.v | `goedel_reduced` | as `goedel_relative_consistency`, with LAX replaced by the six HT i[Mf] and Choice relativized |
| Abs2.v | `abs_d0` | every Δ₀ formula φ, every axiom set B: B ⊢ M(v0) → … → M(v(n−1)) → TrM → (rel M φ ↔ φ) |
| VLred.v | `lch_from_vl` | LEX, LAX, LSEP, LCOLL, ZFpure ⊢ rel M VL, ZFpure + VL ⊢ pi ch → LCH M (VL any closed sentence) |
| VLred.v | `goedel_final_red` | for a pure class formula Mf and closed VL: LEX, HT 0..5, Choice^Mf, LSEP, LCOLL, VL^Mf, (ZFpure + VL ⊢ pi ch) → prov GamCH Bot → prov ZFpure Bot |

Details of Rel2.v:

- `rel M`: `All a ↦ All (M → rel a)`; atoms and connectives are unchanged.
- Free variables carry guards: `chain (G M n) g` = M(v0) → … → M(v(n−1)) → g.
- `rel_sound`: if A is closed under renaming and every axiom of A, relativized and guarded with any n ≥ 1 covering its free variables, is derivable in B, then the same holds for every theorem of A.
- `rel_closed`: in addition, if B ⊢ ∃x M(x), then every closed theorem of A has its relativization derivable in B, with no guard.
- `rel_con`: A ⊢ ⊥ implies B ⊢ ⊥.

The five premises of `goedel_relative_consistency` (GoedelCH.v):

- **LEX** ZFpure ⊢ ∃x M(x).
- **LAX** ZFpure ⊢ rel M (axf i) for the seven axioms of the kernel's table.
- **LSEP** For every pure g and every n ≥ 1 with closedk n (SepF g): ZFpure ⊢ chain (G M n) (rel M (SepF g)).
- **LCOLL** The same for CollF g.
- **LCH** ZFpure ⊢ rel M (pi ch).

The six hypotheses HT i, as derived in `out4/02-relax.jdg`. M is the predicate symbol 5000, defined nowhere; Rocq instantiates it by uniform substitution.

| i | axiom | HT i |
|---|---|---|
| 0 | Ext | M transitive: ∀x∀y (M(y) → x∈y → M(x)) |
| 1 | Pair | ∀x∀y (M(x) → M(y) → ∃z (M(z) ∧ ∀u (u∈z ↔ u=x ∨ u=y))) |
| 2 | Union | ∀f (M(f) → ∃a (M(a) ∧ ∀x (x∈a ↔ ∃y (y∈f ∧ x∈y)))) |
| 3 | Power | M transitive ∧ ∀x (M(x) → ∃y (M(y) ∧ ∀z (M(z) → (∀u (u∈z → u∈x) → z∈y)))) |
| 4 | Inf | M transitive ∧ ∃w (M(w) ∧ B(w)), B = the body of the table's Infinity axiom (∅ ∈ w, w closed under y ↦ y ∪ {y}) |
| 5 | Found | M transitive |

## 3. Judge results

Run from `C:\ClaudeOutput\pompetzki\judge\`, both judges on every file: `pompetzki.exe judge-v3.pmp FILE` and `racket\judge.rkt FILE`.

**Run 2 (`judge-run-2.txt`, 18:26:11 – 18:26:44, files of `out4\`, generator lch4.rkt):**

| file | theorems | steps | bytes | pmp | pmp time | Racket | Racket time |
|---|---:|---:|---:|---|---:|---|---:|
| 01-align.jdg | 5 | 76 | 59,552 | ACCEPT, exit 0 | 1,306 ms | ACCEPT, exit 0 | 511 ms |
| 02-relax.jdg | 6 | 106 | 66,020 | ACCEPT, exit 0 | 1,534 ms | ACCEPT, exit 0 | 624 ms |

- **Registry of both files:** 677 entries, equal entry for entry to AX0 (7) ++ DEF0 (670) of RpInit.v, none with hypotheses. The check is sigma1.rkt's own parse of the Rocq source.
- **Generator's copy of the checker:** ACCEPT 677 5 76 682, and ACCEPT 677 6 106 683.
- **19 mutated copies:**
  - 17 REJECT, exit 1, from both judges, each time at the same theorem and step in both. The mutations are drop-step, exel-var, exi-witness, mp-swap (01 only), neg-final, taut-goal, twin-final, use-shift, and registry-used.
  - registry-used alters a registry entry the file uses: Sub2's body for 01, Extensionality for 02.
  - 2 ACCEPT, exit 0, from both judges: `registry-suc`, inherited from sigma1.rkt. It alters Suc2's definition, which neither file uses, so the shortened file is still a valid derivation. The registry check above is what catches a changed registry.

**Run 1 (`judge-run-1.txt`, 17:50:58 – 17:51:19, `out\01-align.jdg`, generator lch2.rkt):**

- The file is byte-identical to `out4\01-align.jdg` (cmp). ACCEPT from both judges, pmp 1,410 ms, Racket 494 ms.
- 9 mutants: 8 REJECT from both; registry-suc ACCEPT from both.

## 4. Rocq (9.1.0, Rocq Platform 2026.07.0)

All Rocq files are in `rocq\`. They are compiled with `-R ../../../forcing-src/general Cohen -R . LCH`, against the unchanged `.vo` files of Theorem 29.

| file | lines | content |
|---|---:|---|
| Rel2.v | 312 | relativization; guard chains |
| GoedelCH.v | 114 | ch, GamE, GamCH, pi_prov, the reduction with five premises |
| AlignB.v | 82 | 01-align.jdg as `list thm` (jdg2v.rkt) |
| AlignCH.v | 151 | replay of AlignB, elimination with an extra axiom, Theorem 29 over ¬CH |
| RelB.v | 112 | 02-relax.jdg as `list thm` |
| LAXred2.v | 215 | replay of RelB, substitution for symbol 5000, `gam_pure` (a pure theorem of Gam is one of ZFpure), lax_reduced, goedel_reduced |
| Abs2.v | 139 | Δ₀ absoluteness for transitive classes |
| VLred.v | 62 | LCH from V = L; goedel_final_red |

coqchk (`-silent -o`), each run reporting Axioms: <none>, no type-in-type, no unsafe fixpoints, no assumed positivity:

| run | modules | time (`date`) | real |
|---|---|---|---:|
| coqchk-1 | LCH.Rel2, LCH.GoedelCH, LCH.AlignCH (with Theorem 29's whole chain, RpFinal) | 18:19:59 – 18:29:50 | 9 min 50 s |
| coqchk-2 | LCH.LAXred2 | 18:41:50 – 18:44:53 | 3 min 3 s |
| coqchk-3 | LCH.Abs2 | 18:45:10 – 18:45:32 | 21 s |
| coqchk-4 | LCH.VLred | 18:47:00 – 18:49:33 | 2 min 33 s |

## 5. The exact remaining obligations

To close Gödel's half, instantiate `VLred.goedel_final_red` with the following:

- a pure formula Mf with closedk 1 Mf = true: the constructible universe L;
- a closed pure sentence VL, i.e. ∀x Mf(x).

Then prove the obligations below. The pmp judge discharges single statements: post each as a JDG1 derivation and replay it in Rocq, as AlignB and RelB are. Schemas need one Rocq proof each about every instance.

| # | obligation | kind | route |
|---|---|---|---|
| O0 | the formula Mf (the hierarchy L_α by transfinite recursion of Def, Def by coded satisfaction or by Gödel's operations) and VL | definition | a generator emitting Mf as a pure formula, in the same way sigma1.rkt writes Add and Mul over registered symbols |
| O1 | LEX: ZFpure ⊢ ∃x Mf(x) | single | ∅ ∈ L₁; existence of the recursion's values |
| O2 | HT 0 = HT 5: Mf transitive | single | each L_α transitive, by induction on α |
| O3 | HT 1: pairs | single | {x, y} ∈ Def(L_α) for x, y ∈ L_α |
| O4 | HT 2: unions | single | ⋃f ∈ Def(L_α) for f ∈ L_α |
| O5 | HT 3: power covers | single | Collection bounds the L-ranks of the constructible subsets of x |
| O6 | HT 4: an inductive set in L | single | ω ∈ L_{ω+1} |
| O7 | Choice relativized: ZFpure ⊢ rel Mf (axf 6) | single | the definable well-order <_L |
| O8 | LSEP: every pure Separation instance relativized, parameters guarded | **schema** | reflection for the L-hierarchy, proved in Rocq by induction on the formula with templates, as Claim.v did for Theorem 29; `Abs2.abs_d0` is its Δ₀ case |
| O9 | LCOLL: every pure Collection instance relativized | **schema** | as O8 |
| O10 | VL relativized: ZFpure ⊢ rel Mf VL | single | absoluteness of the L-construction for transitive models; Δ₀ base in Abs2 |
| O11 | ZFpure + VL ⊢ pi ch | single | Gödel's condensation lemma: under V = L every subset of ω is in L_{ω₁}, so 2^ℵ₀ = ℵ₁ |

After O0–O11, the theorem `prov GamCH Bot -> prov ZFpure Bot` holds with no premise. With `con_zfc_con_notch_plain`, both relative consistencies would then be closed for the one text `ch_text`.

## 6. Files (all kept; failed versions stay beside their repairs)

| file | what |
|---|---|
| `lch4.rkt` | current generator: layers 01 and 02, mutants, judge runner |
| `lch3.rkt`, `out3\` | 02 with a redundant last step per theorem (its drop-step mutant still a proof); not judged |
| `lch2.rkt`, `out\` | layer 01 only; judged in run 1 |
| `lch.rkt` | first assembly, without sigma1.rkt's `require` line; did not compile |
| `lch-part-derivations.rkt.txt`, `lch-part-relativized.rkt.txt` | the new code as written, before assembly |
| `jdg2v.rkt` | JDG1 → Rocq `list thm` (not trusted; checked by check_batch) |
| `judge-run-1.*`, `judge-run-2.*` | judge rows, start and end times |
| `rocq\Rel.v` | first draft of Rel2.v; stops at line 245 |
| `rocq\LAXred.v` | first draft of LAXred2.v; stops at line 76 |
| `rocq\Abs.v` | first draft of Abs2.v; does not compile |
| `rocq\T0.v` | a load test of the Cohen library |
| `rocq\print-assumptions-1.txt`, `-2.txt` | Print Assumptions output |
| `rocq\coqchk-1..4.*` | coqchk output, start and end times |

## 7. Notes

- The first coqtop trial of AlignCH (17:53) cascaded from an error in a lemma statement: `length` resolved to `String.length`. One later step then drove its worker to 7.6 GB.
  - I stopped those two processes, coqtop 72576 and rocqworker 70540, at about 18:03.
  - Two kernel traps were found and avoided: an `unfold` cast on D1, and a conversion of `[] ++ D0`. Checks are now stated expanded, as the Theorem 29 notes prescribe.
- sigma1.rkt, the judge folder, forcing-src and Theorem 29's `.vo` files are read only; nothing outside this folder was written.

## 8. Reproduce

```
racket lch4.rkt emit NEWDIR
racket lch4.rkt judge NEWDIR NEWRESULTS.txt
racket jdg2v.rkt NEWDIR/01-align.jdg rocq/NEW-AlignB.v AB
coqc -R ../../../forcing-src/general Cohen -R . LCH  Rel2.v GoedelCH.v AlignB.v AlignCH.v RelB.v LAXred2.v Abs2.v VLred.v   (in this order, from rocq\)
coqchk -silent -o -R ../../../forcing-src/general Cohen -R . LCH LCH.AlignCH LCH.VLred LCH.Abs2
```
