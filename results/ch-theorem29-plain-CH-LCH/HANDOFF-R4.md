# Lane LCH handoff R4: Gödel's half of the independence of CH

Written after the 19:30:07 power outage. Lane folder: `C:\ClaudeOutput\pompetzki\lanes\LCH`.

## Recovery checks

- `date` read 20:18:33 when recovery began.
- The live process table at 20:18 had no coqc, coqchk, racket or pompetzki process with LCH in its command line. The only match was the manager's launcher, `nohup … resume-lane-r4.rkt LCH …`.
- Every file listed below was hashed at 20:22:12. All have 0 NUL bytes.

Files written by the turn that was interrupted (mtimes 19:22–19:30) are not verified and are not for release. They stay unchanged:

- `lch-part-L5.rkt.txt`: its `BMadd1` generator is unfinished.
- `lch-part-L6.rkt.txt`
- `lch-part-cmd13.rkt.txt`
- `lch13.rkt`
- `lch14.rkt`

No receipt exists for any of them.

## Closed results (kernel-checked; every Print Assumptions: "Closed under the global context")

Rocq 9.1.0 (Rocq Platform 2026.07.0). Compile from `rocq\` with `-R ../../../forcing-src/general Cohen -R . LCH`.

| theorem | statement | coqchk receipt (Axioms: <none>, exit 0) |
|---|---|---|
| `AlignCH.con_zfc_con_notch_plain` | `prov (GamE (Neg ch)) Bot -> prov ZFpure Bot`, no premise: Cohen's half over the plain ¬CH | coqchk-1.txt (18:19:59–18:29:50) |
| `AlignCH.notch_plain_equiv` | `prov (GamE (Neg ch)) Bot <-> prov Gam0 Bot` | coqchk-1.txt |
| `Rel2.rel_sound`, `rel_closed`, `rel_con` | relativization of `prov` derivations to any class formula M with closedk 1 M | coqchk-1.txt |
| `GoedelCH.goedel_relative_consistency` | ∀M, closedk 1 M → LEX M → LAX M → LSEP M → LCOLL M → LCH M → `prov GamCH Bot -> prov ZFpure Bot` | coqchk-1.txt |
| `LAXred2.lax_reduced`, `goedel_reduced` | LAX i (i<6) from ZFpure ⊢ `psub (tauM Mf) sid (HT i)` | coqchk-2.txt (18:41:50–18:44:53) |
| `Abs2.abs_d0` | Δ₀ absoluteness for transitive classes | coqchk-3.txt (18:45:10–18:45:32) |
| `VLred.lch_from_vl`, `goedel_from_vl`, `goedel_final_red` | LCH from V = L relativized plus `prov (ZFE VL) (pi ch)` | coqchk-4.txt (18:47:00–18:49:33) |
| `LRed.LEX_L` | `LEX Lpure` (O1) | coqchk-5.txt (19:10:32–19:22:16, 11 m 42 s) |
| `LRed.HT0_L`, `LRed.HT5_L` | `prov ZFpure (psub (tauM Lpure) sid (HT 0))`, and the same for HT 5: L transitive (O2) | coqchk-5.txt |
| `LRed.LAX_Ext_L`, `LRed.LAX_Found_L` | `prov ZFpure (rel Lpure (axf 0))`, `prov ZFpure (rel Lpure (axf 5))` | coqchk-5.txt |
| `LRed.goedel_L` | the final kernel target, stated below | coqchk-5.txt |

Commands:

```
coqc -R ../../../forcing-src/general Cohen -R . LCH  Rel2.v GoedelCH.v AlignB.v AlignCH.v RelB.v LAXred2.v Abs2.v VLred.v LDef.v LexB.v LtrB.v LRed.v
coqchk -silent -o -R ../../../forcing-src/general Cohen -R . LCH LCH.LRed LCH.Abs2
```

Only the last run's results above are receipts. The exit codes are recorded at the end of each coqchk-N.txt.

## The final kernel target and its open premises

`LRed.goedel_L`, with L = `Lpure` = `pi (tof LDef.Ld)` and V = L = `VLpure` = `All Lpure`:

```
(forall i, 1 <= i -> i < 5 -> prov ZFpure (psub (LAXred2.tauM Lpure) sid (LAXred2.HT i))) ->
prov ZFpure (rel Lpure (axf 6)) ->
LSEP Lpure -> LCOLL Lpure ->
prov ZFpure (rel Lpure VLpure) -> prov (ZFE VLpure) (pi ch) ->
prov GamCH Bot -> prov ZFpure Bot
```

Each premise is an open obligation:

| # | exact statement | status |
|---|---|---|
| O3 | `prov ZFpure (psub (LAXred2.tauM Lpure) sid (LAXred2.HT 1))` (L closed under pairs) | open; detail below |
| O4 | the same with `HT 2` (L closed under unions) | open; missing LevExt and the union assembly |
| O5 | the same with `HT 3` (power covers) | open |
| O6 | the same with `HT 4` (an inductive set in L) | open |
| O7 | `prov ZFpure (rel Lpure (axf 6))` (Choice in L) | open |
| O8 | `LSEP Lpure` | open; schema, assigned to lane L2R |
| O9 | `LCOLL Lpure` | open; schema, assigned to lane L2R |
| O10 | `prov ZFpure (rel Lpure VLpure)` | open |
| O11 | `prov (ZFE VLpure) (pi ch)` (Gödel condensation: V = L ⊢ CH) | open |

Detail for O3:

- Proved, judge-accepted but not yet replayed in Rocq:
  - `Coh` (out10/05-coh.jdg): two hierarchies agree where both are defined;
  - `Cmp` (out12/06-cmp.jdg): any two ordinals are comparable.
- Missing:
  - LevExt: ∀t (Lev t → ∃s e v U (Lev s ∧ App(s,e,v) ∧ ∀z (BM(s,e,z) ↔ z∈U) ∧ RanU(t,U)));
  - the pair assembly.

CH over ZFC is therefore **not** closed as independent: Cohen's half is closed, and Gödel's half has open premises O3–O11.

## Judge-accepted JDG1 files

Both judges were run from `C:\ClaudeOutput\pompetzki\judge\`: `pompetzki.exe judge-v3.pmp FILE` and `racket\judge.rkt FILE`. Registry: 677 entries = AX0 ++ DEF0.

| file | theorems | steps | both judges | mutants REJECT by both | receipt |
|---|---:|---:|---|---|---|
| out4/01-align.jdg | 5 | 76 | ACCEPT, exit 0 | 9 of 10 | judge-run-2.txt |
| out4/02-relax.jdg | 6 | 106 | ACCEPT, exit 0 | 8 of 9 | judge-run-2.txt |
| out6/03-lex.jdg | 28 | 466 | ACCEPT, exit 0 | 10 of 11 | judge-run-3.txt |
| out6/04-ltr.jdg | 1 | 17 | ACCEPT, exit 0 | 6 of 7 | judge-run-3.txt |
| out10/05-coh.jdg | 4 | 172 | ACCEPT, exit 0 | 10 of 11 | judge-run-4.txt |
| out12/06-cmp.jdg | 10 | 193 | ACCEPT, exit 0 | 10 of 11 | judge-run-5.txt |

- In each file, the one mutant both judges accept is `registry-suc`. It changes the Suc2 entry, which these derivations do not use. Every other mutant is rejected by both judges at the same theorem and step.
- Files 01, 02, 03 and 04 are replayed in Rocq by `check_batch` (AlignB.v, RelB.v, LexB.v, LtrB.v). Files 05 and 06 are not yet replayed.

## SHA-256 (computed 20:22:12)

```
b5b4c7ea5049cf5a41e38bf93d30e4b0e5ffe25e6c233ff7849f6e8fbf52050c lch4.rkt
d409a47d206932a90dbaeb15ef1b911576d18545990c2272478bb3a7b78777e7 lch6.rkt
e3976677f5d7a21ea276e281f5d4987ed6a4b711b45fa614d27b2999ef7dff16 lch10.rkt
dfad0655cf4927ac03f9378b7217d1356c4428cc2f5efb5fbdc7ac0ba382d560 lch12.rkt
6e9d9d303cb4f6e3834f3e47e457fc7a804c10709b61aba1b07eb148a6f070b2 jdg2v.rkt
b578d9d9fa4ac85df7762fb85b40537a65e92941a875592584b52663e5cc1bff ldef.rkt
01eac473ccd5701fd5b084e441dde479907176c2043a8d29a2c0ff001dffb6bb L-DEFINITION.md
79e2ae8fe0e1c1159d549229d083fbc2c16d9973545714faf7f2c74ab6c85dd7 out4/01-align.jdg
30be9a917cae01adda67726a50a88b536c0c7cc0a81614719ec273c48aea09a4 out4/02-relax.jdg
efaab3b619c6c933193092a6432f3211f4a61632cd9a4b78546e96e0ffd91b09 out6/03-lex.jdg
a0c873fd850243a19a77aa5378a3f3bd695a6ed45741961a6039726b83965ff3 out6/04-ltr.jdg
b6113ce458dd1f210bf8f7ee27330fa2240262f110345ab3d8c7c517ddcfd07d out10/05-coh.jdg
71ca4ddf90ccc56876097f0e8277cec02d62a8d3b4fec8d29be5dc313350c300 out12/06-cmp.jdg
e7248a8b311e0a7259d92d257e5e5ecbcd61a3fa06f66c10ab62eb22ddcd79a1 judge-run-2.txt
4d86e6fe298eda6ee57d541a503af1b5bea3c7181592670c79b1ef3e06549dd1 judge-run-3.txt
b87969f39c968d93bca35052e266ba51bc9b348e3416bfc3897e70fa1d29dafa judge-run-4.txt
299b545a8e91099c48c675374908aad96a303b30245d21747b08df7b1c8287a6 judge-run-5.txt
07f5d3a926ed171aa32e98a7758c12665c04dd6625d94ef8d7514bf0006b4249 rocq/Rel2.v
460853b332220c1dcaa6e457e0ba495e7bd7b6955b4a4b4f77f77ecd67808bf4 rocq/GoedelCH.v
92a39cd45feeec5f38da37b7036812d44a2af95fea2542188f6778f228c6e345 rocq/AlignB.v
915c1b90e56330035343d019ea304b244f0c8e65339a508bc2581e16e5e3c0b4 rocq/AlignCH.v
17e1f0ca1689f20102c4ccd83a761b7f8568faf5946f2dd3f36c19082f1d6c97 rocq/RelB.v
73e9acac3ba399c03b6331d9332d69dacfacf47819f49daf1bd5e28a073477fd rocq/LAXred2.v
f869e61727394c49772faabe473fb60e4390096adf3fb35e104ed8a1773c0695 rocq/Abs2.v
64be6fd329f52b3ac0538617da476fc8cf06eaac1f74775342260eaac2e1d444 rocq/VLred.v
5fbfba9986f6b88dc15cfdd2f7cbbe404e1ffd391e229ea3d98abd2957246e88 rocq/LDef.v
eb0714b2c5dd1d08551fcf3b7e093edd9fc90248383cdba7f331f5a6995920d1 rocq/LexB.v
59382c3c00bb9bd956b58b2bc99932232b8003ba7ee6db3f663ec37419d50f5c rocq/LtrB.v
c9a2dfbfa8f23d265b05aab3d6b01f696a12650b23f1b8a92651216869a4bd14 rocq/LRed.v
b0ec52f49d7d3c0b8a214f853b55d70de3a18ed0045fe435ec21e6a5ba7a7a30 rocq/coqchk-1.txt
ffbdc32ec2d9ae9408ac533fe9c4c426c2171c8a21d31d588d6c51ad03036b59 rocq/coqchk-2.txt
c7e8dc34e1743ec27e363979b022a09822e18a43a2c7f318d4958bb7a9a54aab rocq/coqchk-3.txt
c3091cebc78708a05a85ece65a214f75f4914df6c0e561f1885b2ee857d1cc9f rocq/coqchk-4.txt
c708896d3b2273af406f18eaebe8844e607835461ca400a439f563845bd63a71 rocq/coqchk-5.txt
e490788d61d5b8907b529cbeb8d37fa53d40e2631a446f1c9421b2add6d71945 rocq/print-assumptions-2.txt
06c7cff3e83f8e7967d9d01db44a2acfff8547cd4b3d506b0afdddf18f13d9d7 RESULTS.md
b3fa5ea21d053db986033e4e6875b926f53ca58195ae77969750da2e8cb5a005 RESULTS-correction-1.md
f598d3c95804a6096bb5a2cb2cf42fd5905f8b5541fa4c6b5f4ce1561caf2c9f RESULTS-correction-2.md
b4262bf8d3b3c2d0f0d9d468e767c79c5e1013f5b2146ad92093095be82ffe87 STATUS.txt
```

The definition of L (O0) is frozen in L-DEFINITION.md and rocq/LDef.v. Lane L2R was sent the same paths at 19:10 (queued, not confirmed read).
