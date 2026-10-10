# CX3 release integration after recovery

Started 2026-10-09T20:12:54-04:00; completed 2026-10-09T20:12:55-04:00, both from date.exe. Verified execution host: THEBIGMAGILLA, Alienware Area-51 AAT2265; local lane directory has no link target.

The original CX3 proofs retain their exact statements and proof-object hashes. 39 original lane manifest entries and 44 original project/dependency hashes were verified. This integration started zero compiler, kernel-checker, or judge jobs. The preserved compiler and recursive coqchk receipts are reused. Both CX3 checks ended exit 0 with Axioms: <none>; all 23 requested assumption summaries were closed.

## Live ownership and existing package integration

The Stage 1 worker is 01a12227-bb71-7db2-a7f2-518a76ceba25 and the CX4 worker is 01a122ad-bc25-7f33-9dd5-c3da7da04c1f. Both were active in the compact app ownership snapshot saved in LIVE-OWNERSHIP-RECOVERY-1.json. They own the unfinished execution-to-check_batch composition. Package ownership is recorded in C:/ClaudeOutput/pompetzki/lanes/CEO/executive-20261009-183208/COO-STATUS-20261009-2005.md.

The assembled source package is C:/ClaudeOutput/pompetzki/lanes/CEO/executive-20261009-183208/package/release-final-1925. Its CLAIMS.md cites CX3's conservativity and accepted-member APIs; VALIDATION-MATRIX.md rows 2c and 2d mark CX3 and the seven CX3B baseline certificates CLOSED. Every shipped source/receipt selected in the JSON snapshot matched both its live file and its outer package manifest entry. The source package already contains the pure-Gam wiring; this receipt supplies its exact qualified APIs and proof dependencies.

## Exact interfaces for Stage 1 and CX4

Logical mappings for the completed logical bridge are:

```text
-Q C:/ClaudeOutput/pompetzki/forcing-src/general Cohen
-Q C:/ClaudeOutput/pompetzki/forcing-src/codex-judge-link-20261009 JudgeLink
-Q C:/ClaudeOutput/pompetzki/lanes/CX3 CX3
-Q C:/ClaudeOutput/pompetzki/lanes/CX3B CX3B
```

In the source package the corresponding directories are rocq/general, rocq/codex/codex-judge-link-20261009, rocq/CX3, and rocq/CX3B. It ships source and completed receipts; the original checked .vo hashes are in the JSON.

`CX3.Conservativity2.gam_pure_conservative` at Conservativity2.v:60 has type:

```coq
forall f : form, syms f = [] -> prov Gam f -> prov ZFpure f.
```

Its input formula may have free variables. `pure_provability_iff` at line 75 proves equivalence on precisely that pure language. No closedness or execution hypothesis is added to either statement.

`CX3.Stage2Conservativity2.accepted_member_Gam` at Stage2Conservativity2.v:82 is the general replay bridge:

```coq
forall (hypothesis : N -> form) reg ts t,
  reg_ok hypothesis reg -> check_batch reg ts = true ->
  In t ts -> t_hyps t = [] -> prov Gam (tof (t_stmt t)).
```

For any Good expansion table T, `accepted_expanded_member_pure` at line 91 adds `Good T` and `syms (expD Pr T (tof (t_stmt t))) = []` and proves the corresponding ZFpure statement. For the fixed 677-entry Stage 2 registry, `stage2_accepted_member_pure` at line 121 discharges registry soundness and the eleven-definition table and requires only abstract batch acceptance, membership, no hypotheses, and `covered stage2_table (tof (t_stmt t)) = true`.

Exact applications of the existing proved constants are:

```coq
CX3.Conservativity2.gam_pure_conservative f Hpure DGam
CX3.Stage2Conservativity2.accepted_member_Gam
  hypothesis reg ts t R C Hin Hnil
CX3.Stage2Conservativity2.stage2_accepted_member_pure
  ts t C Hin Hnil Cov
```

Here C must come from a proved Replay2 computation or from the completed implementation theorem with its parser, registry, outcome and resource contracts discharged. A native ACCEPT receipt alone is not that proof. Arbitrary initial registries still require reg_ok; the fixed registry obligation is discharged by stage2_registry_ok, with its 677-entry count kernel-proved.

Dependencies: Cohen.Syn/Prov define form, syms and prov; Cohen.Ax/Elim define Gam and ZFpure; Cohen.Use.prov_psub_to and Cohen.Elim.elim_step/okb_Dall support conservativity; Cohen.Expand.repl/buildT_good support faithful expansion; Cohen.Replay2 supplies check_batch and theorem data; Cohen.Replay3 and JudgeLink.JudgeBatch supply abstract soundness; Cohen.RpInitOk.REG0_ok discharges the fixed registry. SOURCE-HASHES.txt and the integration JSON bind those original files.

## Seven concrete Stage 2 batches are already closed

CX3B completed seven entire baseline batch computations and their member proofs after the original CX3 report. The integration verified the preserved proof objects, all seven successful recursive check receipts and Axioms: <none> contexts against CX3B's original manifest; it did not repeat those checks. The source/transcription hashes and both-judge receipt are retained.

| Source | Theorems | Steps | Closed member theorem |
|---|---:|---:|---|
| 01-numerals.jdg | 73 | 1679 | `CX3B.Stage2Certificate01c.batch01_closed` |
| 02-membership.jdg | 226 | 4168 | `CX3B.Stage2Certificate02c.batch02_closed` |
| 03-distinct.jdg | 248 | 4076 | `CX3B.Stage2Certificate03c.batch03_closed` |
| 04-bounded.jdg | 90 | 1596 | `CX3B.Stage2Certificate04c.batch04_closed` |
| 05-arithmetic.jdg | 432 | 20508 | `CX3B.Stage2Certificate05c.batch05_closed` |
| 06-sentences.jdg | 364 | 13904 | `CX3B.Stage2Certificate06c.batch06_closed` |
| 07-sigma1.jdg | 223 | 7138 | `CX3B.Stage2Certificate07c.batch07_closed` |

For each NN the theorem has type `forall t, In t batchNN -> prov Gam (tof (t_stmt t)) /\ prov ZFpure (stage2_expand (tof (t_stmt t)))`. The named `batchNN_accepted`, `batchNN_metadata`, and `registryNN_correct` are proved constants; acceptance and coverage are discharged for these concrete batches. Stage2RegistryCertificate2.reg0_677_correct proves registry equality, and Stage2Bridge2.stage2_batch_certificate_registered composes the proved acceptance and metadata with the CX3 interface.

The seven files total 1656 theorems and 53069 steps. Later larger priority waves belong to CX3B's separate in-flight work. The original CX3 report remains the earlier abstract milestone; these concrete certificates close that earlier finite batch premise for the baseline seven.

## Package receipt scope

INTEGRATION-RECOVERY-1.json contains 95 exact path/size/hash rows, with package copies and outer-manifest matches for shipped artifacts. The outer package MANIFEST.sha256 authenticates the shipped layout. The inner CX3 and CX3B manifests describe original lane snapshots: compiled objects and auxiliary artifacts are omitted from the source package, and CX3B receipts are routed separately from sources.

The source directory's existing post-reboot current-source-scan.txt records 26000 checked/good files and zero failures. The COO recovery status separately records archive structural failures; this receipt authenticates source-package copies and the completed logical proof interfaces and does not certify those archives.

Pure-Gam release wiring is present and hash-matched. The unfinished Stage 1 and ELF implementation theorems remain with their live owners. No desired native verdict equivalence has been supplied as an assumption or substituted for those proofs.
