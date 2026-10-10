# CX3: definitions are conservative

Completed at 2026-10-09T18:11:00-04:00 (Git date.exe). Execution host verified by Win32_ComputerSystem: THEBIGMAGILLA, Alienware Area-51 AAT2265. Filesystem drives C:, G:, and Temp were listed; the lane directory is an ordinary directory with no link target. Authoritative deliverables are in C:\ClaudeOutput\pompetzki\lanes\CX3\.

The final proof sources are `Conservativity2.v` and `Stage2Conservativity2.v`, imported under logical prefix `CX3`. They contain 27 named lemmas/theorems/corollaries. Both compiled with Rocq 9.1.0 and passed recursive coqchk (no `-norec`). Both kernel summaries print `Axioms: <none>`. The compiler printed 23 requested assumption summaries, all `Closed under the global context`. No new Axiom, Parameter, Admitted, or admit occurs in either final source. The coqchk summaries also report no type-in-type dependencies, unsafe fixpoints, or assumed positivity.

## General conservativity

The requested theorem is proved with its original conclusion, for every pure formula including formulas with free variables:

```coq
Theorem gam_pure_conservative (f : form) :
  syms f = [] -> prov Gam f -> prov ZFpure f.

Theorem pure_provability_iff (f : form) :
  syms f = [] -> (prov Gam f <-> prov ZFpure f).

Theorem elim_all_pure (L : list (nat * nat * form)) (f : form) :
  okb [] L = true -> syms f = [] ->
  prov (GamL L) f -> prov ZFsym f.
```

`psub_pure_fixed` derives invariance of a pure formula under every predicate substitution from Syn.psub_none. `elim_all_pure` uses reverse induction on the definition list and the existing Elim.elim_step. For the registered theory it uses the existing proved finite check Elim.okb_Dall. `zfsym_top_substitution` applies Use.prov_psub_to to every remaining axiom, producing a pure Separation or Collection instance; `zfsym_pure_formula` retains the original pure conclusion. Reverse inclusion follows because every ZFpure axiom is a Gam axiom. There is no closedness, depth, memory, consistency, or oracle premise on this theorem.

The other general statements are:

```coq
Theorem expanded_theorem_pure T f :
  Good T -> syms (expD Pr T f) = [] ->
  prov Gam f -> prov ZFpure (expD Pr T f).

Theorem registered_expansion_pure ds f :
  (forall d, In d ds -> In d Dall) ->
  syms (expD Pr (buildT Pr [] ds) f) = [] ->
  prov Gam f -> prov ZFpure (expD Pr (buildT Pr [] ds) f).

Corollary all_registered_expansion_pure f :
  syms (expD Pr (buildT Pr [] Dall) f) = [] ->
  prov Gam f -> prov ZFpure (expD Pr (buildT Pr [] Dall) f).
```

Expansion uses the existing proved equivalence Expand.repl and modus ponens before applying conservativity. Its fallback is Pr, retaining uncovered predicates.

## Stage 2 composition

`Stage2Conservativity2.v` imports the main framework's JudgeLink.JudgeBatch.accepted_member_sound. It proves the 677-entry Stage 2 registry sound by taking AX0 ++ DEF0 as the left prefix of the proved RpInitOk.REG0. It removes AH [] through prov_mono and composes replay soundness, faithful expansion, and conservativity.

The eleven definitions in registration order are Sub2, Sng2, Upr3, Opr3, App3, Fnc1, Emp1, Suc2, Ind1, Om1, Nat1 (symbol IDs 5, 6, 7, 8, 9, 10, 17, 18, 19, 20, 72). `stage2_table_good` proves the expansion equivalent in Gam, and `stage2_table_pure_check` kernel-checks that all eleven fully expanded bodies are pure. `covered` checks that every predicate has a table entry and the correct arity. Structural induction then proves purity for every covered formula.

```coq
Theorem stage2_theorem_pure f :
  covered stage2_table f = true ->
  prov Gam f -> prov ZFpure (stage2_expand f).

Theorem stage2_accepted_member_pure ts t :
  check_batch stage2_registry ts = true ->
  In t ts -> t_hyps t = [] ->
  covered stage2_table (tof (t_stmt t)) = true ->
  prov ZFpure (stage2_expand (tof (t_stmt t))).
```

A general `accepted_expanded_member_pure` additionally supports any sound registry and Good table whose expanded statement is pure. All premises shown are arguments of the proved theorem; they are not global axioms.

`stage2-coverage2.rkt` completed with exit 0. It read the seven current sigma1/out JDG1 files using the existing sigma1.rkt readers, checked all seven registries entry for entry against RpInit.v, checked that all 1,656 theorem hypothesis lists are empty, and matched all current hashes to the existing manifest. The statements use exactly the predicate/arity pairs (6,2), (7,3), (8,3), (9,3), (10,1), (17,1), (18,2), (20,1), (72,1), within the expansion table's vocabulary.

| Stage 2 file | Theorems | Steps | Copied prelude | Generated |
|---|---:|---:|---:|---:|
| 01-numerals.jdg | 73 | 1679 | 7 | 66 |
| 02-membership.jdg | 226 | 4168 | 13 | 213 |
| 03-distinct.jdg | 248 | 4076 | 10 | 238 |
| 04-bounded.jdg | 90 | 1596 | 13 | 77 |
| 05-arithmetic.jdg | 432 | 20508 | 24 | 408 |
| 06-sentences.jdg | 364 | 13904 | 25 | 339 |
| 07-sigma1.jdg | 223 | 7138 | 27 | 196 |
| Total | 1656 | 53069 | 119 | 1537 |

The existing sigma1/judge-run-1.txt has seven original files ACCEPT, exit 0, and seventy mutants REJECT, exit 1, from both judges. These are existing receipts; CX3 did not rerun the judges or create new JDG derivations. CX3 proves the implication from Replay2.check_batch acceptance. It does not assert a kernel computation of those seven complete batches or the pending native judge/check_batch simulation theorem assigned to the other proof lanes. The actual-file coverage check is a Racket receipt; the conservativity, table purity, registry soundness and abstract accepted-member implication are Rocq proofs.

The original sigma1/RESULTS.md gives a 154 prelude / 1502 generated split. Current indices and manifest give 119 / 1537; total 1656 and total steps 53069 agree. This correction is written here and in the new coverage receipt.

## Compiler and kernel receipts

All durations are integer differences of epoch seconds read from date.exe. Exact commands, start/end times and exits are in the companion `.receipt.txt` files.

| Module | coqc exit | coqc seconds | recursive coqchk exit | coqchk seconds | Axioms |
|---|---:|---:|---:|---:|---|
| `Conservativity2` | 0 | 3 | 0 | 135 | `<none>` |
| `Stage2Conservativity2` | 0 | 12 | 0 | 222 | `<none>` |

The first `Conservativity.v` compilation failed at line 69 because an extra bracket in the conjunction pattern requested a disjunction. `Conservativity2.v` corrects the pattern. The first `Stage2Conservativity.v` compilation failed at line 23 when buildT_good did not infer the table through its evaluated literal. `Stage2Conservativity2.v` provides the explicit convertible buildT goal. The first coverage script failed on file-name-from-path; `stage2-coverage2.rkt` imports racket/path. The initial sources and their failure receipts are present beside the corrections.

For reproducible new-file builds, copy the two final Rocq sources and run-rocq.rkt to a new empty local directory, then run the runner sequentially with `compile Conservativity2 1`, `compile Stage2Conservativity2 1`, and `check Stage2Conservativity2 1`. The runner creates logs exclusively and rejects recompiling an existing .vo. Its mappings import the original Cohen library and JudgeLink framework without writing to those directories. Run the coverage script with a new receipt path.

## File hashes

SHA256 hashes below cover every payload file present before this report was created, including preserved attempts and generated Rocq artifacts. SOURCE-HASHES.txt records the original project-source and dependency .vo hashes. MANIFEST.sha256 additionally covers RESULTS.md and STATUS.txt, excluding its own self-hash.

| File | Bytes | SHA256 |
|---|---:|---|
| `.Conservativity.aux` | 1114 | `c2992c383b125cfc4c063f035602a2b0c497f799e292391b6ae3497f6d7943b0` |
| `.Conservativity2.aux` | 1962 | `11b7900870c4ed6ca4744478d737af48a366741ac14e8413567cebbf5f39320f` |
| `.Stage2Conservativity.aux` | 471 | `b56fb24b50ad2b683c653e2578d465b19ce7611c5776e385968c7739980232e3` |
| `.Stage2Conservativity2.aux` | 2826 | `a026363a097505e31896beeb3312a3781fc7f2832fb03bb979267ba8cba39f46` |
| `Conservativity.compile1.receipt.txt` | 491 | `2ef5c0f071308b730bd4c53619f4dd1db9beb1ba4e8eda3cbf84fdbae503bf51` |
| `Conservativity.compile1.txt` | 112 | `8fc7e2fc8a0f165bba066e972e69a568f84338323a02331cda7d27b873ef5773` |
| `Conservativity.glob` | 10143 | `88093a756ac7b86a0b5d418519ff1c9ad1347554bc1d07f6d3f64bf2abe8794d` |
| `Conservativity.v` | 4258 | `a3f9cfdacc44763d4e7c52afd624507b73b49303c15982b5c619f8483098f7be` |
| `Conservativity2.check1.receipt.txt` | 513 | `65835e95c26bc67465d1ccf3447bb0f079ba95e25b38e3771142c60b14b8b82b` |
| `Conservativity2.check1.txt` | 321 | `ebb547b95eb6b78521b61161934660c24a905431f6174d36bdbeab317e57a97b` |
| `Conservativity2.compile1.receipt.txt` | 492 | `28ad058f7c3c427734830ee147f0f622a3cf8ce9d048a8e0a003cf85c9f79810` |
| `Conservativity2.compile1.txt` | 363 | `443353cc220eb9d8797aade5d49cc9ceec09f4fbc4d63a46a5d4cae49f556c6d` |
| `Conservativity2.glob` | 17086 | `b3d1d5f00c75c8d8f576d522c905e47ab132e9ab4b1beb1c0848faa1e57b2024` |
| `Conservativity2.v` | 4256 | `d3aad1691f41c0402cd8d7268ae8e1e04598792f32aef4fa8ce643efe1e5b3ca` |
| `Conservativity2.vo` | 11983 | `b8b0d634585883daf6ec07ae9234d14bcf29aba15303c290ab78418077bce7d2` |
| `Conservativity2.vok` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Conservativity2.vos` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `SOURCE-HASHES.txt` | 5414 | `2725b3ec3d86b25a2e1ecc90f8c420fbd97959bc363ececfe1d9b006b5f82aca` |
| `Stage2Conservativity.compile1.receipt.txt` | 497 | `e0220218d7b1adb67e24053d2ea0bec76d8d0d32a99a0d84d9a829117a18eb58` |
| `Stage2Conservativity.compile1.txt` | 226 | `c7dd96428570c84293976c0f7683f2a042b9336d10eb566da1df1109869b7fea` |
| `Stage2Conservativity.glob` | 4772 | `172bc7e796b26365b3ac835308eee6ba13f32f80c241bc10c0bea38ed456bf7c` |
| `Stage2Conservativity.v` | 5512 | `2825ef68875a35afa76b2bb40e10bbe3c7e58b8bc4e076c0834a3c64318f3dbf` |
| `Stage2Conservativity2.check1.receipt.txt` | 519 | `fe7be71e5a461da1a8e8add1f1f18ba24bed6797c6040f82962b9ba0f2948460` |
| `Stage2Conservativity2.check1.txt` | 321 | `ebb547b95eb6b78521b61161934660c24a905431f6174d36bdbeab317e57a97b` |
| `Stage2Conservativity2.compile1.receipt.txt` | 499 | `34d89c6652c2d3f6357ffab27b3660fff1197acf311616e7711a5453410ae456` |
| `Stage2Conservativity2.compile1.txt` | 396 | `035582f045e160e05e513a48aa2798bf6e791221921ca9aeb0bd43409681f427` |
| `Stage2Conservativity2.glob` | 26733 | `201a92787181c4bcade63b686ef23d6c82940433bb83bcc4a9ca1c579ccf5280` |
| `Stage2Conservativity2.v` | 5561 | `e14eb32bc7d4f80f809e76c7c9fbf7369efb6e303db118117743348e680c8645` |
| `Stage2Conservativity2.vo` | 26243 | `d88a9ad05d6a0d166b8229bff1e0f973fa2f93aa81a2704ababa5c52d6771407` |
| `Stage2Conservativity2.vok` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Stage2Conservativity2.vos` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `finish.rkt` | 12698 | `57087703df66f42f1f37903818740eb3fef9b5375d15adc30b43158f8a767416` |
| `run-rocq.rkt` | 2986 | `42d45a17a2272083f346124a882e03497e7588aa18f49eb0b23b368c5afe99d2` |
| `stage2-coverage-first-failure.txt` | 328 | `998c0ed69ccd3d5c444b06d5de943151fb8ab4c4810ace26785125f79e78acc3` |
| `stage2-coverage-receipt.txt` | 4563 | `57ce7e512cae1f92174737a807659fe865c914aae0973a563d2bad74aabcb38c` |
| `stage2-coverage.rkt` | 9247 | `e37373938c51ca33e8a9e32dd4febb2d73b8670655a1ce392f8ad2f9fad5cb58` |
| `stage2-coverage2.rkt` | 9259 | `7fde2befb1115791438b228c4634171cf48f8ded8f3445ef2be434d778b74b93` |
