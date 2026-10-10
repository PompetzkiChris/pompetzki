# AG12 order 2: coverage including judge logic steps

Completed: 2026-10-09T19:17:08.3988864-04:00, obtained from Get-Date.

ORDER-2.md is complete. The execution host is THEBIGMAGILLA, Alienware Area-51 AAT2265. The filesystem check returned C:, G:, and Temp; the lane path is an ordinary local directory with no link target. All writes created new files under `C:\ClaudeOutput\pompetzki\lanes\AG12-setmm-registry\`. The named round-2 rules and the earlier RESULTS.md, LOGIC-ROUTES.tsv, and COVERAGE.tsv were read. Programs are Racket; result decisions use exact integers, exact rational arithmetic, or syntactic equality.

COVERAGE-2.tsv applies the ordered dependency criterion to all 5,757 rows: every required ax-/df- label must be a numbered match or an order-counted logic route. ROUTES-2.tsv records all 85 earlier logic rows and names their JDG1 step kinds, kernel constructors, derivation basis, and binding/interpretation conditions. There are 82 counted routes, comprising 41 axioms/rules and 41 logical definitions. The three uncounted routes are ax-prv1, ax-prv2, and ax-prv3: the earlier routing table explicitly marks their provability rules/schemas as missing.

| Metric | Exact count |
|---|---:|
| cohort_rows | 5757 |
| cohort_provable_assertions | 5753 |
| cohort_syntax_assertions | 4 |
| source_labels | 167 |
| numbered_registry_matches | 8 |
| logic_routes | 85 |
| covered_logic_routes | 82 |
| missing_logic_routes | 3 |
| registry_only_covered | 22 |
| covered | 4798 |
| newly_covered | 4776 |
| covered_provable_assertions | 4794 |
| covered_syntax_assertions | 4 |
| covered_empty_dependencies | 22 |
| uncovered | 959 |
| full_signature_sensitivity_covered | 4796 |
| conditional_route_coverage_difference | 2 |
| blocker_labels | 77 |
| distinct_missing_sets | 164 |
| first_1000_source_theorems_covered | 1000 |
| first_1000_cohort_rows_covered | 1000 |
| cohort_decoded_dependency_differences | 0 |
| independent_exact_checks | 135946 |
| independent_discrepancies | 0 |
| original_artifacts_bytes_and_mtimes_unchanged | 59 |
| sample_JDG1_files | 10 |
| judge_runs | 20 |
| sample_theorems | 10 |
| sample_steps | 12 |
| sample_registry_entries_per_file | 0 |
| sample_declared_hypotheses_per_file | 0 |

The eight numbered matches retain the earlier mapping: ax-ext -> 0 Ext, ax-pr -> 1 Pair, ax-un -> 2 Union, ax-pow -> 3 Power, ax-inf2 and ax-inf -> 4 Inf, ax-reg -> 5 Found, and ax-ac -> 6 Choice. The coverage output preserves source theorem order, assertion indices, full dependency lists, and statements. It adds the routed labels with their step kinds, remaining missing labels and counts, and the two-class-route sensitivity columns. All first 1,000 source theorem rows are covered under the new criterion.

The order-counted class routes ax-frege52c and ax-frege54c retain their stated lowering conditions. ax-frege52c needs an explicit interpretation of arbitrary class substitution; ax-frege54c needs class equality lowering, with direct Y reflexivity for set operands. Excluding these two conditional routes changes coverage by 2 rows, from 4,798 to 4,796. The main 4,798 count follows the instruction to count every earlier judge-routed logic entry. Logical definitions use their recorded capture-avoiding source expansions; class operations and their missing source definitions remain in the dependency lists. Coverage is a dependency-availability calculation. The judge verdicts below validate the ten generated instances.

BLOCKERS.tsv contains all 77 missing labels, ordered by blocked-theorem count descending and label ascending on ties. It includes the exact source extension formula, typed signature and arity, source hypotheses and disjoint pairs, new-symbol defining formula, and registration boundary. Blocked counts overlap because a row may need several labels. The single-addition gain column counts rows whose entire missing set is that label.

| Rank | Label | Theorems blocked | Unlocked by this label alone |
|---:|---|---:|---:|
| 1 | df-cleq | 550 | 173 |
| 2 | df-clel | 424 | 147 |
| 3 | df-ss | 209 | 29 |
| 4 | df-f | 69 | 4 |
| 5 | df-fn | 54 | 7 |
| 6 | ax-sep | 49 | 24 |
| 7 | df-f1 | 32 | 1 |
| 8 | df-pss | 31 | 6 |
| 9 | ax-rep | 25 | 16 |
| 10 | df-fo | 25 | 1 |

Exact enumeration gives the unique maximizing additions at each tested budget. Every subset of 1, 2, or 3 of the 77 missing labels was considered; gains count a theorem once when its complete missing set is included.

| Addition budget | Unique maximizing labels | Further rows unlocked | Total covered | Remaining uncovered | Subsets examined |
|---:|---|---:|---:|---:|---:|
| 1 | df-cleq | 173 | 4971 | 786 | 77 |
| 2 | df-clel df-cleq | 473 | 5271 | 486 | 2926 |
| 3 | df-clel df-cleq df-ss | 586 | 5384 | 373 | 73150 |

For L5, the first three additions by both frequency rank and these exact budget calculations are df-cleq, df-clel, and df-ss. Their source formulas are retained below.

| Label | Exact source extension formula |
|---|---|
| df-cleq | \|- ( A = B <-> A. x ( x e. A <-> x e. B ) ) |
| df-clel | \|- ( A e. B <-> E. x ( x = A /\ x e. B ) ) |
| df-ss | \|- ( A C_ B <-> A. x ( x e. A -> x e. B ) ) |

The gains assume these exact source-signature additions are supplied. Definitions retain class operands, free formula parameters, binders, hypotheses, and distinct-variable conditions. Asserted axioms require a derivation or asserted schema; naming the assertion body supplies an abbreviation. MISSING-SETS-2.tsv lists all 164 distinct missing sets, exact membership labels, and gains after supplying each set. UNLOCK-PREFIX-2.tsv records cumulative gains from the frequency-ranked additions. Supplying all 77 missing labels covers all 5,757 rows under this criterion; every one of those 77 labels occurs in at least one required missing set.

ROUTE-CHECK contains 10 small JDG1 files proving ax-1 through ax-10 instances. Both prescribed judges were run from `C:\ClaudeOutput\pompetzki\judge\`. Each run has separate stdout/stderr and a receipt with the command, working directory, Get-Date start/finish, exit code, and verdict.

| Label | Step route | Steps | pmp exit/verdict | Racket exit/verdict |
|---|---|---:|---|---|
| ax-1 | T/STaut | 1 | 0 / ACCEPT | 0 / ACCEPT |
| ax-2 | T/STaut | 1 | 0 / ACCEPT | 0 / ACCEPT |
| ax-3 | T/STaut | 1 | 0 / ACCEPT | 0 / ACCEPT |
| ax-4 | Y/SAx distribution | 1 | 0 / ACCEPT | 0 / ACCEPT |
| ax-5 | Y/SAx vacuity | 1 | 0 / ACCEPT | 0 / ACCEPT |
| ax-6 | Y/SAx reflexivity; E/SExi; M/SMp | 3 | 0 / ACCEPT | 0 / ACCEPT |
| ax-7 | Z/SLeib equality | 1 | 0 / ACCEPT | 0 / ACCEPT |
| ax-8 | Z/SLeib left membership | 1 | 0 / ACCEPT | 0 / ACCEPT |
| ax-9 | Z/SLeib right membership | 1 | 0 / ACCEPT | 0 / ACCEPT |
| ax-10 | Y/SAx vacuity after binding | 1 | 0 / ACCEPT | 0 / ACCEPT |

The quantifier-distribution instance depends on its bound variable. The vacuity instance retains its source disjoint condition. The existential instance uses reflexivity, existential introduction, and modus ponens with witness y. The three Leibniz instances retain three free variables and cover equality and both membership positions. ax-10 starts with a body depending on x and uses vacuity after x is bound. The sample consists of axioms with no essential hypotheses; M occurs in the ax-6 derivation. The sample does not exercise G or every remaining derivation route.

All per-label step kinds are listed here; ROUTES-2.tsv retains the full source and translation metadata. T = STaut, M = SMp, G = SGen, Y = SAx, V = SInst, Z = SLeib, H = SAlli, E = SExi, L = SExel, S = SSpec, U = SUse. SAx recognizes its shape from the formula.

| Source label | Counted | JDG1 step kinds | SAx shapes |
|---|---:|---|---|
| ax-mp | 1 | M |  |
| ax-1 | 1 | T (also Y k/s/c for ax-1/2/3) | k/s/c respectively |
| ax-2 | 1 | T (also Y k/s/c for ax-1/2/3) | k/s/c respectively |
| ax-3 | 1 | T (also Y k/s/c for ax-1/2/3) | k/s/c respectively |
| df-bi | 1 | T |  |
| df-an | 1 | T |  |
| df-or | 1 | T |  |
| df-ifp | 1 | T |  |
| df-3or | 1 | T |  |
| df-3an | 1 | T |  |
| df-nan | 1 | T |  |
| df-xor | 1 | T |  |
| df-nor | 1 | T |  |
| df-tru | 1 | T |  |
| df-fal | 1 | T |  |
| df-had | 1 | T |  |
| df-cad | 1 | T |  |
| df-ex | 1 | T |  |
| df-nf | 1 | T |  |
| ax-gen | 1 | G |  |
| ax-4 | 1 | Y | dist |
| ax-5 | 1 | Y | vac |
| ax-6 | 1 | Y;E;M (or Y;V;T) | refl |
| ax-7 | 1 | Z |  |
| df-sb | 1 | T |  |
| ax-8 | 1 | Z |  |
| ax-9 | 1 | Z |  |
| ax-10 | 1 | Y | vac |
| ax-11 | 1 | V;V;T;H;H |  |
| ax-12 | 1 | Z;Y;V;T;H | refl |
| ax-13 | 1 | Y;Z;T | vac;refl |
| df-mo | 1 | T |  |
| df-eu | 1 | T |  |
| df-nfc | 1 | T |  |
| df-ne | 1 | T |  |
| df-nel | 1 | T |  |
| df-ral | 1 | T |  |
| df-rex | 1 | T |  |
| df-rmo | 1 | T |  |
| df-reu | 1 | T |  |
| df-cdeq | 1 | T |  |
| df-2reu | 1 | T |  |
| df-bnj17 | 1 | T |  |
| df-3nand | 1 | T |  |
| ax-prv1 | 0 | none |  |
| ax-prv2 | 0 | none |  |
| ax-prv3 | 0 | none |  |
| df-bj-nnf | 1 | T |  |
| ax-luk1 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-luk2 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-luk3 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-wl-13v | 1 | Y;G;T | vac;refl |
| df-redundp | 1 | T |  |
| ax-c5 | 1 | V |  |
| ax-c4 | 1 | Y;T | dist;vac |
| ax-c7 | 1 | Y;V;T | vac |
| ax-c10 | 1 | V;Y;V;T | refl |
| ax-c11 | 1 | V;Z;T;H |  |
| ax-c11n | 1 | V;Y;Z;T;H | refl |
| ax-c15 | 1 | V;Z;T;H |  |
| ax-c9 | 1 | V;Z;Y;T;H | vac;refl |
| ax-c14 | 1 | V;Z;Y;T;H | vac;refl |
| ax-c16 | 1 | V;Z;T;H |  |
| ax-frege1 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege2 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege8 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege28 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege31 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege41 | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege52a | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege54a | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege58a | 1 | T (also Y k/s/c for ax-1/2/3) |  |
| ax-frege52c | 1 | Z;V;T;H (conditional) |  |
| ax-frege54c | 1 | Y(refl) for represented sets; T;G after class-equality lowering (conditional) | refl for set-variable instance |
| ax-frege58b | 1 | V;Y;Z;T;H | refl |
| df-vd1 | 1 | T |  |
| df-vd2 | 1 | T |  |
| df-vhc2 | 1 | T |  |
| df-vhc3 | 1 | T |  |
| df-vd3 | 1 | T |  |
| df-ich | 1 | T |  |
| df-als | 1 | T |  |
| df-rals | 1 | T |  |
| df-alseu | 1 | T |  |
| df-ralseu | 1 | T |  |

INDEPENDENT-VERIFICATION-2.tsv records 135,946 exact checks with zero discrepancies: all coverage rows and original source metadata, all route flags, all blocker ranks/counts/formulas and extension fields, all missing-set memberships and rational gain ratios, and all ranked addition prefixes. VERIFY-2.tsv checks the unchanged bytes and mtimes of 59 original artifacts and all 20 judge-run outputs. Launcher-owned codex-run.log and codex-run-2.log are captured as changing logs in the checksum snapshots.

The table below hashes every file present immediately before RESULTS-2.md was created. SHA256-2.tsv is the final recursive snapshot and supplies actual hashes for RESULTS-2.md, STATUS-2.txt, and the delivery verification receipt. SHA256-2.tsv excludes itself; its detached digest is supplied with the handover. SOURCE-SHA256-2.tsv hashes the external read-only decision and judge sources. ORIGINALS-SHA256-2.tsv records the 59 original artifact identities used by the preservation check.

| Local relative path | Bytes captured | SHA256 |
|---|---:|---|
| BLOCKERS.tsv | 73576 | EC7D2EF1149FF1FDA45B1151E1DA13821048EA5201258A4039B50588459C2414 |
| CLASS-FREE.tsv | 1052625 | 480201A2E19F625D3BEC4E8FE0C13679C7FFD8BCC634197E30CCC5D327FE78EF |
| COVERAGE-2.tsv | 2107830 | C46DAB3D94EA1191CD0CC81F07033F745C1A363500EE32A295EA4D9A9F1586E1 |
| COVERAGE.tsv | 1046266 | EBDAD02AD4409EC1E67518C7F0352A4BE248121C973D90E7A1E0D5963D7754B1 |
| EXTENSION-FORMULAS-v2.tsv | 203395 | CAA6D242B93C76FCA11842348174F972DB2CBEA80401B3179F4F1D069CCC12C9 |
| EXTENSION-FORMULAS.tsv | 105761 | 8812AE398688FAB33B07EC20E5DC23B397D9D65E5F2420B687E482F7E6B110C0 |
| EXTENSION-VERIFY.tsv | 5649 | 3D96D69144F375DEDEB4D9AEE8433F816D517315C264BC30B1305195AD9A88B4 |
| INDEPENDENT-COVERAGE-2.tsv | 13741 | 2E2B1ABE69AC0E348D7DC7D70B5A53BFD2FA2B634C5081F1C1628F234647A061 |
| INDEPENDENT-FINAL-AUDIT-2.tsv | 2407 | DE248EE37B6C202979D238992B58205D16B68B440C21AE1393E2D03C40FC36B5 |
| INDEPENDENT-VERIFICATION-2.tsv | 2407 | DE248EE37B6C202979D238992B58205D16B68B440C21AE1393E2D03C40FC36B5 |
| INVENTORY.tsv | 264 | D9458789557BE4D011070547CE9BAD373CE5EE76D451456D4B85014CF16994C8 |
| LOGIC-BOOLEAN-CHECK.rkt | 2963 | 8C3AC0166FFF2FC53BBF98E7E4A55D08FAD5983980989F7D5E1919636AAB6CB9 |
| LOGIC-BOOLEAN-CHECK.tsv | 445 | B6C34E7CDA60E4783C6DF647CEA516D0E74295A33B1C0093ADE6CCE03E9B0390 |
| LOGIC-MATCHES.tsv | 17132 | E9281464161234D6A6F2AF75FD4A53735F4E32904B2E17A9D87D5104CA4C7E98 |
| LOGIC-ROUTES.rkt | 8221 | 86EEA03ECA1C7589F76B53BA0FF453AF5CF0A3D616AA13358973C4AFCC50CCAF |
| LOGIC-ROUTES.tsv | 17132 | E9281464161234D6A6F2AF75FD4A53735F4E32904B2E17A9D87D5104CA4C7E98 |
| LOGIC-SOURCE-UNION.tsv | 11403 | 70A02189B9477EF7213DFF908883C0A97C5C66BAE993E9BFE3FAE0254CDC4CC8 |
| LOGIC-SOURCE.rkt | 1762 | 89D94B091DEE1FE1F38D2E6820748F3F1712DE75E6202E13BC6E3A2175454EF8 |
| MAP-SUMMARY.tsv | 253 | 8A5F50E836A79FE0DAD0E542D92EDEAFCF9E94AB5F356A3D97B2447EC75D3EAC |
| MAP.tsv | 255280 | E5F9CFF5E5DCEFDD46E7F852CB0C25CC475315F6532BD981C7AF888F8C2D10F8 |
| MATCH-ANALYSIS.md | 5353 | F5D09A4C5EC4A75D60717168029983E1F755258AD10564FB8FB4A1F6AEA41986 |
| MATCH-VALIDATION.tsv | 146 | 467417E4D6AEBD9F9B6DA50A9C442AA246A1F5952D7F2D141B2466D6A1A1200E |
| MISSING-SETS-2.tsv | 13801 | 7BFCC14C0F66147E69B3D4E9D0A230F456A8FF35A6C972DBFF78694EC628C104 |
| OPTIMAL-ADDITIONS-2.tsv | 527 | 4E44547EC3B11F539FAB8DDC10BA112992635DB74338E73C23F96963C4BB1E9D |
| ORDER-2.md | 1604 | B5F3F1C7E4A0AA2C821E16BE55E28EBB7BBB54E365D620A06899EADA8D117F73 |
| ORDER.md | 1588 | FC95AAAD9C189E46D7E9A45A3FD71A7EC17E72F1EB1B186E69DDCDBC2C146CFF |
| ORIGINALS-SHA256-2.tsv | 5955 | 18E2DB9C7CEFF683D74077C8F811051FBF6A287B11A8A67815B39769FDC90B7C |
| REGISTRY.tsv | 338504 | 4DEC9446A76D3A1A802C5B15CF590DEC6CA82149A01432C34A398DA6B8B023C4 |
| RESULTS.md | 17940 | 74285F785512E2F7F6B155058E9265E024C78A55C6DB757BBBE440D7BB4A3C35 |
| ROUND2-METRICS.tsv | 600 | E6A386A9051FF3660FD1DF03C36A5E2EAA3D7FEAAB5C0B507B8FC4054E910D43 |
| ROUTE-CHECK\MANIFEST.tsv | 1292 | FD4E050E77324A56AC5A6FDCAC41404A3C0EB0FEE4231EF2394FFACDDCEC54A1 |
| ROUTE-CHECK\READOUT.md | 1372 | 2352B25332311BB7BEE6C533E0506DD66508934805A74EF34281BFCE5AC67AB8 |
| ROUTE-CHECK\ax-1.jdg | 71 | 6BFDB283418058D2A562B4367330189AE4DFE10E899141529FADFD84AA067F64 |
| ROUTE-CHECK\ax-1.pmp.run.txt | 480 | DCE7F3947999AE6E88EE4C3AAA3CFE6C77ED51FBB099B152FE578CD9AA9C8809 |
| ROUTE-CHECK\ax-1.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-1.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-1.racket.run.txt | 485 | 86221ACAB93013EA17849A4DB93948491390CE1B20F3EDB47778F02A96DC8E9B |
| ROUTE-CHECK\ax-1.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-1.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTE-CHECK\ax-10.jdg | 71 | 840E961EAF92542DD280BFD255B1E70D8C9B96D9D4977EB4EBDF5C281EBCA59F |
| ROUTE-CHECK\ax-10.pmp.run.txt | 483 | 69C8C5D418E19908BA9FA2F4D10AA0D70F072701B6B7B35DFA7E817184D1BBC4 |
| ROUTE-CHECK\ax-10.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-10.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-10.racket.run.txt | 488 | F30B9BA1AF1F76B922B17728F2556D41E2C386A9814F3E462E69AE5F7D02C2AE |
| ROUTE-CHECK\ax-10.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-10.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTE-CHECK\ax-2.jdg | 135 | 7BB7DB8F0AEA1E8326E4636773F7BB8F9DCB0F4A8B4B189B9209193397F9F2EC |
| ROUTE-CHECK\ax-2.pmp.run.txt | 480 | 80A95555D36D629D87A28809AEC1926EF12CAF883D58357C2827AC9F4348AC39 |
| ROUTE-CHECK\ax-2.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-2.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-2.racket.run.txt | 485 | 1A78E7DA1A70B8998E4B5453706BD4FFFA6D5DB1FA13DF49E75B4DCD0E0E168A |
| ROUTE-CHECK\ax-2.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-2.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTE-CHECK\ax-3.jdg | 95 | 42EFBAC8E3D2C4E856EFAC161EA4D49694463E2404D2D7775F60D5C1AA091AD4 |
| ROUTE-CHECK\ax-3.pmp.run.txt | 480 | 8E55D1BB89A6680A0F9316DC54598C9F1706FDA173D50024EF410F50129FAFED |
| ROUTE-CHECK\ax-3.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-3.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-3.racket.run.txt | 485 | DF026A34E2E2A7281C2431FDBA6836B4E3D635DDEE47ECE27B9D4494D5D58820 |
| ROUTE-CHECK\ax-3.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-3.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTE-CHECK\ax-4.jdg | 97 | E757C6D01410DDF399E93F9C77CE09FC8ADA42D528AFBEF27799BEE62B5124D4 |
| ROUTE-CHECK\ax-4.pmp.run.txt | 480 | 098A29CA84B213645BA3D2ECFCD0DFC199F0C188C17E989E3C3EAF8BDACB07EA |
| ROUTE-CHECK\ax-4.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-4.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-4.racket.run.txt | 485 | 4AECFF471D397F43A825BC8BE95E6AFA2E1C304DDA536EE094F6AB2C2A80A1AF |
| ROUTE-CHECK\ax-4.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-4.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTE-CHECK\ax-5.jdg | 57 | 9CF75F2DD0388811D102BACC53AD064DF308F4375494A3765AAC977F0AEE0AE6 |
| ROUTE-CHECK\ax-5.pmp.run.txt | 480 | 6B938EEBD854D053E2F4142FB2EA47B91F6E4697560D89A15FCC6F2C049750AD |
| ROUTE-CHECK\ax-5.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-5.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-5.racket.run.txt | 485 | 72BC14284F9ACF880479DDA4CDC7055105133199421CAD4A2D1EAB8A6AC866C1 |
| ROUTE-CHECK\ax-5.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-5.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTE-CHECK\ax-6.jdg | 71 | 1D95CB3EBBC25B02FCC1938E87B2F7B916547A5C0B70F24C699A6B6E216BE498 |
| ROUTE-CHECK\ax-6.pmp.run.txt | 480 | DFFEEBFD69B5D07F022DC96AA1AEBC827BC7A466E217E34566A84D2FBBABA433 |
| ROUTE-CHECK\ax-6.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-6.pmp.stdout.txt | 109 | 887B187AEBBD8D61ABCF478B779F811924581050063839EED2857715724D54CB |
| ROUTE-CHECK\ax-6.racket.run.txt | 485 | 1A5E532EEC0A3EDF2542069E5C9D82CF4D2884D01E6CC7188DDFBAB33251DBCB |
| ROUTE-CHECK\ax-6.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-6.racket.stdout.txt | 54 | 74C623F5030061617ED1518BD56B05BA1BEBDC4F5126B779D2A14699C58EA976 |
| ROUTE-CHECK\ax-7.jdg | 77 | 1B9E0DD0F725793F2D5FF03C001B1E393749EFB3C455FAE08A5D953EF8808D89 |
| ROUTE-CHECK\ax-7.pmp.run.txt | 480 | 1E569C26B5DC365E62DF201129894962B547F291B53A5E89BB8FD3A6FC0FFBCD |
| ROUTE-CHECK\ax-7.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-7.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-7.racket.run.txt | 485 | B21294A8EA53C4C9B30EE3CB652515E2B6F1BC27BF9B68B83D0518141AD3CF17 |
| ROUTE-CHECK\ax-7.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-7.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTE-CHECK\ax-8.jdg | 77 | FFE79B4E920437D1DC83B9269CFCC5E181A8F1539B6B213E2E9BEED270EE7041 |
| ROUTE-CHECK\ax-8.pmp.run.txt | 480 | B6CDBD8DD9E646DB9433934C008F9F62C6C1EE590E5807DE14901314B655A020 |
| ROUTE-CHECK\ax-8.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-8.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-8.racket.run.txt | 485 | 5720B7B0B0AE129C52C76D017D2CF48ADB0ABFBBAB7C9E80A09255A5CBD49999 |
| ROUTE-CHECK\ax-8.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-8.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTE-CHECK\ax-9.jdg | 77 | 0052867E904F5D3F639653C5D0D3092AE962413EF05E6F0775130B759E5F93A0 |
| ROUTE-CHECK\ax-9.pmp.run.txt | 480 | DD99BCA8A9F0A2836F6F45C2C814B27559403F2115C161D5B5A9CCF6BBE265A0 |
| ROUTE-CHECK\ax-9.pmp.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-9.pmp.stdout.txt | 109 | 5D8138F0191D84671CD0B2F99F06AFA1FA427A19762136EC2EC6038B28D86B76 |
| ROUTE-CHECK\ax-9.racket.run.txt | 485 | 9AC4145F7B210904736D1856B31E5ED2A3BBA7CCA98574F98EE77DE06F6351F1 |
| ROUTE-CHECK\ax-9.racket.stderr.txt | 0 | E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 |
| ROUTE-CHECK\ax-9.racket.stdout.txt | 54 | BAA019BA21A4AC65F462EB348BFBED62801D98F533051F1D62A982261CC94F6B |
| ROUTES-2.tsv | 51533 | 92EB80EE4BEB819BA03A092A3930C53CE089A4525D43A4273ED8D0AAD2A80ED9 |
| RUN-BY.txt | 159 | DEC44F46F5493E5EF3DE79CDB4DF291B158FE235634CD1D31713A4A10A84CB75 |
| SET-CANDIDATES.tsv | 3639 | 350566D4DD90997DA1AD35BB6BD7FC316023CC54B558DBFBECBF91885A434464 |
| SET-DERIVATION-SOURCES.md | 5001 | 6C2A0141705EF0D3A9CCFF4D921DE6DCB50916477E27F54F68D590FED7797682 |
| SET-EXTENSION-PROTOTYPES.tsv | 3262 | 8448C9A236F65097B42CF80C7F26430809736AD27478419CF7135ABF042F421D |
| SET-MATCH-ANALYSIS.md | 14456 | 53FAF2D284C0291443E66524D0135ED084CD8765CACD60EAC170DC16223C3DC3 |
| SHA256.tsv | 5679 | 99C670DBB91CBA157F445B7E2AFC989351AF884B01B3C1B08A6FE2FCFBBB9CB9 |
| SOURCE-LABELS.tsv | 16312 | 8EAD9A0376F14D8962C5DE5389AC7C59BCECEA5988BC8426FE48D96E4B0C85E7 |
| SOURCE-SHA256-2.tsv | 1407 | 4385CE2748F6B3E7D39527B1BEBE418EF064AE88DD8C0710010803E090864E81 |
| SOURCE-SHA256.tsv | 2226 | 0CE3A58617DF5F7A0E8822AB974DE069FCD5B155A8CE9115A1C4B937977C1185 |
| STATUS-2.txt | 1069 | 9FD1EDDAEDE65F6FA9941DAAB42ED8B4709FA0531D36E381DA4FE80A1AE5DF9E |
| STATUS.txt | 923 | F0A8F9766947D28FE38D9B80764D2391E8C6CD480EF9A738927FE095467BE12B |
| UNLOCK-PREFIX-2.tsv | 24389 | 71FC6999E3CEA0C7C5922222C5E21270B3AFF90717D69FAA01628F40A7E4B64A |
| VERIFY-2.tsv | 211 | FCDD16D946D7901A961A4D219B5E6C56663CD0FC555D3C2B33E72903897DFF0A |
| VERIFY-FINAL.tsv | 386 | DB67420454E8116603A3A106ACFB6ABBF39C58A86C76ECDB1EC0FFFEBFE2A05B |
| codex-run-2.log | 1568519 | F62759FC02012EC06494D36B4727209577077ADC1D588CABED6C74E475390871 |
| codex-run.log | 1089978 | DC98BD1DD5F2CAC98D569744A80DBBD46CF878A8C2431D6A9DBB9046AEC16A55 |
| extension-formulas-v2.rkt | 7808 | 35472DED7678D4CA63DE232D49CA42935B80EB37A7D53ACD3CF6A37E6B9A0E8D |
| extension-formulas.rkt | 11418 | 00EB4C3A860234C0034B22F92EA990B6C652C7A9395F3307BFCF7CC994EC640D |
| extension-verify-v2.rkt | 4014 | 9356F9A6D548AC0F5E6B65D6CE19971EFB64F3E3FFD1844482BCA25CD7C6B868 |
| extension-verify-v3.rkt | 3998 | 0C485E19D0BFDC93FD488C4BD2FCDAFEDF20C12372121379391F89663EA456A5 |
| extension-verify-v4.rkt | 3993 | 486B89CFED0FD08C5B7D9745EF93AAC18CBA607253320B3C55A4B786DE899377 |
| extension-verify.rkt | 4013 | 40B711F67DCBAD0625FF9BEE22ED47234A241EE3522B9DA63F6842D4F25FE0B7 |
| independent-coverage-verify-2-v2.rkt | 8652 | 5D8428788B7C4AFCB8D2FAA79304AA0D30FECFC0441A0AF42B63C6B9F1926998 |
| independent-coverage-verify-2.rkt | 8636 | B9C74BBEC899F7583A8D394DCBADDCC2BB42AC4E5E67FB54820BC6AF7A178902 |
| independent-final-audit-2.rkt | 11887 | 57F5B171A84E73CE34DF9C837468D5FF7D4B1DFE3AD997F13EC9D65545F19F01 |
| independent-summary-tables-2.rkt | 2757 | 18591C65A295146DB274B9DA709817296BF6D998E366BED500DD41F5864A8B47 |
| inventory-v2.rkt | 7702 | 6155BAF8FE22C9E146A26FC60C18678E20973D2300EF343780D4ABAB5EA2E834 |
| inventory-v3.rkt | 7716 | D784F2E079E9FDD93DC40090D30E51F19AB1EC9F41205C681A1D4A9F02A9A8C5 |
| inventory-v4.rkt | 7747 | 9F0A2CDFD0D18E778242CAA041366AB5698A248BC559F9BA0687BED4E7B5A663 |
| inventory.rkt | 7674 | EF5277E1854420D0E9AB40424E1E44040CA2721669048748A3788180FDE882FE |
| launch.end.txt | 9 | D42B623579D3C387BF919421BE14A8E7C7CEAEABAE2C7953FFA079E5BE35E41D |
| launch.start.txt | 9 | 53C9F8B66F107FDB2C16B741BEEC65BBC8AB19F0EA98C91B748A2B99A9CC5332 |
| launch2.start.txt | 9 | F023DA7F93ACA749951790CF6A62114441CCCC82388583F276F44A92DA7B193B |
| make-map-v2.rkt | 9759 | 3CACAD8FE71E58CDC14231680CCF1D89C516265A88A4CF14F6152FFBF907E0D0 |
| make-map.rkt | 9762 | 5BDC577FEBD8CD9CE1AEF1F6312412D5DC8339696C0B329902FA83E332925746 |
| mm-extension-existence.rkt | 17201 | B0E93DB53DFCFE0CEEEB8E23A65BA0E374FCB2C56E8DEF3261010A9F4C0743DD |
| mm-extension-inspect.rkt | 17286 | 6C48379E8D3FC8028D6347A40AD099BF38D8B9A098BBF0B9BC235E776B5A3469 |
| recompute-round2.rkt | 10382 | 44162482FF8DAB65CD3CE03F9D688919478ADCE4729A459B534C3457C6CE3D6A |
| registry-correction-01.rkt | 370 | 0AC0A0F25E509BEF6973B8B3418CC755629C70368DDBF9CF8DA88EACB7CE0228 |
| registry-correction-02.rkt | 948 | 9A1A0DD4199B037A625CEF82A8CF3FBEFAF1FEF894A6F1CB3CBF8696FE6E4B68 |
| registry-reader-v2.rkt | 12405 | D6A72D16C1725FC7A15353D2A6B1443C238583DC5EEF4CA224FED6F2F0C53DD9 |
| registry-reader-v3.rkt | 12434 | 19A1F74EFA59B4A463E4AAA4DB451A1A4D01E0A33E62B65F10A5A8AD33F7D3B5 |
| registry-reader.rkt | 12407 | 34996CFCE6BD0370870C7DA9AFD62FBE786179FE78F0AEBF6EE8264F27B9AE5C |
| round2-core.rkt | 1440 | 9378C0B9581D2E8F032BDFE6D619A7A8CE46B482173E0FE524F43555C31DD57B |
| route-check-round2.rkt | 8905 | 5985B8C38EC1831EFAAF86E8311BBF401BBC86017A2DBFDFC8B4047CE6DC1164 |
| route-classification-2.rkt | 8697 | B5673788D3B8768900C49317736F7184F66607482F91821A641C111B67539692 |
| set-candidate-writer.rkt | 6510 | 8AB02D8099E4BAD902A89B84B7C5785C34E67BF90AB9E6CE807581F0068B248F |
| set-extension-prototypes.rkt | 7839 | 7364F194C9D1558D5FE985252FE51889D12F05D177AA895F0E30096FC750A040 |
| snapshot-round2.rkt | 1513 | AAE3391B8C37B03673CB55C520F0D17810DB1A68A830DE598E69F14BA4C33784 |
| verify-final.rkt | 4676 | 395849853F6C04AF921F10CBB1E9B26BBA3C6B28A5C2D789E6B47C27D445C37A |
| verify-round2-v2.rkt | 3765 | C7938C2749FCCDA749785A9829D77147C6B726B88B5E528929C1CC8181AF3D58 |
| verify-round2.rkt | 3766 | C71B78A1D4B6876F40A6AD3EBAABA7CBD215DE346DAC3E79ED4D18882B7B9789 |
| write-report-v2.rkt | 14939 | EFBAE0B1ADA694F716880EFF4772746212295D91DD0084D92E5D7DB3AED3EB6E |
| write-report-v3.rkt | 14943 | 4F60EB5E49A59FFEC3B890BCD4AFBD72197D7E4163749CBA32AA9D5370041F62 |
| write-report.rkt | 14452 | 514A62E8DEEAF54AF1A4CCA172D463F389F643FB11C0C65A99AAFCDD4D83076D |
| write-results-round2.rkt | 12970 | 031E7CB024D0364E28431EDF4422EF1389693FA5845B33A649B507584C078D60 |
| RESULTS-2.md | Recorded in SHA256-2.tsv | Actual digest in SHA256-2.tsv |
| VERIFY-DELIVERY-2.tsv | Recorded in SHA256-2.tsv | Actual digest in SHA256-2.tsv |
| SHA256-2.tsv | Detached snapshot | Detached digest in final handover |
