# AG12 set.mm registry mapping

Completed: 2026-10-09T19:08:21.0664434-04:00, obtained from Get-Date.

The authoritative output directory is `C:\ClaudeOutput\pompetzki\lanes\AG12-setmm-registry\`. Execution host was verified as THEBIGMAGILLA, Alienware Area-51 AAT2265. The observed filesystem drives were C:, G:, and Temp. The lane directory was an ordinary directory with no link target. All program and artifact writes were confined to this existing lane directory, with creation-only file operations. Inputs outside the lane were read-only.

MAP.tsv maps every ax-* and df-* label used by the specified AG8 cohort. It contains exact source statements, mandatory variables and their types, essential hypotheses, disjoint-variable constraints, registry indices/names and printed formulas, match classes, named derivations, typed new-symbol definitions, and separate qualified set-specialization candidates. COVERAGE.tsv contains every cohort assertion in set.mm order and its required labels, missing labels, and registry-only coverage flag.

| Metric | Exact count |
|---|---:|
| set.mm assertions | 50912 |
| AG8 class-free cohort | 5757 |
| Actual decoded class-free assertions | 5757 |
| Provable assertions in the cohort (|- type) | 5753 |
| Syntax assertions in the cohort (wff type) | 4 |
| Cohort dependency-list differences | 0 |
| Unused compressed-proof assertion table entries | 0 |
| Relevant ax-* labels | 80 |
| Relevant df-* labels | 87 |
| Total MAP rows | 167 |
| Numbered registry counterparts | 8 |
| Identical up to renaming and universal closure | 2 |
| Equivalent by named derivation | 6 |
| No counterpart for the full source signature | 159 |
| Axiom/rule labels without a numbered counterpart | 72 |
| Definition labels without a full-signature numbered counterpart | 87 |
| Qualified set-specialization candidates | 10 |
| Registry-only covered cohort rows | 22 |
| Covered provable assertions | 18 |
| Covered syntax assertions | 4 |
| Covered rows with empty dependencies | 22 |
| Registry-only uncovered cohort rows | 5735 |
| First 1000 registry-only covered rows | 2 |
| AX0 axioms | 7 |
| DEF0 definitions | 670 |
| Registry entries | 677 |
| Symbol-table symbols | 686 |
| Direct source/registry structural checks | 3 |
| Typed source-extension formulas | 167 |
| Definition right-hand sides extracted | 87 |
| Logical analysis rows | 85 |
| Logical axiom/rule analysis rows | 44 |
| Logical definition analysis rows | 41 |
| Propositional axiom truth tables | 15 |
| Exact integer Boolean assignments | 84 |
| False assignments | 0 |
| Extension source-formula equality checks | 167 |
| Typed definition RHS/LHS roundtrips | 87 |
| Outer equation reconstructions | 86 |
| Primitive biconditional expansion assignments | 8 |
| First-order set-definition prototypes | 11 |
| Verified named set derivation source assertions | 11 |
| Read-only input checksum rows | 16 |
| Existing and generated artifact checksum rows before RESULTS.md | 55 |

The numbered matches are ax-ext ->0 Ext, ax-pr ->1 Pair, ax-un ->2 Union, ax-pow ->3 Power, ax-inf2 and ax-inf ->4 Inf, ax-reg ->5 Found, and ax-ac ->6 Choice. Ext and Power match after universal closure and alpha conversion. Pair uses equality substitution and specialization; Union uses existential-antecedent conversion; Foundation uses quantifier negation; Inf2 uses conjunction commutation. The alternate Infinity and Choice formulations use named ZF equivalences relative to the other ZF axioms and the stated schemas, including Foundation. The named top-level derivations delegate to established source proofs. The Infinity witnesses are axinf and axinf2. Choice equivalence is recorded directly by dfac0 and dfac5, with ac8 and axac describing the alternate forms. SET-DERIVATION-SOURCES.md retains the actual source assertions, source line numbers, and compressed-proof reference tables. No bound on the fully expanded length of those two ZF conversions is asserted.

The strict coverage count uses the numbered AX0 ++ DEF0 registry alone. Its22 covered rows all have empty axiom/definition dependencies. Their labels, in source order, are:

`idi`, `a1ii`, `weq`, `pm11.07`, `wel`, `conventions`, `conventions-labels`, `conventions-comments`, `natded`, `dummylink`, `mathbox`, `bj-0`, `wl-section-prop`, `wl-section-boot`, `wl-section-impchain`, `wl-impchain-com-1.1`, `iddii`, `sn-wcdeq`, `idiALT`, `iin1`, `iin2`, `iin3`.

The cohort includes 4 wff syntax assertions; all 4 occur in that covered list. Thus 18 of the 22 covered rows are |- assertions. Logical proof constructors and syntax expansions explain why a theorem may be translatable despite failing this literal registry-only dependency criterion. The first 1000 source theorems use ax-mp, ax-1, ax-2, ax-3, df-bi, df-an, and df-or; their proof rules and connective expansions are documented separately from the numbered registry. This report records dependency coverage, rather than judge-accepted translations.

The source class variables have their full class signatures. A class-abstraction-free proof may still use proper classes, primitive class constants, and class-valued operations. The ten qualified candidates require set representatives or additional hypotheses; they do not increase full-signature coverage. They are df-ss, df-br, df-tr, df-ord, df-cleq, df-fun, df-fn, df-f, df-f1, and df-isom. For example, Sub2 matches subset for represented sets. Fnc1 alone permits nonpair members and therefore needs graphhood for the source function definition. SqD2 and Sq3 also impose a natural-number domain. The qualification formulas and counterexamples appear in SET-MATCH-ANALYSIS.md and SET-CANDIDATES.tsv.

EXTENSION-FORMULAS-v2.tsv supplies all 167 exact source formulas, typed mandatory signatures, operator operands, binder names, dummy variables, and explicit new-symbol defining formulas. MAP.tsv includes those columns directly, so all 159 no-counterpart rows have the requested formula and arity information. For class-valued definitions the exact extension is a membership schema with a fresh set element argument. Formula operands and arbitrary class operands require capture-avoiding formula translation with their free parameters; they are not fixed arguments ranging over sets. The arity columns therefore distinguish typed schema arity from fixed set-predicate arity. Where the full source signature has no fixed first-order predicate arity, the table states that fact and gives the set-restricted arity or instance-based translation boundary.

An axiom or inference rule cannot be supplied by a conservative definition alone. For those rows the exact source assertion, premises, and constraints are retained; the displayed predicate alias names the assertion body and does not assert it. Missing mathematical axioms require a derivation or an asserted extension. The source Prv operator needs an explicit provability interpretation or modal syntax/rules. The complex-number and Hilbert-space primitives need their own fixed interpretations and derivations. These are mathematical signature boundaries, rather than omitted formulas.

SET-EXTENSION-PROTOTYPES.tsv gives 11 exact closed first-order definitions for represented sets, with hypothetical new symbol IDs 686 through 696: Rel1, Fun1, Fn2, Map3, Inject3, Onto3, Bijection3, RelPres5, Isom5, DomExact2, and Er2. Every row includes arity, source label, scope, named defining formula, and de Bruijn formula. All 11 passed closure, declared-arity, named-prefix and dform roundtrips, and body-scoping checks. They retain graphhood, exact domains, exact ranges, and the source relation arguments. No registry was modified.

The independent compressed-proof pass decoded actual label uses for all source proofs and reproduced 5757 class-free assertions, with 0 queue dependency differences and 0 unused assertion references in compressed tables. All 677 registry formulas were checked against their named Data.v/lib sources, declared predicate arities, closure, and printing roundtrips. Additional structural checks independently parsed the source Ext, Power, and Inf2 formulas. Fifteen propositional axiom formulas passed 84 exhaustive exact integer 0/1 assignments with 0 false results. VERIFY-FINAL.tsv checks map/source/extension label equality, all 159 missing-formula/arity records, all 8 numbered references, and every coverage row and its order. EXTENSION-VERIFY.tsv records 167 source-formula equalities, 87 typed RHS/LHS parse roundtrips, 86 exact outer-equation reconstructions, and 8 integer Boolean checks of the primitive df-bi expansion. Overlapping wi and bj-0 syntax trees were handled by choosing a complete typed parse for existence and exact token roundtrip; no uniqueness claim is made. All result decisions use exact integers or syntactic equality. No JDG1 file was generated, so the two-judge rule produced no acceptance claim.

The working scripts create new files only. inventory.rkt, inventory-v2.rkt, and inventory-v3.rkt stopped at the AG8 footer; inventory-v4.rkt handles its comment/footer rows. make-map-v2.rkt corrects a local binding in the first map script. Registry-reader correction versions, extension-table versions, and verification variants are preserved alongside their completed versions. Programs use the full Racket executable path and single-process substantive jobs, bounded to at most 4 active workers. This run finished before the 20-minute periodic-status interval and before the required delivery deadline. STATUS.txt is the final paragraph.

The checksums below cover bytes captured at finalization. SHA256.tsv includes the actual RESULTS.md and STATUS.txt checksums and every other file present at that snapshot except SHA256.tsv itself. Its own checksum is printed by the reporting program and supplied with the final handover. The launcher-owned codex-run.log is a changing log; its checksum and byte count identify the captured snapshot. SOURCE-SHA256.tsv records all decision-source inputs and their filesystem modification times.

| Artifact | Bytes captured | SHA256 |
|---|---:|---|
| CLASS-FREE.tsv | 1052625 | `480201A2E19F625D3BEC4E8FE0C13679C7FFD8BCC634197E30CCC5D327FE78EF` |
| COVERAGE.tsv | 1046266 | `EBDAD02AD4409EC1E67518C7F0352A4BE248121C973D90E7A1E0D5963D7754B1` |
| EXTENSION-FORMULAS-v2.tsv | 203395 | `CAA6D242B93C76FCA11842348174F972DB2CBEA80401B3179F4F1D069CCC12C9` |
| EXTENSION-FORMULAS.tsv | 105761 | `8812AE398688FAB33B07EC20E5DC23B397D9D65E5F2420B687E482F7E6B110C0` |
| EXTENSION-VERIFY.tsv | 5649 | `3D96D69144F375DEDEB4D9AEE8433F816D517315C264BC30B1305195AD9A88B4` |
| INVENTORY.tsv | 264 | `D9458789557BE4D011070547CE9BAD373CE5EE76D451456D4B85014CF16994C8` |
| LOGIC-BOOLEAN-CHECK.rkt | 2963 | `8C3AC0166FFF2FC53BBF98E7E4A55D08FAD5983980989F7D5E1919636AAB6CB9` |
| LOGIC-BOOLEAN-CHECK.tsv | 445 | `B6C34E7CDA60E4783C6DF647CEA516D0E74295A33B1C0093ADE6CCE03E9B0390` |
| LOGIC-MATCHES.tsv | 17132 | `E9281464161234D6A6F2AF75FD4A53735F4E32904B2E17A9D87D5104CA4C7E98` |
| LOGIC-ROUTES.rkt | 8221 | `86EEA03ECA1C7589F76B53BA0FF453AF5CF0A3D616AA13358973C4AFCC50CCAF` |
| LOGIC-ROUTES.tsv | 17132 | `E9281464161234D6A6F2AF75FD4A53735F4E32904B2E17A9D87D5104CA4C7E98` |
| LOGIC-SOURCE-UNION.tsv | 11403 | `70A02189B9477EF7213DFF908883C0A97C5C66BAE993E9BFE3FAE0254CDC4CC8` |
| LOGIC-SOURCE.rkt | 1762 | `89D94B091DEE1FE1F38D2E6820748F3F1712DE75E6202E13BC6E3A2175454EF8` |
| MAP-SUMMARY.tsv | 253 | `8A5F50E836A79FE0DAD0E542D92EDEAFCF9E94AB5F356A3D97B2447EC75D3EAC` |
| MAP.tsv | 255280 | `E5F9CFF5E5DCEFDD46E7F852CB0C25CC475315F6532BD981C7AF888F8C2D10F8` |
| MATCH-ANALYSIS.md | 5353 | `F5D09A4C5EC4A75D60717168029983E1F755258AD10564FB8FB4A1F6AEA41986` |
| MATCH-VALIDATION.tsv | 146 | `467417E4D6AEBD9F9B6DA50A9C442AA246A1F5952D7F2D141B2466D6A1A1200E` |
| ORDER.md | 1588 | `FC95AAAD9C189E46D7E9A45A3FD71A7EC17E72F1EB1B186E69DDCDBC2C146CFF` |
| REGISTRY.tsv | 338504 | `4DEC9446A76D3A1A802C5B15CF590DEC6CA82149A01432C34A398DA6B8B023C4` |
| RUN-BY.txt | 159 | `DEC44F46F5493E5EF3DE79CDB4DF291B158FE235634CD1D31713A4A10A84CB75` |
| SET-CANDIDATES.tsv | 3639 | `350566D4DD90997DA1AD35BB6BD7FC316023CC54B558DBFBECBF91885A434464` |
| SET-DERIVATION-SOURCES.md | 5001 | `6C2A0141705EF0D3A9CCFF4D921DE6DCB50916477E27F54F68D590FED7797682` |
| SET-EXTENSION-PROTOTYPES.tsv | 3262 | `8448C9A236F65097B42CF80C7F26430809736AD27478419CF7135ABF042F421D` |
| SET-MATCH-ANALYSIS.md | 14456 | `53FAF2D284C0291443E66524D0135ED084CD8765CACD60EAC170DC16223C3DC3` |
| SOURCE-LABELS.tsv | 16312 | `8EAD9A0376F14D8962C5DE5389AC7C59BCECEA5988BC8426FE48D96E4B0C85E7` |
| SOURCE-SHA256.tsv | 2226 | `0CE3A58617DF5F7A0E8822AB974DE069FCD5B155A8CE9115A1C4B937977C1185` |
| STATUS.txt | 923 | `F0A8F9766947D28FE38D9B80764D2391E8C6CD480EF9A738927FE095467BE12B` |
| VERIFY-FINAL.tsv | 386 | `DB67420454E8116603A3A106ACFB6ABBF39C58A86C76ECDB1EC0FFFEBFE2A05B` |
| codex-run.log | 962623 | `14D28D18FB3F96D550A98098ECB7AE441CE56A8869BF201CAD18BAE6A645B9ED` |
| extension-formulas-v2.rkt | 7808 | `35472DED7678D4CA63DE232D49CA42935B80EB37A7D53ACD3CF6A37E6B9A0E8D` |
| extension-formulas.rkt | 11418 | `00EB4C3A860234C0034B22F92EA990B6C652C7A9395F3307BFCF7CC994EC640D` |
| extension-verify-v2.rkt | 4014 | `9356F9A6D548AC0F5E6B65D6CE19971EFB64F3E3FFD1844482BCA25CD7C6B868` |
| extension-verify-v3.rkt | 3998 | `0C485E19D0BFDC93FD488C4BD2FCDAFEDF20C12372121379391F89663EA456A5` |
| extension-verify-v4.rkt | 3993 | `486B89CFED0FD08C5B7D9745EF93AAC18CBA607253320B3C55A4B786DE899377` |
| extension-verify.rkt | 4013 | `40B711F67DCBAD0625FF9BEE22ED47234A241EE3522B9DA63F6842D4F25FE0B7` |
| inventory-v2.rkt | 7702 | `6155BAF8FE22C9E146A26FC60C18678E20973D2300EF343780D4ABAB5EA2E834` |
| inventory-v3.rkt | 7716 | `D784F2E079E9FDD93DC40090D30E51F19AB1EC9F41205C681A1D4A9F02A9A8C5` |
| inventory-v4.rkt | 7747 | `9F0A2CDFD0D18E778242CAA041366AB5698A248BC559F9BA0687BED4E7B5A663` |
| inventory.rkt | 7674 | `EF5277E1854420D0E9AB40424E1E44040CA2721669048748A3788180FDE882FE` |
| launch.start.txt | 9 | `53C9F8B66F107FDB2C16B741BEEC65BBC8AB19F0EA98C91B748A2B99A9CC5332` |
| make-map-v2.rkt | 9759 | `3CACAD8FE71E58CDC14231680CCF1D89C516265A88A4CF14F6152FFBF907E0D0` |
| make-map.rkt | 9762 | `5BDC577FEBD8CD9CE1AEF1F6312412D5DC8339696C0B329902FA83E332925746` |
| mm-extension-existence.rkt | 17201 | `B0E93DB53DFCFE0CEEEB8E23A65BA0E374FCB2C56E8DEF3261010A9F4C0743DD` |
| mm-extension-inspect.rkt | 17286 | `6C48379E8D3FC8028D6347A40AD099BF38D8B9A098BBF0B9BC235E776B5A3469` |
| registry-correction-01.rkt | 370 | `0AC0A0F25E509BEF6973B8B3418CC755629C70368DDBF9CF8DA88EACB7CE0228` |
| registry-correction-02.rkt | 948 | `9A1A0DD4199B037A625CEF82A8CF3FBEFAF1FEF894A6F1CB3CBF8696FE6E4B68` |
| registry-reader-v2.rkt | 12405 | `D6A72D16C1725FC7A15353D2A6B1443C238583DC5EEF4CA224FED6F2F0C53DD9` |
| registry-reader-v3.rkt | 12434 | `19A1F74EFA59B4A463E4AAA4DB451A1A4D01E0A33E62B65F10A5A8AD33F7D3B5` |
| registry-reader.rkt | 12407 | `34996CFCE6BD0370870C7DA9AFD62FBE786179FE78F0AEBF6EE8264F27B9AE5C` |
| set-candidate-writer.rkt | 6510 | `8AB02D8099E4BAD902A89B84B7C5785C34E67BF90AB9E6CE807581F0068B248F` |
| set-extension-prototypes.rkt | 7839 | `7364F194C9D1558D5FE985252FE51889D12F05D177AA895F0E30096FC750A040` |
| verify-final.rkt | 4676 | `395849853F6C04AF921F10CBB1E9B26BBA3C6B28A5C2D789E6B47C27D445C37A` |
| write-report-v2.rkt | 14939 | `EFBAE0B1ADA694F716880EFF4772746212295D91DD0084D92E5D7DB3AED3EB6E` |
| write-report-v3.rkt | 14943 | `4F60EB5E49A59FFEC3B890BCD4AFBD72197D7E4163749CBA32AA9D5370041F62` |
| write-report.rkt | 14452 | `514A62E8DEEAF54AF1A4CCA172D463F389F643FB11C0C65A99AAFCDD4D83076D` |
| RESULTS.md | Recorded in SHA256.tsv | Actual digest in SHA256.tsv |
| SHA256.tsv | Reported at completion | Detached digest in final handover |

| Read-only input | Bytes captured | SHA256 |
|---|---:|---|
| C:/ClaudeOutput/formalization-toolchain-20260924/libraries/metamath-set-mm-28167ed89a49/set.mm | 51401872 | `F14BFA0B2AF830C4E722CEE84EEB0C0E5F885F9E61FA433F71802ACB1AE5AD17` |
| C:/ClaudeOutput/pompetzki/forcing-src/general/Ax.v | 6120 | `A452BC702BC8B33D4EE83AA7EEC013BB8899C6019C3E02D01407A67CBC051829` |
| C:/ClaudeOutput/pompetzki/forcing-src/general/Data.v | 98999 | `5BCEA58DD0B3C4F95E7560369B352083D3AF56088FE61459E7642F33A675C6B2` |
| C:/ClaudeOutput/pompetzki/forcing-src/general/Prov.v | 3580 | `D794DAFA01CF4E13C262FCC40EE775ED237D18642D36EFD30FDB40AD0C7A859C` |
| C:/ClaudeOutput/pompetzki/forcing-src/general/Replay2.v | 10867 | `E4D94FA3B02C95441D3F86B45876A026B81C84C6AF100A248FA32629B99867AC` |
| C:/ClaudeOutput/pompetzki/forcing-src/general/RpInit.v | 84950 | `9421B47EEEED5FA9F16DD599C33E7181991DEE700638D5043D8FA55114ADD97F` |
| C:/ClaudeOutput/pompetzki/forcing-src/general/Syn.v | 6962 | `65A7E01796EA28462C3F5F5ED52BEFC3620227CFEA8162F0FCF33CA2EFEE5A51` |
| C:/ClaudeOutput/pompetzki/forcing-src/general/replay/mkreplay.pl | 17671 | `033486269868A7EF611E491179769DBCE6CACBC2302DC0E7C90D8B6F6E0D6A39` |
| C:/ClaudeOutput/pompetzki/lanes/AG8/RESULTS.md | 5972 | `0692F2770C6DC79753C166CE0B09E65183E85CACE857345CB40B37B1BB1E440E` |
| C:/ClaudeOutput/pompetzki/lanes/AG8/setmm_priority.rkt | 29632 | `29097946EB8D032F4D0996C68D5261E7F90F52CE76698246A7245A2EF7CEE228` |
| C:/ClaudeOutput/pompetzki/lanes/AG8/setmm_queue.tsv | 76749721 | `3D5FD3F5FD5036498912739ED529620F1099CD4125BE41ECF9CD4953AE6DD6C0` |
| C:/ClaudeOutput/pompetzki/lanes/AG8/summary_counts.tsv | 2392 | `0DF1D40EC15E16D9EC0CD0846447137C2691446CBC0DA1534747BA7494FF36E4` |
| C:/ClaudeOutput/pompetzki/lanes/L5/mm2jdg7.rkt | 45803 | `DE9DA1A9D457FE6B128092C4283FA0F55509B938FCEF43D478943D6CA3EC131D` |
| C:/ClaudeOutput/pompetzki/lanes/L5/mm3.rkt | 17277 | `4F95924C4641272B5362655223C4ED7EF0FC068AE7BCD9BB1EA17982E05B8607` |
| C:/ClaudeOutput/pompetzki/lanes/RULES-ROUND2-2026-10-09.md | 1927 | `DFB64B0F697D7343769B3B698963F67CF6CC2EEE6492CE1D45B02A93AFB768FB` |
| C:/ClaudeOutput/pompetzki/lib/zfc.pmp | 30772 | `64D822ED7378C924660FEB98E9AF727A2B753F16213C4CD84129021932CD09F5` |
