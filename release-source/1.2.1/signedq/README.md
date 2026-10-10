Abschluss 1.2.1 — signed-Q source correction and two host proofs

The four selected signed-Q modules now compile from fresh source copies. `SignedQForms1.v` required one additional closing parenthesis at original line 76, at the end of `QRepF`. The copied original failed with `Syntax error: '|' or ',' or ')' expected after [term level 200]`. The original files and compiler failure are included beside `corrected-v2/`. Every other character of `SignedQForms1.v` is unchanged; `correction-equality.txt` records that comparison. The other three selected `.v` files are byte-identical to their originals.

Fresh compiler results:

| source module | coqc exit | elapsed ms |
|---|---:|---:|
| SignedQForms1 | 0 | 387 |
| SignedQObjectForms1 | 0 | 369 |
| SignedQTargets1 | 0 | 6,306 |
| SignedQObjectTargets1 | 0 | 2,311 |
| SignedQHostProofs1 | 0 | 3,190 |

`SignedQHostProofs1.v` supplies proofs of two unchanged original target propositions:

```coq
Theorem signed_parts : Target_SignedParts.
(* forall z : Z,
   Z.sub (Z.of_N (PosPart z)) (Z.of_N (NegPart z)) = z *)

Theorem z_balance : Target_ZBalance.
(* forall (z : Z) (u v : N),
   ZBalancedb z u v = true <-> Z.sub (Z.of_N u) (Z.of_N v) = z *)
```

The first proof destructs the signed integer constructor; the second uses the exact `Z.eqb_eq` theorem and the first identity, then exact integer linear arithmetic. Both `Print Assumptions` commands report `Closed under the global context`. They quantify arbitrary signed integers and arbitrary natural operands. No bound, normalization condition, floating-point value, tolerance, new axiom or replacement target was introduced.

The five fresh objects passed a target-only `coqchk` run in 2,499 ms, exit 0. The log names all five checked libraries and both checked proof constants. The run used `-norec` for each of these libraries, so imported dependency libraries were admitted by that invocation. This package does not present that target-only check as a fresh recursive check of the entire imported Cohen/L2R/Groebner/MathComp chain.

The compiler imports used these mappings:

```text
-R C:\ClaudeOutput\pompetzki\forcing-src\general Cohen
-R C:\ClaudeOutput\pompetzki\lanes\L2R L2R
-Q C:\ClaudeOutput\exact-execution-pipeline-20260924\workforce-v4\claude-second-20260924\work\formal Groebner
-Q corrected-v2 CX1.signedq
```

`source-object-associations.tsv` binds each fresh source and object by SHA-256. `source-comparison.tsv` compares the four selected sources with their preserved originals. `selected-dependency-sha256.tsv` records the source/object hashes of selected imported interfaces and the compiler/checker executable hashes. `SHA256SUMS.tsv` covers the package files.

The original `Target_*` definitions remain proposition specifications. The two targets proved here are `Target_SignedParts` and `Target_ZBalance`. The rational-value correspondence through `QPoly.q2r`, strict decoder correspondence, object-language `prov Gam` derivations, closure, unreduced rational-object equivalence and full-`Dall` faithful pure-ZF expansion are still separate targets. Compilation establishes that their intended proposition types and formula definitions are well formed; it does not supply proofs of those targets.
