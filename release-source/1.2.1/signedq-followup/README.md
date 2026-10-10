Abschluss 1.2.1 — three further original signed-Q host targets proved

`source/SignedQHostProofs3.v` proves these unchanged target propositions from the selected `SignedQTargets1.v`:

```coq
Theorem q_balance_q2r : Target_QBalanceQ2r.
(* forall (z : Z) (d : positive) (u v : N) (h : positive),
     QBalancedb z d u v h = true <->
     q2r (DifferenceQ u v h) = q2r (Qmake z d). *)

Theorem q_equivalence_q2r : Target_QEquivalenceQ2r.
(* forall (u v : N) (h : positive) (U V : N) (H : positive),
     QEQuivb u v h U V H = true <->
     q2r (DifferenceQ u v h) = q2r (DifferenceQ U V H). *)

Theorem original_wire_decode : Target_OriginalWireDecode.
(* forall (a b : string) (z : Z) (d : positive),
     OriginalWireCoefficient a b z d ->
     zdecS a = Some z /\ zdecS b = Some (Zpos d) /\
     @DecRatG DecIntS a b (q2r (Qmake z d)). *)
```

These statements quantify arbitrary signed numerators, positive denominators and natural representation components. They allow unreduced fractions. The proofs introduce no size bound, normalization hypothesis, coprimality requirement, extra axiom or floating-point calculation.

The arithmetic proofs use the original `CertExtCheck.q2r_eqv` to reflect equality of exact rational values into equality of signed integer cross-products. `signed_parts` from the previous package supplies the positive-minus-negative integer identity; `nia` proves the polynomial integer equalities. The decoder proof uses the original `CertDecode2.zdecS_complete` for both strings, then supplies the original `DecRatG` witnesses and positive denominator. The `QPoly.q2r` interpretation and `CertDecode2` relations remain unchanged.

Fresh validation:

| check | result | elapsed ms |
|---|---|---:|
| coqc SignedQHostProofs3.v | exit 0 | 6,763 |
| Print Assumptions q_balance_q2r | Closed under the global context | included in coqc log |
| Print Assumptions q_equivalence_q2r | Closed under the global context | included in coqc log |
| Print Assumptions original_wire_decode | Closed under the global context | included in coqc log |
| target-only coqchk SignedQHostProofs3 | exit 0; all three proof constants checked | 2,369 |

The kernel command used `-norec CX1.signedq.SignedQHostProofs3`: it checks the new module while admitting imported dependency modules. It is separate from a recursive kernel check of the entire imported library chain. The compiler assumption reports describe the three actual target proofs.

The first helper proof in `SignedQHostProofs2.v` failed because `iffP eqP` did not directly supply the requested propositional equivalence. That source and its failed compiler log remain here. `SignedQHostProofs3.v` replaces only that helper proof with the two directions from `elimT eqP` and `introT eqP`; the three theorem targets and their original target definitions are unchanged.

The prerequisite sources and objects copied from the preceding signed-Q package are in `source/`. Selected original rational/decoder sources and objects are in `provenance/`. `source-object-associations.tsv` binds their hashes and scopes; `compiler-sha256.tsv` binds the compiler/checker executables. `SHA256SUMS.tsv` covers the package files.

The compiler mappings were:

```text
-R C:\ClaudeOutput\pompetzki\forcing-src\general Cohen
-R C:\ClaudeOutput\pompetzki\lanes\L2R L2R
-Q C:\ClaudeOutput\exact-execution-pipeline-20260924\workforce-v4\claude-second-20260924\work\formal Groebner
-Q source CX1.signedq
```

Together with `SignedQHostProofs1.signed_parts` and `SignedQHostProofs1.z_balance`, the signed-Q recovery now supplies five original universal host arithmetic/decoder targets. Object-language derivations over `Gam`, rational-object existence/domain/equivalence, closure and faithful full-`Dall` pure-ZF expansion remain separate proof targets.
