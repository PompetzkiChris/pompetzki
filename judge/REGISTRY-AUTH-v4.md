The pmp judge and independent Racket entrypoint authenticate the submitted initial registry before checking any theorem. The accepted initial registries are exact prefixes of the proved canonical 706-entry REG0. Every formula and its hypothesis list must match. The pmp routine compares formula tags and exact decimal integers, with a delimiter after each embedded reference entry; it accepts whitespace changes and numeric leading zeros. The Racket entrypoint compares parsed dform vectors and exact hypothesis lists to immutable quoted canonical data.

Actual candidate paths:

    C:\ClaudeOutput\abschluss-repair-20261011\judge\judge-v4.pmp
    C:\ClaudeOutput\abschluss-repair-20261011\judge\judge-v4.rkt
    C:\ClaudeOutput\abschluss-repair-20261011\judge\registry-auth-v4.rkt

The pmp reference is embedded in judge-v4.pmp as a 55,854-character text literal. The Racket reference is embedded in the required code module registry-auth-v4.rkt. Neither entrypoint reads a reference JDG file at runtime. REG0-canonical.jdg is an exported development artifact; changing that file does not change either judge's embedded reference.

Canonical provenance:

    Public commit e8958a92d72c0b4cace72949510807b8a5b1320e
    Released replay-all.jdg SHA256 a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae
    CanonicalRegistryData.v SHA256 9b149f5100921e9f6228041d1350ed45bc873b2ee936772ee8952ae4d26167aa

generate-v4.rkt independently parses the 706 released registry entries, checks each entry's grammar and end, and emits the pmp reference text, Racket data, and Rocq canonical_data from the same parsed input. Native Rocq 9.1.0 checked canonical_data = Cohen.RpInitOk.REG0 by vm_compute and reflexivity, as well as length canonical_data = 706.

The Rocq prefix theorem proves reg_ok hypf (firstn n REG0) for every n. The generated-data theorem gives the same result for firstn n canonical_data. The check_thm and check_batch consequences retain the exact submitted-registry equality premise reg = firstn n canonical_data, and then apply the released Replay3 soundness theorems. The generic proof kernel check exited 0 in 18.186913 seconds, and the canonical integration kernel check exited 0 in 15.214402 seconds. All printed results are closed under the global context; both kernel checks report no axioms, type-in-type dependencies, unsafe fixpoints, or assumed positivity. Parsing, token-comparison implementation and complete executable correspondence remain separate proof obligations.

Proof files and receipts:

    judge\rocq\PrefixSoundness.v
    judge\rocq\CanonicalRegistryData.v
    judge\rocq\CanonicalPrefixSoundness.v
    judge\rocq\prefix-run-20261011-210906-291\prefix-proof-result.json
    judge\rocq\canonical-prefix-run-20261011-211231-299\canonical-prefix-proof-result.json

The portable Book API in registry-auth-v4.rkt provides:

| Name | Shape and behavior |
| --- | --- |
| canonical-registry | List of 706 pairs `(cons dform-vector hypothesis-list)`; quoted immutable vector data |
| canonical-registry-length | Exact integer 706 |
| canonical-registry-entry | Index to that entry |
| canonical-token-entries | List of 706 per-entry token lists; formula tags are strings, and counts, variable numbers, predicate numbers and hypothesis identifiers are exact nonnegative integers |
| authenticated-prefix? | Parsed entry list to Boolean, requiring exact equality to the corresponding canonical prefix |
| authenticated-token-prefix? | Per-entry raw token lists to Boolean; decimal digit strings are normalized to exact integers, including numeric leading zeros, before exact prefix comparison |

The token list for an entry includes the formula followed by the hypothesis count and identifiers. It excludes the JDG1/R header and excludes any theorem data. Canonical prefixes of length 0 through 706 are accepted by the API. A longer initial registry, an altered entry, a changed hypothesis list, and decimal token strings such as 0.0 are refused.

The corrected interpreter/source test suite at registry-tests-v4b contains 15 cases and 29 runs. All 29 pass with the expected verdict and exit, with 0 timeouts. Each of the pmp and Racket judges accepted true proofs under prefixes 0, 1, 677 and 706 and numeric leading zeros with tab whitespace. Each rejected the forged registry containing forall x, not(x=x), altered first and last pure formulas, altered pure hypotheses, an altered final placeholder hypothesis, a 707-entry initial registry, false proof inputs and nonexistent registry use. The full Racket replay accepted 4,551 theorems and 139,194 steps from registry 706 to final registry 5,257, exit 0, in 3.112 seconds. Detailed commands and outputs are in registry-tests-v4b/results.json and its referenced logs; SHA256SUMS.txt covers them.

The API regression has 3,538 checks, all passing: every prefix length 0 through 706; a formula mutation, hypothesis-list mutation and token mutation at every one of the 706 entry positions; numeric leading zeros across the entire 706-entry token reference; oversized and invalid token inputs. Its output is registry-api-v4-results.json. These are finite implementation tests; the Rocq prefix theorem supplies the universal mathematical result with the exact equality premise.

The first test harness used PowerShell's automatic $input variable as a parameter and wrote empty fixtures. Its files and outputs remain in registry-tests-v4. The corrected test-registry-v4b.ps1 uses caseText and writes its new fixtures and results in registry-tests-v4b. Native compilation and its further tests are recorded separately under judge/native when complete.
