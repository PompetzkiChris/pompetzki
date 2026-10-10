# Abschluss 1.2.1 recovery sources

This directory contains the verifier repair, the extracted bounded-sentence entry point, five proofs of the original signed-Q host targets, and the Book continuation and portable verification tools. Existing repository files and earlier deliverables are preserved. The release assets carry complete payloads, dependency objects, source associations and execution receipts.

## Windows release verification

`verifier/abschluss-verify-r2.rkt` binds its selected Windows ZIP to a successfully verified checksum entry, checks archive paths before extraction, locates the actual bundle root and requires a nonempty, well-formed `selftest/EXPECTED.tsv`. It requires both the judge and its interpreter. Each row must produce the exact expected verdict with the corresponding process exit code. Missing inputs, ambiguous Windows archives, traversal paths, malformed rows and diagnostic text that merely mentions a verdict cause failure. `VERIFIED` requires successful completion of every row.

`verifier/build-verifier.ps1` builds and distributes the source into a new output directory. `SOURCE-BUILD-R2.json` binds the source and executable hashes. The release asset includes the executable and standalone runtime DLLs. `VERIFIER-FAILURE-TESTS-R2.json` contains the compiled input-failure controls; the release QA receipts include the additional verdict/exit controls and complete native run.

## Exact mathematical sources

`sigma1-emitter/runtime/emit-sentence.rkt` runs the extracted `CEmitFinal_0033.emit` on closed, well-formed bounded sentences over natural numbers. A true sentence produces its translated statement; a false sentence produces the negation. Both branches have an empty additional-hypothesis list. The underlying universal theorem retains the original theory `Gam = ZFC7 OR SepAx OR CollAx OR DefAx Dall`. The Racket wrapper, extraction and text printer execute outside Rocq's kernel; their finite controls and source bindings are in the emitter release asset.

`signedq/SignedQForms1.v` corrects one missing closing parenthesis in the original source. The other original definition/target files are byte-identical to their submitted versions. `SignedQHostProofs1.v` proves `Target_SignedParts` and `Target_ZBalance`. `signedq-followup/SignedQHostProofs3.v` proves `Target_QBalanceQ2r`, `Target_QEquivalenceQ2r` and `Target_OriginalWireDecode`.

These five original universal host targets quantify arbitrary signed numerators, positive denominators and natural representation components, including unreduced fractions. Their proofs add no bounds, normalization or coprimality hypotheses, extra axioms or floating-point calculations. All five assumption reports are closed under the global context. Fresh target-module kernel checks passed with imported dependencies admitted by `coqchk -norec`; their scope is recorded separately from prior recursive-chain receipts.

The object-language derivations over `Gam`, rational-object existence/domain/equivalence, closure and faithful full-`Dall` pure-ZF expansion remain separate proof targets. The release does not establish CH O10/O11, L2R DSEP0 or generic Mathlib-universe targets.

## Book continuation

The continuation retains the first 33 journal segments byte for byte and appends 63 segments. The resulting 96-segment journal contains 648 source families, 284,207 derivation postings, 2,073 refutation postings and 17 suspense postings. The derivation statuses are 284,036 Proved and 171 Qualified; 218,370 statement hashes are distinct. Both source-record checkers pass with zero conflicts.

The source-pair decisions are 151 MERGE, 34 HOLD and 33 EMPTY. Holds remain represented in the decision/debt receipts. One historical suspense certificate has a SHA mismatch at the checked source and archived paths. It is kept as suspense, with the checked-path receipt, rather than admitted as a derivation or refutation.

`book/BUILD.md` describes the continuation. The portable asset preserves absolute provenance fields and binds them to staged relative payloads through `PATH-ALIASES.tsv`. It includes admitted source ledgers, certificates, judge receipts, a SHA-256 manifest, two Racket source-record checkers and an independent Python journal/payload checker. The release receipts record fresh archive extraction and checks.

## Build and receipt scope

These files are the changed and selected sources, not a replacement for every imported library source. Each mathematical asset includes its selected dependencies and exact logical module mappings. The Windows asset supplies its standalone runtime. The Book asset supplies its journal, ledgers and admitted payloads.

`SOURCE-SHA256.tsv` binds the source files in this directory. Public asset checksums bind the separately packaged executable, proof and Book bytes. Native judge controls assess the delivered CLI workflows; a physical GUI interaction test is a separate workflow.
