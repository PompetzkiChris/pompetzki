# Exact mathematics repair candidate

This branch develops the next release of Pompetzki/Abschluss. Version 1.2.0 remains available as a historical release. The v1.3.0 Windows application is being assembled and tested; this branch is the source candidate.

The v4 judges authenticate the initial JDG1 registry against an embedded canonical REG0 prefix before checking a theorem. The pmp program is the primary judge and its independently implemented Racket counterpart provides a cross-check. A forged initial registry containing `forall x, not (x = x)` is rejected by both. Whitespace and leading decimal zeros remain accepted for equivalent canonical entries. A new Rocq theorem proves soundness of the canonical prefixes, under the original checker theorem's hypotheses.

The corrected NASM runtime parses the full signed 64-bit literal range, including `-9223372036854775808`, while rejecting values outside it. The corrected strx byte library preserves embedded zero bytes. Exact tool validation uses integer and rational oracles.

The verified Book command copies each JDG1 input, runs the pmp and Racket judges on the same copy, records their commands and file hashes, and then posts the checked results. It refuses an existing output directory. Unknown, timed-out, changed, or conflicting results enter SUSPENSE with exit status 3. A direct receipt-import invocation is refused. Ledger headers bind the run metadata hash.

Recorded checks at this candidate stage:

- Runtime: 918 independent exact tool cases, 32 literal boundaries, 12 valid emitted literals, and 20 invalid emitted literals passed for console and window builds.
- strx: 150 raw byte cases passed.
- Registry API: 3,538 prefix and mutation checks passed.
- Native v4 judges: 132 cases on Windows and 132 on Linux passed, with byte-identical paired output and status. These comprise 14 registry cases, the 4,551-theorem replay, and all 117 selected math confirmations.
- Verified Book: mixed valid/false inputs, decimal spelling equivalence, existing-output preservation, timeout status, and direct receipt-import refusal passed. The full replay posted 4,373 Proved and 178 Qualified entries; an independent Python implementation verified both ledger chains and the run metadata hashes.

Finite test runs do not prove executable bytes correspond to the Gallina checker. That correspondence remains an open obligation. The original closed Rocq theorem statements and their hypotheses remain the mathematical claims; an ACCEPT result is interpreted through those hypotheses and the authenticated registry.

Source locations:

- `judge/judge-v4.pmp`, `judge/judge-v4.rkt`, `judge/registry-auth-v4.rkt`
- `judge/rocq/` for the new prefix soundness statements and receipts
- `judge/native/portable/` for native compiler and runtime adapter sources
- `repair/runtime/source/pompetzki.asm` for the repaired monolithic interpreter
- `repair/libraries/strx/` for the corrected byte library
- `repair/book/` for verified posting and independent ledger verification

The editable exact matrix workspace and portable installer are under development. Release packaging will include the actual verified executables, their source, build commands, run output, and SHA-256 manifests.
