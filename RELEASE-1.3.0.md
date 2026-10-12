# Abschluss 1.3.0

This release adds an editable exact matrix workspace and authenticates the initial registry before a certificate can receive an ACCEPT verdict. It also repairs embedded-zero byte strings, signed minimum literals, signed minimum division by minus one, padded certificate integers, and verified Book posting and rejudgment.

Open `Abschluss Start.exe`, enter integer or rational matrix entries in A and B, select an operation, and click Compute. Answer shows the result. The workspace computes RREF, rank and nullity, kernel and image bases, particular and homogeneous solutions of Ax=b, inconsistent systems, determinant, inverse, transpose, addition and multiplication. It supports explicit zero dimensions and arbitrary integer/rational matrix entries. Decimal and exponent input are refused. Font controls and file import/export are included.

The launcher menu runs the authenticated pmp judge and the independent Racket cross-check, creates a posting from freshly judged copied inputs, verifies a posting by fresh rejudgment, and checks installation hashes. The installer creates a fresh local folder and shortcut. The uninstaller removes listed unchanged program files while retaining additional and modified files.

The matrix engine and built-in integer/rational matrix operations use exact arithmetic. The interpreter's Word64 interface retains its declared wrapping operations: minimum signed word divided by minus one wraps to the minimum word, and its remainder is zero. Certificate indices in both v5 judges have the declared domain 0 through 999999999999; any number of insignificant leading zeros is accepted, and a thirteenth significant digit is refused before arithmetic.

The Book verifier checks chain hashes, copied input and output hashes, current tool hashes, receipt consistency, exact ordered timing fields, record identities and links, theorem hypotheses, statement and derivation hashes, and recorded trace fields. It reruns both judges on the copied input. Ledger metadata is unsigned; a hash chain alone does not authenticate a past execution. The supported posting command executes the judges itself, and the supported verification command performs fresh rejudgment.

Executed validation for the current sources includes:

- 898 v5 judge runs: 254 each on Windows native, Linux native and Racket, plus 136 interpreted pmp runs. There were zero unexpected verdicts or timeouts. Native Windows/Linux output and exits agree on all 254; native/interpreted pmp agree on all 136.
- A 94-certificate bot corpus with 23 valid controls, 24 proof-step mutants, 14 final-statement mutants, 17 registry-authentication mutants and 16 malformed parser inputs. Malformed input is counted separately from semantic proof coverage.
- The full 4,551-theorem replay, with 139,194 proof steps, on both native judges and Racket. Book posting and fresh rejudgment preserve 4,373 Proved and 178 Qualified entries.
- An independent Fraction matrix corpus: 429 cases, 7,288 exact mathematical identity checks and 3,754 engine jobs, including 179 inconsistent systems, with zero failures. The earlier independent 849-case matrix suite also passes source and compiled engine routes.
- The received Linux runtime harness independently rerun on a fresh local build: 1,493 cases, zero failures. The Windows division/remainder harness passes 740 cases, and the earlier 918 exact tool cases pass on each rebuilt Windows interpreter.
- Fresh Rocq compilation and recursive kernel checking for the canonical-prefix and authentication gate proofs. Seven authentication lemmas and five decimal-policy lemmas report closed assumptions, without added axioms or unsafe flags.

The two judges agree on the tested verdicts. One retained math mutant has different refusal classifications: native pmp reaches a proof step, whereas Racket reports an unexpected step tag. Route-specific classifications are retained in the public validation corpus.

The GUI tests invoke the owned application's actual Compute callbacks in hidden frames. Physical interaction with a visible desktop window is a separate acceptance boundary. Parser denotation, executable checker correspondence with Gallina, compilation semantics and shipped-byte correspondence remain open formal proof obligations. The original theorem statements and hypotheses are preserved.

The source asset includes the NASM interpreter and native compiler source, project license and source credit, portable builders, proof sources, independent test drivers and the pinned historical vendor asset used by the bundle builder. Current package build and installation receipts are included in its provenance. Earlier public releases and prior correction artifacts remain at their existing paths.
