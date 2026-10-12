# ASCII decimal proof addendum

The received Grok Bot ASCII decoder and its exact type and assumption receipt are copied unchanged. The original DecimalSignificantV4 model and prior GrokNumericGaps proofs retain their source bytes. The fresh local build compiled four project modules with Rocq 9.1.0, checked all 27 received statements, and recursively checked the resulting proof objects. Every statement is closed under the global context. The kernel reports no axioms, type-in-type, unsafe fixpoints, or assumed positivity. The platform-library count in the received report is not used as a project proof count.

The decoder consumes `list Z`. It accepts exactly integer values 48 through 57 as ASCII digits, subtracting 48 before invoking the existing numeric model. Every other integer is refused, including integers outside the byte range 0 through 255. The statements therefore apply to byte-valued lists as a subset of their integer-list domain. This does not assert that arbitrary integers are physical bytes.

`ascii_padding` retains the premise `bs <> []`. `ascii_all_zeros` retains `(1 <= n)%nat`. The empty token refuses; adding one zero byte to the empty token accepts zero, so dropping the padding premise would change the statement. More than twelve significant digits refuse, while arbitrary leading zero bytes are allowed. Accepted values lie in 0 through 999999999999. Fixed-width and minimal spellings both round-trip over that range, with arbitrary leading zero padding.

Signs and delimiters are outside the surrounding tokenizer model. As bytes inside this complete unsigned token, plus, minus, spaces, commas, and newlines refuse. The statements do not prove that actual RDNUM, pmp or Racket tokenization, compiled code, or executable bytes implement these functions. The remaining correspondence obligation is stated in `review-boundaries.json`.

The supplemental source checks 22 concrete boundary examples. These include the empty-padding counterexample, nonempty all-zero tokens longer than twelve bytes, maximum value, thirteen significant digits with and without padding, malformed token bytes, integer values outside 0 through 255, and round trips at zero and the maximum. They add one compiled example module to the four-module core; they are counted separately from the 27 received statements.

Run the source-only build with Python and Rocq on PATH:

```text
python build-ascii-decimal-proof.py --output fresh-build
python check-ascii-boundaries.py --core-build fresh-build --output boundary-build
```

Both drivers accept explicit `--coqc` and `--rocqchk` paths. They create new output directories and fail if a chosen output already exists. The boundary driver verifies the public source hashes against the completed fresh core build, compiles its example module, and recursively checks the dependencies again.

`ascii-types-and-assumptions.txt` contains the fresh raw output of every received type and assumption query. `logs/` contains raw stdout and stderr of the compiler and both recursive kernel runs. The result files record relative commands, source hashes, exit codes, and tool version. Compiled objects are excluded from this public addendum.

The actual received archive hash is 23c359431aec35ef055a7f733742701092b66df85be894202d904ddf540ba2ba. Its 27 manifest entries comprise delivered files and contextual aliases, source, release ZIP, and object hashes. The current verification is `archive-manifest-verification-v2.json`: 25 entries are checked against received bytes or local release-source bytes, and two undelivered build-object context entries remain classified as context. Received compiled objects are retained privately as delivery evidence and were not used in the fresh build. The initial verification file is retained as historical context.

The MIT project license and source credit are included. No license claim is made about the Rocq toolchain itself. `PUBLIC-SOURCE-MANIFEST.json` is the authoritative explicit payload list; `SHA256SUMS.txt` also hashes that manifest.
