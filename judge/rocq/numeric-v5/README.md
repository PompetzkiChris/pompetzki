The source DecimalSignificantV4.v models the decimal policy of the v5 judge using exact integers. The module name records the fourth saved proof attempt. The earlier attempts remain in the local proof work directory; the public source whitelist includes the completed module.

The model parses decimal digits, skips leading zeros while the significant count is zero, and refuses a further significant digit when that count is 12. It proves that accepted values lie in 0..999999999999, adding leading zeros preserves the result, and the guarded arithmetic lies below 2^63. Empty numeric input is excluded by parse_decimal. A separate certificate parser checks delimiters and digit characters.

Rebuild from the packaged source with:

    python judge/rocq/numeric-v5/build-decimal-proof.py fresh-decimal-proof

Rocq compiler and recursive kernel checker executables are found on PATH. Explicit executable paths may be supplied with --coqc and --kernel. The output directory must be new. The builder copies the pinned proof source, captures command outputs and exits, and writes hashes.

This module does not prove a correspondence with executable tokenization, the pmp interpreter, the direct compiler, the Racket implementation, or generated native bytes. Canonical registry prefix soundness remains in the separate prefix proof sources. The original check_batch soundness theorem retains its valid-registry premise.
