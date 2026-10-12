# Exact interpreter runtime revision 2

This revision includes the signed minimum literal parser repair and the machine-word division/remainder crash guard. The monolithic NASM source has no local assembly or binary includes. Its SHA-256 is `2329d3c993abfc5a89b979e6caae0b47aabdc12ec1858d752134a71a4e014f2e`.

The imperative `set ... const` interface accepts signed 64-bit decimal and hexadecimal machine-word literals. Its `add`, `sub`, and `mul` operations store the resulting machine word. This revision gives division of INT64_MIN by -1 the consistent wrapped machine-word result INT64_MIN, and gives its remainder 0. A zero divisor is rejected. This avoids the processor exception on that operand pair.

The built-in matrix and rational interfaces support arbitrary integers and exact fractions; their matrix literals and mathematical results can exceed 64 bits. The separate Racket matrix workspace also uses arbitrary integers and rational numbers. These mathematical interfaces are distinct from the machine words used by the imperative address/bit interface.

Build into a fresh directory:

```text
python build-interpreter.py build-windows --target windows
python3 build-interpreter.py build-linux --target linux
```

The builder uses PATH or explicitly supplied NASM/linker paths, pins the included source hash, and records every command, exit status, output hash and executable hash. Windows produces console and window executables. Linux produces an ELF executable. Racket is not required to build this interpreter.

The Grok Bot Linux runtime lane discovered the division/remainder processor exception, and its accountability lane repeated it. Codex independently reproduced both crashes on Windows, then tested the new source: 740 machine-word cases and emitted programs passed across the console and window builds. The previous 918 exact tool cases passed on each new executable, for 1,836 matching runs. The original repaired source and binaries remain beside this revision.

Finite executions and source hashes do not establish a general assembly or executable-to-Gallina correspondence theorem. That obligation remains open. The compiler, parser and proof checker have separate contracts.
