# Native canonical-registry gate

The Windows executable `judge-v4-windows.exe` and Linux ELF `judge-v4-linux` compile the frozen `../judge-v4.pmp` source, SHA256 C0698F6C00310E4CF95147D4DDFBFAB0F8C06D00AA8F9CA1DA8482123C073E33.

Each executable passed 132 cases: 14 registry cases (5 ACCEPT, 9 REJECT), the full 4,551-theorem replay with 139,194 steps, and all 117 public v1.2 math cases (78 ACCEPT, 39 REJECT). All 132 output files and exit codes matched across Windows and Linux. There were zero timeouts and zero unexpected verdicts. `native-test-result.json` contains every input SHA256, exact command, exit code, duration and output path; raw stdout/stderr are under `test-logs`.

Windows: `judge-v4-windows.exe FILE.jdg`. Linux: `./judge-v4-linux FILE.jdg`. With no Linux pathname argument the runtime exits 2. A registry rejection prints REJECT and exits 1. An accepted batch prints ACCEPT and exits 0.

The compiler snapshot is `compiler/pmpc-original.rkt`, copied byte for byte from `C:\ClaudeOutput\pompetzki\pmpc\pmpc.rkt`. Its embedded Windows runtime uses kernel32. Linux uses the new `linux-runtime.asm` syscall adapter with the original core statement lowering. Variables are single fixed 8-byte cells. Literal statements refer to static literal bytes; the frozen gate reads AUTHREF and WHY without changing those bytes. The new artifacts use the frozen pmp gate directly. The separate L4 jdgchk source and the independent Racket judge are not embedded.

Build into a new directory with `python build-gated-native.py FULL_PATH_TO_judge-v4.pmp NEW_OUTPUT_DIRECTORY`. It requires Racket, NASM, MinGW GCC and WSL Ubuntu-24.04 with NASM/ld. The build script preserves every existing artifact. `reproduce-build/build-result.json` records a second successful build. Assembly source hashes match the tested build; all allocated PE/ELF section bytes and their addresses also match. Absolute filename symbol metadata and the PE timestamp give different whole-file hashes.

The retained r60 smoke build returned FAULT on the tested registry cases and is excluded from the release recommendation. Its artifacts remain beside the successful builds. The basic compiler runtimes do not provide the r60 triple-copy/string-integrity protection.

The full source-to-native and executable-to-Gallina check_batch correspondence proofs remain open. These receipts establish the recorded finite builds and runs.
