# Portable native gate source

This directory contains the direct pmp compiler snapshot, its Linux syscall runtime adapter, a portable builder, provenance, and the project's MIT license. The compiler's Windows kernel32 runtime is embedded in `pmpc-original.rkt`. The program compiled by the builder is the frozen `judge-v4.pmp`, SHA256 `c0698f6c00310e4cf95147d4ddfbfab0f8c06d00aa8f9ca1da8482123c073e33`.

The complete source layout is:

```text
judge/judge-v4.pmp
judge/native/portable/build-native.py
judge/native/portable/pmpc-original.rkt
judge/native/portable/linux-runtime.asm
judge/native/portable/LICENSE
judge/native/portable/PROVENANCE.json
judge/native/portable/README.md
```

The builder uses Python 3 standard libraries. The compiler uses the standard Racket modules `racket/string`, `racket/list`, `racket/file`, and `racket/port`. It has no project-local include or runtime dependency. Install Racket, NASM, and the linker toolchains separately. Windows uses an x64 MinGW GCC driver with the system kernel32 import library. Linux uses NASM and GNU ld. Tool paths may be supplied explicitly; the defaults are looked up through PATH. No compiler or assembler binaries are bundled in this source directory.

From the source package root, build Windows on Windows with:

```text
python judge/native/portable/build-native.py --source judge/judge-v4.pmp --output build-windows --target windows
```

Build Linux directly on Linux with:

```text
python3 judge/native/portable/build-native.py --source judge/judge-v4.pmp --output build-linux --target linux
```

Build both on Windows using a configured WSL distribution with:

```text
python judge/native/portable/build-native.py --source judge/judge-v4.pmp --output build-both --target all --wsl-exe wsl --wsl-distro Ubuntu-24.04
```

Omit `--wsl-distro` to use the machine's configured default distribution. WSL path conversion uses that distribution's `wslpath`; no drive letter or mount prefix is fixed in the builder. `--racket`, `--nasm`, `--windows-cc`, `--linux-nasm`, and `--linux-ld` accept executable paths or PATH names. Building both directly on Linux requires an installed x64 MinGW cross compiler; its default command is `x86_64-w64-mingw32-gcc`.

Every build requires a new output directory and preserves existing artifacts. It produces `build-result.json`, raw per-step stdout/stderr, and `SHA256SUMS-build.txt`. The Windows executable takes a JDG pathname argument. The Linux executable does the same. Accepted inputs print ACCEPT with exit 0. Registry/proof rejections print REJECT with exit 1. The Linux runtime exits 2 for missing input or an input open/read error.

The source compiler emits direct instructions for pmp statements and uses fixed 8-byte variable cells. A literal statement refers to static literal bytes. The gate reads its AUTHREF and WHY bytes without changing them. The Linux adapter changes startup, external service calls, and the runtime while retaining the original statement lowering. These basic runtimes do not supply triple-copy/string-integrity protection.

The retained finite native test receipts cover 132 cases per platform: 14 registry fixtures, the 4,551-theorem replay with 139,194 steps, and 117 public v1.2 math cases. All expected verdicts passed, and paired Windows/Linux outputs and exits matched. Source-to-native and executable-to-Gallina `check_batch` correspondence proofs remain open. These tests and build receipts are finite evidence.
