# Native judge v6 source

The primary judge is judge-v6.pmp. This version adds a necessary remaining-input-byte bound before theorem, step, and numeric-list record allocations. Each record needs at least one byte. The full decimal domain 0..999999999999 and arbitrary leading zeros are unchanged. SKIPWS, ENDTOK, RDNUM, and RDTAG are copied byte for byte from v5.

The direct compiler and Linux runtime are copied unchanged from the v5 portable snapshot. The builder pins both the new judge source hash and the existing compiler hash. It writes a new output directory and refuses existing output directories.

From this directory, with Python, Racket, NASM, and MinGW GCC on PATH:

```
python build-native.py --source ../../judge-v6.pmp --output new-windows-build --target windows
```

For both Windows and Linux artifacts on Windows, supply an installed WSL executable:

```
python build-native.py --source ../../judge-v6.pmp --output new-both-build --target all --wsl-exe wsl
```

The builder accepts explicit Racket, assembler, linker, and WSL paths. Its source hash rejects every source other than the frozen v6 program. Build logs and hashes record the actual output artifacts. Native/source/compiler correspondence remains an open proof obligation. The Racket judge is an independent implementation cross-check.

The MIT project license is included. This package makes no license claim about external build tools. SOURCE-INPUTS.json lists the exact current portable inputs and primary source. V5 source and artifacts are retained separately.
