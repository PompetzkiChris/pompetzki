The included monolithic NASM source builds the exact Pompetzki interpreter. It contains the Windows kernel32/shell32 imports and its Linux syscall implementation. There are no local assembly includes or binary include files. The source revision has SHA256 778a2710b4151bad5a71c1bbdf5b5243d86d01f2a654fd727f341d589f2289db.

Build from this directory into a new output directory:

    python build-interpreter.py output --target windows
    python3 build-interpreter.py output --target linux

The Windows build uses NASM and MinGW-w64 GCC from PATH and writes both pompetzki.exe and pompetzki-w.exe. The Linux build uses NASM and ld from PATH and writes pompetzki. Explicit --nasm, --windows-linker and --linux-linker arguments select other installed tools. On Linux a MinGW-w64 cross compiler can build the Windows targets by supplying --windows-linker x86_64-w64-mingw32-gcc. Build directories are created anew. The builder preserves existing output directories.

The source checksum is enforced for the included release revision. --allow-modified-source builds an edited source and records its actual new hash in the build receipt. That flag changes the release-revision check; it does not establish correctness of the edited source.

The portable script was run from a directory containing spaces on Windows, producing both Windows subsystems, and was run by Linux Python with the same source to produce Linux ELF. All assembler/linker steps exited 0. The newly built Windows console interpreter and Linux interpreter each rejected the forged one-entry registry and accepted a true proof with canonical prefix 706 when running judge-v4.pmp.

The source is licensed under the accompanying MIT LICENSE, copyright Christopher Pompetzki. Required build tools are external dependencies and are not included in this source directory. General source-to-executable correspondence remains open; build and smoke receipts establish the recorded executions.
