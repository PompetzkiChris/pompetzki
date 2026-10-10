# Order L8G (Grok Build), 2026-10-09

Read C:\ClaudeOutput\abschluss\docs\RELEASE-DAY-ORDERS-2026-10-09.md first; its rules bind you (new files only, in this folder; never edit an existing file; exact integers only, no floating point anywhere, including the GPU).

Task: exact-integer CUDA C kernels for the RTX 5090 on this machine, built into a DLL that pmp calls through `extern` (pmp language: C:\ClaudeOutput\pompetzki\README.md; pompetzki.exe is the interpreter). Kernels: Gaussian elimination modulo word-size primes (rank, kernel basis, determinant mod p), many primes at once, Chinese remaindering on the CPU, and integer matrix products. Every result is checked on the CPU in exact arithmetic before it is reported (rank via a nonzero minor and a kernel basis that A·K = 0 exactly over the integers).

Workload: run it on real matrices: the rank–nullity and Smith certificates lane L2D needs (C:\ClaudeOutput\pompetzki\lanes\L2D\, read-only for you) and a benchmark set from 64×64 to 8192×8192. Record GPU utilization (nvidia-smi) during the runs.

Done when: DLL + pmp extern example + CPU checks pass + timings and GPU utilization numbers in RESULTS.md; STATUS.txt one paragraph. Known mathematics and engineering only. Lane L8A (Antigravity) works on search producers in C:\ClaudeOutput\pompetzki\lanes\L8A\; do not write there.
