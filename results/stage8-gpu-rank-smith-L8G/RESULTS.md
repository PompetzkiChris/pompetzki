# L8G results

`C:\ClaudeOutput\pompetzki\pompetzki.exe example.pmp` exited 0 on Fri 10/09/2026. The run log is `example-run2.txt`. The process certificate is `example-process-2.txt`. The DLL wrote `C:\ClaudeOutput\pompetzki\lanes\L8G\out2\`.

`l8g_api_version` returned 1 (`check zero` printed `zero: yes`). `l8g_workload` returned 0 (`check zero` printed `zero: yes`, and `out2\summary.txt` ends with `workload 0`). pmp then printed `l8g checks passed`. The certificate records 8 of 8 claims established, 51 statements executed, 1084 rational operations, largest integer at most 2 × 64 bits, and `end: every obligation discharged`. Program sha256 `92a8132dfc7fac0392c18ab80fe00c915cf6426e245c66773ded86bc6b02772d`. Interpreter sha256 `ccf835920e566b8a45468654798fb9577a261cfec171a707e0438696515a3bec`.

Clock lines from `out2\summary.txt`:

```
date_start
Fri 10/09/2026
06:55 PM
date_end
Fri 10/09/2026
07:01 PM
```

## DLL

`C:\ClaudeOutput\pompetzki\lanes\L8G\l8g.dll`, built from `src\l8g.cu` with `nvcc -O3 -arch=sm_120 -cudart static -shared`. Static cudart. Integer types only. Device log: `device cc 12 0`. Eight primes in (2^62, 2^63), first prime `4611686018427388039`. `selftest 0`.

Kernels used on the workload: Gaussian elimination modulo those primes (rank, kernel basis, determinant mod p), eight primes in one launch, Chinese remaindering of the kernel on the CPU, and an integer matrix product C = A·A. Each GPU result was compared with a CPU check in exact arithmetic before the summary line was written.

## pmp claims on the files the call wrote

| claim | files | result |
|---|---|---|
| A·K is the zero matrix | `out2\pmp_A.txt` (6×8), `out2\pmp_K.txt` (8×4) | established |
| leading minor determinant is nonzero | `out2\pmp_minor.txt` (4×4) | established |
| rank + nullity = number of columns | same A | established |
| exact rank equals the GPU rank | `out2\pmp_gpu_rank.txt` holds 4 | established |
| unit triangular determinant is 1 | `out2\pmpT_A.txt` (5×5) | established |
| U·S·V equals the Smith form | `out2\pmp_smith_{S,U,V,D}.txt` (3×3) | established |
| det(U) is ±1 | det(U)^2 equals the 1×1 identity | established |
| det(V) is ±1 | det(V)^2 equals the 1×1 identity | established |

Dumped Smith form of the 3×3 is diag(1, 1, 8). Sign of det U is 1, sign of det V is 1.

An earlier invocation, logged in `example-run.txt` and `out\`, reached `workload 0` and then stopped at `line 11: syntax` because the `load` paths were quoted. `load matrix` takes a bare path token. Those files remain. The numbers below are the later run, the one whose pmp claims closed.

## CPU verdicts inside the DLL

Smith form, modular proof that U·A·V = D and that det U and det V are ±1:

| tag | shape | sign det U | sign det V | bits U | bits V |
|---|---|---|---|---|---|
| known246 | 3×3 | 1 | 1 | 3 | 3 |
| smith4x6 | 4×6 | 1 | 1 | 10 | 5 |
| smith6x8 | 6×8 | -1 | -1 | 12 | 7 |
| smith8x8 | 8×8 | 1 | -1 | 24 | 13 |

`snf_check_known`, called from selftest, checks [[2, 4], [6, 8]] to diag(2, 4) and diag(2, 4, 6) to diag(2, 2, 12), including the integer products U·A·V.

Rank certificates (GPU elimination, CRT kernel compared with the integer kernel, A·K = 0, bottom of K equal to I, nonzero leading minor, minor compared mod 2^31−1):

| case | rows | cols | rank | nullity | primes | ge_ms | minor mod 2147483647 | minor det | max abs entry |
|---|---|---|---|---|---|---|---|---|---|
| rn6x8 | 6 | 8 | 4 | 4 | 4 | 1 | 2 | 2 | 5 |
| tri5 | 5 | 5 | 5 | 0 | 4 | 1 | 1 | 1 | 1 |
| tri5b | 5 | 5 | 5 | 0 | 2 | 1 | 1 | 1 | 1 |
| rn9x6 | 9 | 6 | 3 | 3 | 4 | 0 | 46 | 46 | 7 |
| inj8x5 | 8 | 5 | 5 | 0 | 4 | 1 | 2147483637 | -10 | 6 |

32×32 CRT determinant: 4 primes, 97 bits, Gaussian elimination 7 ms, determinant `96008578392693488164984015920`, match 1 against CPU Bareiss.

Square benchmarks, rank = n − 4, 8 primes. CPU Gaussian elimination compared on every prime for n ≤ 1024 and on one prime at n = 2048. GPU product compared entrywise with the 4-thread CPU product. Times are integer milliseconds from QueryPerformanceCounter.

| n | rank | nullity | ge_ms | gemm_gpu_ms | gemm_cpu_ms | minor det | minor mod 2147483647 | max abs |
|---|---|---|---|---|---|---|---|---|
| 64 | 60 | 4 | 14 | 1 | 1 | 3676 | 3676 | 38 |
| 128 | 124 | 4 | 29 | 1 | 0 | -157902 | 2147325745 | 66 |
| 256 | 252 | 4 | 58 | 1 | 1 | 5079016 | 5079016 | 69 |
| 512 | 508 | 4 | 122 | 2 | 6 | -14011856 | 2133471791 | 124 |
| 1024 | 1020 | 4 | 320 | 8 | 54 | -181929096 | 1965554551 | 142 |
| 2048 | 2044 | 4 | 1358 | 23 | 334 | -442194401 | 1705289246 | 288 |
| 4096 | 4092 | 4 | 7376 | 159 | 11007 | -166066905 | 1981416742 | 482 |
| 8192 | 8188 | 4 | 50819 | 446 | 108305 | 1470428278 | 1470428278 | 376 |

## GPU samples

nvidia-smi query `utilization.gpu,utilization.memory,memory.used`, once a second, from a thread inside the one interpreter process. 265 lines in `out2\gpu-util.txt`. Summary integers: ug_min 0, ug_max 98, ug_sum 5556, um_min 0, um_max 79, um_sum 4222, mem_max_mib 23200. The query is for the whole device. Samples 139 through 184 of that file are gpu utilization 96, 97, or 98 and memory used 23003 to 23200 MiB. The other lines are mostly gpu utilization 0 to 12, with memory used near 18400 to 19000 MiB.

## L2D

`C:\ClaudeOutput\pompetzki\lanes\L2D\` exists. The run recorded `l2d_dir_entries 52`. The summary writes `l2d_matrix_files 0` as a fixed integer. The top-level directory is Racket sources for rank, kernel, Smith, Farkas, Pratt, and LRAT. Nested `certs\in\` holds rank sexps of shapes 2×2, 2×3, 3×3, 3×4, and 4×4, and Smith sexps of shapes 2×2, 2×3, and 3×3. The 2×2 Smith matrix in `smith-2x2.sexp` is [[2, 4], [6, 8]], the first matrix in `snf_check_known`. The GPU rank certificates and the larger Smith certificates are the instances built in this lane: a nonzero minor plus an integer kernel with A·K = 0, and U·A·V = D with det U and det V equal to ±1.
