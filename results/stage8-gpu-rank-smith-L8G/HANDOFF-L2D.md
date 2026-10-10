# L8G handoff to L2D, Fri 10/09/2026 08:44 PM

Clock from `date /t` and `time /t`. L2D files were read and not written. `STATUS.txt`, `RESULTS.md`, `out\`, and `out2\` are the earlier receipts and are unchanged.

At 08:13 PM the same clock, `nvidia-smi --query-gpu=utilization.gpu,utilization.memory,memory.used,memory.total --format=csv,noheader,nounits` returned `100, 2, 14467, 32607`. The compute-apps list included `C:\ClaudeOutput\utilization-20261009-185137\recovery-2001\area51-gpu\h716mitm2.exe`. No L8G process was started on that device after the query. The 8192 ladder was not run again.

## What the DLL already proved

`example.pmp` sha256 `92a8132dfc7fac0392c18ab80fe00c915cf6426e245c66773ded86bc6b02772d` called `l8g.dll` sha256 `a239e625c29a6d2ec4b586eabcf49216dcd637e0441b041e7c2e537c31342883` through `pompetzki.exe` sha256 `ccf835920e566b8a45468654798fb9577a261cfec171a707e0438696515a3bec`. The process log `example-process-2.txt` records 8 of 8 claims and `end: every obligation discharged`. `out2\summary.txt` records `workload 0`, selftest 0, and `crt_det n 32 primes 4 bits 97 ge_ms 7 det 96008578392693488164984015920 match 1`. Those eight claims are matrix arithmetic inside pmp. They are not JDG1 derivations.

## DLL surface

```
int64_t l8g_api_version(void);             /* returns 1 */
int64_t l8g_workload(const char *out_dir); /* returns 0 when every CPU check in the ladder passed */
```

pmp calls them as literal tokens:

```
extern ver C:/ClaudeOutput/pompetzki/lanes/L8G/l8g.dll l8g_api_version
extern run C:/ClaudeOutput/pompetzki/lanes/L8G/l8g.dll l8g_workload
text DIR "C:/ClaudeOutput/pompetzki/lanes/L8G/out2"
set rc call run DIR
check zero rc
```

`l8g_workload` writes integer text matrices. It does not write a sexp and it does not write JDG1.

## Bridge that was run

`C:\ClaudeOutput\pompetzki\lanes\L8G\release\example.rkt` sha256 `97d8ae37c50bcf4ec2fc8fddd080d382cdda9eb8987a8bacf6352fe576963a01`.

Commands, already executed once in this tree:

```
"C:\Program Files\Racket\racket.exe" C:\ClaudeOutput\pompetzki\lanes\L8G\release\example.rkt emit
"C:\Program Files\Racket\racket.exe" C:\ClaudeOutput\pompetzki\lanes\L8G\release\example.rkt judge
"C:\Program Files\Racket\racket.exe" C:\ClaudeOutput\pompetzki\lanes\L8G\release\example.rkt hashes
```

`emit` reads the out2 dumps, checks them again in exact integers, and calls the L2D consumer

```
"C:\Program Files\Racket\racket.exe" C:\ClaudeOutput\pompetzki\lanes\L2D\certs-v3.rkt emit CERT.sexp OUT.jdg
```

Consumer sha256 `a001058611f52c2c8a85f11273a7a48f67a1041dc969d60ae8d8d478ed71aee7`. Its require closure, each hashed in `release\HASHES.txt`, is `cert-v1.rkt`, `core-v1.rkt`, `nd-v3.rkt`, `kernel-v6.rkt`, `kernel2-v2.rkt`, `kernel3-v4.rkt`, `bin-v6.rkt`. Registry check reads `C:\ClaudeOutput\pompetzki\forcing-src\general\RpInit.v` sha256 `9421b47eeeed5fa9f16dd599c33e7181991dee700638d5043d8fa55114add97f`. Judges: `judge\judge-v3.pmp` sha256 `bf147194d415d0ab6991b5912c718c772f4bcb285ea027326fc5a108a81e6ce7`, `judge\racket\judge.rkt` sha256 `d6cf694c294a829172976ebd6741d15e39d91f5cb2feb09951421e5212c079ca`. `HASHES.txt` has 78 lines.

| certificate | sexp sha256 | jdg sha256 | entries | theorems | steps | det |
|---|---|---|---|---|---|---|
| rn6x8 rank 4, nullity 4, minor rows and columns 0 1 2 3, kernel rows 4 5 6 7 | `cec043ad4ad60d744f10ea17de80a49b59c9fbece0ba1a8d2245308a18a52ed6` | `8636d5717e16e37279b9821980b048dcb081636468c601623be5d247a9725cee` | 44 | 228 | 10270 | minor 2, kernel minor 1 |
| tri5 rank 5, empty kernel | `91634d321221f326c94388c5c928f161bc137b9f6985f342635611c9163e5b91` | `ec5c79410ba31b57d6bdf20811a43974c3339296622aba49a08c30766d4cd9c5` | 12 | 68 | 1762 | 1 |
| smith3, D = diag(1, 1, 8), det U = 1, det V = 1 | `b5a64a61bafc76df8c2176483769ad8238edc4efac73add315c2dba3a56aa979` | `d779a8756612bb52451200ff45619b27965e8d5b80fd0c94abdea34da2fec4a4` | 29 | 156 | 6125 |  |

Each file's registry line is `OK: 677 entries = AX0 (7) ++ DEF0 (670) of RpInit.v, entry for entry, none with hypotheses`. The emitter's own checker returned ACCEPT on the three files and REJECT on each of the ten mutants.

## Both judges

From `C:\ClaudeOutput\pompetzki\judge\`, on all 33 JDG1 files. `release\judge-run.txt` has 33 lines: 3 with pmp ACCEPT and racket ACCEPT, 30 with pmp REJECT and racket REJECT, 0 mismatched.

| file | pmp | racket |
|---|---|---|
| rn6x8.jdg | ACCEPT exit 0, 376011 ms, registry 677, theorems 228, steps 10270, final registry 905 | ACCEPT exit 0, 2465 ms, same counts |
| tri5.jdg | ACCEPT exit 0, 22886 ms, 677, 68, 1762, 745 | ACCEPT exit 0, 2112 ms, same counts |
| smith3.jdg | ACCEPT exit 0, 193753 ms, 677, 156, 6125, 833 | ACCEPT exit 0, 4301 ms, same counts |

Mutant names, ten per file: `cert-use-swap`, `drop-step`, `exel-var`, `exi-witness`, `leib-swap`, `neg-final`, `registry-suc`, `taut-goal`, `twin-final`, `use-shift`. Each is REJECT from both judges. The row with the theorem index and the step index is in `judge-run.txt`.

## Corruption refused before a derivation existed

`release\corrupt\smith3-bad.sexp` is smith3 with the leading entry of A changed from 2 to 3. `certs-v3.rkt` exited 1 and printed `smith: U A V /= D`. No jdg file was written.

`release\corrupt\rn6x8-bad.sexp` adds 1 to every entry of the first kernel row. `certs-v3.rkt` exited 1 and printed `rank: A K /= 0`. No jdg file was written.

## Sexp shapes this bridge fills

Rank, as `certs-v3.rkt` reads it:

```
(rank (A rows) (r n) (I row-indexes) (J column-indexes) (K kernel-columns-as-rows) (I2 kernel-minor-rows))
```

Smith:

```
(smith (A rows) (U rows) (V rows) (D rows))
```

Rows are lists of exact integers. Kernel columns of the DLL's `pmp_K.txt` (n rows, nullity columns) are transposed into K. For rn6x8, I = J = (0 1 2 3) and I2 = (4 5 6 7). For tri5, K and I2 are empty.

## Interface still open

`l8g.dll` has no producer for these L2D forms, and this handoff does not emit them:

- Pratt, inside `certs-v3.rkt`: `(pratt p a ((q e) ...) sub-certificates...)`.
- Farkas, inside `farkas-v3.rkt`: `(farkas (A rows) (b vector) (y vector))`, command `racket farkas-v3.rkt emit CERT.sexp OUT.jdg`.
- LRAT, inside `lrat-v4.rkt`: `racket lrat-v4.rkt emit CNF LRAT OUT.jdg`.

`l8g_workload` checks a 32×32 determinant, 97 bits, value `96008578392693488164984015920`, against CPU Bareiss (`match 1` in `out2\summary.txt`). `certs-v3.rkt` has no residue-determinant argument, and no JDG1 file was emitted for that integer. The integer matrix product C = A·A is checked inside the DLL, GPU against CPU, and is not a JDG1 family.

The benchmark matrices from 64×64 through 8192×8192 are not among the dumped text files. Writing them again means calling `l8g_workload`, which runs that ladder, including the finished 8192 case, on the GPU.
