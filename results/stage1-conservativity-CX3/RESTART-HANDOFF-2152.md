# CX3 restart checkpoint

Clock from date.exe: 2026-10-09T21:54:00-04:00. Christopher's maintenance request was relayed by CEO01a122d8-5caa-70d3-9230-3890c6139116. CX3 is restart-ready. No CX3 compiler, kernel checker, judge, watcher or scheduled relaunch remains active. All source edits are saved as new files in this lane. No reboot or foreign process stop was performed. CX3 will launch no further work until the post-restart CEO instruction.

Original CX3 results are complete: Conservativity2.v and Stage2Conservativity2.v compiled and passed recursive coqchk; their final source/object hashes and exact public APIs are in RESULTS.md and INTEGRATION-RECOVERY-1.md/json. Seven CX3B baseline certificates separately cover1,656 conclusions/53,069 steps. Their checks were reused.

Current Round2 integration was delivered to the COO before20:55. Selected pre21:10 snapshot is CURRENT-ROUND2-INTEGRATION-2.md/json/copy-plan.tsv/sha256, verified21:09:12 with191 matching hashes. It records3/46 recursively checked targets (480 conclusions/26,286 steps),13 compiled targets (7,442 conclusions/215,169 steps),ten compiled kernel-pending targets and33 target-pending files. CURRENT-ROUND2-FREEZE-1.md/json proves the postcut table3 has identical46 target claims and187 artifact records. No pending check was marked PASS.

The last CX3-owned bounded process was the read-only package verifier in exec session83304. It completed with exit0; there is no active owned PID to interrupt or rerun before maintenance. Its receipt CURRENT-ROUND2-PACKAGE-VERIFY-2.json is dated21:15:10 and records34/160 direct-layout source copies matching the new assembly and its outer manifest. The COO assembler actually places the160 current selections under current-handoffs/CX3-round2-v1/. That prefixed layout remains to be verified after restart; the34 direct-layout matches do not certify the160 prefixed copies.

New assembly root: C:\ClaudeOutput\pompetzki\lanes\CEO\executive-20261009-183208\package\coo-final-v2-20261009-2058\coo-candidate-20261009-200631. Its assemble-v3.rkt lines77-84 identify the exact prefixed copy plan and integration artifacts. COO owns its complete scan, archive and extraction receipts. ONE COO handoff was sent; his LATEST-COO-READINESS-SUPPLEMENT-v3.md consumes it.

The process snapshot below records foreign CX3B workers if still present, plus any process whose command names this lane's integration helpers. The short-lived writer/PowerShell query belongs to this checkpoint and completes before restart readiness is reported. Foreign CX3B PID91732 and its Racket parents belong to CX3B/CEO; CX3 neither stops them nor authorizes their interruption. Their owner must finish or checkpoint them.

```json
[{"ProcessId":104832,"Name":"Racket.exe","CreationDate":"\/Date(1791591525248)\/","CommandLine":"C:\\Program Files\\Racket\\racket.exe"},{"ProcessId":102296,"Name":"powershell.exe","CreationDate":"\/Date(1791597240321)\/","CommandLine":"C:\\Windows\\System32\\WindowsPowerShell\\v1.0\\powershell.exe -NoProfile -Command \"Get-CimInstance Win32_Process | Where-Object { $_.ProcessId -in 91732,128904,104832 -or $_.CommandLine -match \u0027integrate-current-round2-|verify-current-round2-package-|finish-current-round2-checkin-|freeze-current-round2-\u0027 } | Select-Object ProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Depth 4 -Compress\""}]
```

After the CEO's post-restart instruction, resume the remaining package-copy verification with this exact read-only command. It verifies the160 prefixed copies and their outer-manifest entries against the frozen table; a failure leaves the remaining obligation open.

```powershell
& 'C:\Program Files\Racket\racket.exe' -e @'
(begin
 (require racket/file racket/list racket/string json openssl/sha1)
 (define root "C:/ClaudeOutput/pompetzki/lanes/CEO/executive-20261009-183208/package/coo-final-v2-20261009-2058/coo-candidate-20261009-200631")
 (define frozen (call-with-input-file "C:/ClaudeOutput/pompetzki/lanes/CX3/CURRENT-ROUND2-INTEGRATION-2.json" read-json))
 (define manifest (make-hash))
 (for ([line (file->lines (build-path root "MANIFEST.sha256"))])
   (define m (regexp-match #px"^([a-f0-9]{64})  (.+)$" line))
   (when m (hash-set! manifest (string-replace (caddr m) "\\" "/") (cadr m))))
 (define checked 0)
 (for ([r (hash-ref frozen 'files)] #:unless (eq? (hash-ref r 'package_relative) 'null))
   (define relative (string-append "current-handoffs/CX3-round2-v1/" (hash-ref r 'package_relative)))
   (define expected (hash-ref r 'sha256))
   (define actual (call-with-input-file (build-path root relative) (lambda (i) (bytes->hex-string (sha256-bytes i))) #:mode 'binary))
   (unless (and (equal? actual expected) (equal? expected (hash-ref manifest relative #f)))
     (error 'package "source/manifest mismatch: ~a" relative))
   (set! checked (add1 checked)))
 (unless (= checked 160) (error 'package "unexpected selection count: ~a" checked))
 (printf "Verified160 current prefixed source/receipt copies and their outer-manifest entries.\n"))
'@
```

Next original release obligation: complete this current-version package-copy receipt, then integrate only owner-completed kernel receipts with their exact contexts and hypotheses. The original Stage1 actual-interpreter-to-check_batch and CX4 actual-ELF-to-check_batch proofs remain with their owners. The frozen table does not close those obligations or other Corelib contexts.

