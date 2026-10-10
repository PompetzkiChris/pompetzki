#lang racket/base
(require racket/file racket/string racket/port racket/system openssl/sha1)
(define lane "C:/ClaudeOutput/pompetzki/lanes/CX3")
(define clock (string-trim (with-output-to-string (lambda () (unless (system* "C:/Program Files/Git/usr/bin/date.exe" "+%Y-%m-%dT%H:%M:%S%:z") (error 'date "date.exe failed"))))))
(define snapshot
 (with-output-to-string (lambda ()
  (unless (system* "C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe" "-NoProfile" "-Command"
   "Get-CimInstance Win32_Process | Where-Object { $_.ProcessId -in 140196,148076,104832,116532 } | Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Depth 4 -Compress")
   (error 'process "process query failed")))))
(define p1 "C:/ClaudeOutput/pompetzki/lanes/CX3B/Round2KernelP1.check1.receipt.txt")
(define p2 "C:/ClaudeOutput/pompetzki/lanes/CX3B/Round2KernelP2.check1.receipt.txt")
(define (receipt p) (if (file-exists? p) (file->string p) "No completed receipt at the named path at this checkpoint."))
(define out (string-append lane "/RESTART-HANDOFF-2152-ADDENDUM-1.md"))
(call-with-output-file out #:exists 'error
 (lambda (o)
  (fprintf o "# CX3 restart ownership addendum\n\nClock from date.exe: ~a. CX3 remains restart-ready; all owned bounded jobs ended, edits are saved, and no work will relaunch until CEO post-restart instruction. This addendum stays beside RESTART-HANDOFF-2152.md.\n\nCEO's subsequent checkpoint named the CX3B priority2 chain below. Its checker command targets CX3B.Round2CertificateW04-W11 andW21-W38. This chain and its heartbeat were not launched by CX3. CX3 sent the exact owner/creation/command facts and ready status to CEO, then forwarded the CEO's checkpoint to the CX3B order2 chat01a122f2-13b1-7602-8eaa-711ff95e9958. CX3 stopped no foreign process and did not mark any unfinished check PASS or INTERRUPTED. The owning runner must record its actual stop and no-relaunch state.\n\n```json\n~a\n```\n\n" clock (string-trim snapshot))
  (fprintf o "The original baseline and completed priority1 group are retained. Current priority1 completed-receipt path: ~a. Its current contents are copied below as observed evidence, including exit and end clock when present. Postcut completion remains separate from the pre21:10 table freeze.\n\n```text\n~a\n```\n\n" p1 (receipt p1))
  (fprintf o "Current priority2 completed-receipt path: ~a. A missing completed receipt does not establish failure; a stopped unfinished group requires the owner to record INTERRUPTED_FOR_RESTART and rerun only that unfinished group after authorization.\n\n```text\n~a\n```\n\n" p2 (receipt p2))
  (displayln "Resume order: CEO confirms post-restart execution; CX3 verifies the160 prefixed package selections with the exact command in RESTART-HANDOFF-2152.md; CX3B resumes only unfinished P2/P3 work using its preserved full checker/runner commands and source/object hashes, without rerunning completed baseline/P1 groups. The original whole interpreter/ELF release obligations retain their owners.\n" o)))
(define (sha p) (call-with-input-file p (lambda (i) (bytes->hex-string (sha256-bytes i))) #:mode 'binary))
(call-with-output-file (string-append lane "/RESTART-HANDOFF-2152-ADDENDUM-1.sha256") #:exists 'error
 (lambda (o) (fprintf o "# date.exe ~a\n~a  ~a\n" clock (sha out) out)))
(displayln out)
