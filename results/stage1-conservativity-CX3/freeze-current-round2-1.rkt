#lang racket/base
(require racket/file racket/string racket/port racket/system json openssl/sha1)
(define lane "C:/ClaudeOutput/pompetzki/lanes/CX3")
(define selected (string-append lane "/CURRENT-ROUND2-INTEGRATION-2.json"))
(define later (string-append lane "/CURRENT-ROUND2-INTEGRATION-3.json"))
(define a (call-with-input-file selected read-json))
(define b (call-with-input-file later read-json))
(define clock (string-trim (with-output-to-string
  (lambda () (unless (system* "C:/Program Files/Git/usr/bin/date.exe" "+%Y-%m-%dT%H:%M:%S%:z")
               (error 'date "date.exe failed"))))))
(define (sha p) (call-with-input-file p (lambda (i) (bytes->hex-string (sha256-bytes i))) #:mode 'binary))
(define same-rows (equal? (hash-ref a 'rows) (hash-ref b 'rows)))
(define same-files (equal? (hash-ref a 'files) (hash-ref b 'files)))
(unless (and same-rows same-files) (error 'freeze "postcut snapshot differs in target claims or source/hash records"))
(define artifact
  (hasheq 'clock_date_exe clock 'cutoff "2026-10-09T21:10:00-04:00"
          'selected_pre_cutoff_table selected 'selected_sha256 (sha selected)
          'selected_capture_clock (hash-ref a 'clock_date_exe)
          'selected_verified_clock "2026-10-09T21:09:12-04:00"
          'selected_status (string-append lane "/STATUS-CURRENT-ROUND2-2.txt")
          'post_cutoff_snapshot later 'post_cutoff_sha256 (sha later)
          'post_cutoff_capture_clock (hash-ref b 'clock_date_exe)
          'same_target_claims same-rows 'same_source_and_artifact_records same-files
          'source_and_artifact_records (length (hash-ref a 'files))
          'targets (hash-ref a 'targets) 'kernel_completed (hash-ref a 'kernel_completed)
          'kernel_theorems (hash-ref a 'kernel_theorems) 'kernel_steps (hash-ref a 'kernel_steps)
          'compiled (hash-ref a 'compiled) 'compiled_theorems (hash-ref a 'compiled_theorems)
          'compiled_steps (hash-ref a 'compiled_steps)
          'coo_consumed_packet "C:/ClaudeOutput/operations-coo-20261009-190715/release-readiness-v2/LATEST-COO-READINESS-SUPPLEMENT-v3.md"
          'coo_handoff_count 1 'duplicate_proof_jobs_started 0
          'package_verification "CURRENT-ROUND2-PACKAGE-VERIFY-1.json verifies34/160 copies against the earlier candidate and its outer manifest; new package/manifest completion is still owned by COO."))
(define out (string-append lane "/CURRENT-ROUND2-FREEZE-1.json"))
(call-with-output-file out #:exists 'error (lambda (o) (write-json artifact o) (newline o)))
(define md (string-append lane "/CURRENT-ROUND2-FREEZE-1.md"))
(call-with-output-file md #:exists 'error
  (lambda (o)
    (fprintf o "# CX3 current-batch correction freeze\n\nReceipt clock from date.exe: ~a. The selected pre21:10 input is CURRENT-ROUND2-INTEGRATION-2.md/json/copy-plan.tsv/sha256, captured21:00:51 and verified21:09:12. Its191 hashes verified.\n\nThe table has46 targets:3 completed recursive kernel checks,480 conclusions/26,286 steps;13 compiled certificates,7,442 conclusions/215,169 steps. Ten compiled certificates retain kernel-pending status;26 further wave2 and7 L6/L7 targets retain target-pending status. The seven baseline batches remain separately completed:1,656 conclusions/53,069 steps.\n\nCURRENT-ROUND2-INTEGRATION-3 was captured21:10:17 and verified21:10:19. Exact comparison confirms that its46 target claims and187 source/artifact hash records are identical to the selected pre-cutoff input. Both snapshots remain beside this selection receipt.\n\nCX3 sent the CEO check-in and followed his current-batch integration order. ONE COO handoff was sent before20:55. The COO consumed that exact packet in LATEST-COO-READINESS-SUPPLEMENT-v3.md, preserving pending/conditional claims and exact faithful expansion APIs. Original candidate verification proves34/160 planned copies match source and outer manifest;126 additions are designated. A new final-package/manifest path is still required from its active owner for final current-copy verification.\n\nAll artifacts were written in C:\\ClaudeOutput\\pompetzki\\lanes\\CX3\\. No compiler, kernel checker or judge job was started by CX3 during this integration. Qualified registry, resource and unrelated global context obligations remain explicit in the table.\n" clock)))
(define receipt (string-append lane "/CURRENT-ROUND2-FREEZE-1.sha256"))
(call-with-output-file receipt #:exists 'error
  (lambda (o)
    (fprintf o "# date.exe ~a\n" clock)
    (for ([p (in-list (list out md selected later))]) (fprintf o "~a  ~a\n" (sha p) p))))
(printf "Selected pre-cutoff table2; postcut table3 has identical46 target claims and187 artifact records. ~a\n" out)
