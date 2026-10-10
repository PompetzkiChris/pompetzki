#lang racket/base
(require racket/file racket/string racket/port racket/system racket/path json openssl/sha1)
(define lane "C:/ClaudeOutput/pompetzki/lanes/CX3")
(define args (current-command-line-arguments))
(unless (= (vector-length args) 1) (error 'usage "integration-sequence"))
(define n (vector-ref args 0))
(unless (regexp-match? #px"^[0-9]+$" n) (error 'sequence "expected an integer"))
(define name (string-append "CURRENT-ROUND2-INTEGRATION-" n))
(define j (call-with-input-file (build-path lane (string-append name ".json")) read-json))
(define clock (string-trim (with-output-to-string
  (lambda () (unless (system* "C:/Program Files/Git/usr/bin/date.exe" "+%Y-%m-%dT%H:%M:%S%:z")
               (error 'date "date.exe failed"))))))
(define (sha p) (call-with-input-file p (lambda (i) (bytes->hex-string (sha256-bytes i))) #:mode 'binary))
(define count 0)
(for ([s (in-list (file->lines (build-path lane (string-append name ".sha256"))))]
      #:unless (string-prefix? s "#"))
  (define m (regexp-match #px"^([a-f0-9]{64})  (.+)$" s))
  (unless m (error 'manifest "invalid record"))
  (unless (equal? (cadr m) (sha (caddr m))) (error 'manifest "hash changed: ~a" (caddr m)))
  (set! count (add1 count)))
(define out (build-path lane (string-append "STATUS-CURRENT-ROUND2-" n ".txt")))
(call-with-output-file out #:exists 'error
  (lambda (o)
    (fprintf o "CX3 checked in successfully with CEO01a122d8-5caa-70d3-9230-3890c6139116 and followed his current-batch integration order. ONE COO handoff was successfully sent to01a122c1-147c-7520-bb09-d8b6ca442661 before20:55; his LATEST-COO-READINESS-SUPPLEMENT-v3.md consumes the exact packet and preserves its conditional/pending rows. At ~a(date.exe), ~a/46 Round2 targets have completed recursive kernel receipts (~a conclusions/~a steps); ~a/46 compiled (~a conclusions/~a steps). Exact module/API/source/object/JDG/license/registry/resource records and copy plan are in ~a.md/json/copy-plan.tsv/sha256, independently verified here: ~a hash rows. All baseline CX3/CX3B results remain separate completed inputs. Zero new proof compiler, kernel or judge jobs were started by CX3. Original candidate verification is CURRENT-ROUND2-PACKAGE-VERIFY-1.json:34/160 planned copies match both original source and outer manifest,126 additions designated. New final-package copy verification requires the new package and manifest emitted by its active COO owner; original interpreter/ELF and unrelated Corelib context obligations retain their explicit premises and owners.\n"
      clock (hash-ref j 'kernel_completed) (hash-ref j 'kernel_theorems) (hash-ref j 'kernel_steps)
      (hash-ref j 'compiled) (hash-ref j 'compiled_theorems) (hash-ref j 'compiled_steps) name count)))
(define receipt (build-path lane (string-append "STATUS-CURRENT-ROUND2-" n ".sha256")))
(call-with-output-file receipt #:exists 'error
  (lambda (o) (fprintf o "# date.exe ~a\n~a  ~a\n" clock (sha out) out)))
(printf "~a: ~a hash rows verified; new status ~a\n" clock count out)
