#lang racket/base
;; assemble-v2.rkt -- lane L7: fills the placeholders of results-head-v1.md and status-draft-v1.txt and writes
;; L7\RESULTS.md and L7\STATUS.txt (new files; an existing file stops the program). The time is read from `date`.
(require racket/string racket/file racket/port racket/system racket/list)
(define S "C:/Users/cpomp/AppData/Local/Temp/claude/C--Users-cpomp-Math/0c7e86d9-5a68-4a4d-b4f4-7d38ea17497c/scratchpad")
(define L7 "C:/ClaudeOutput/pompetzki/lanes/L7")
(define now (string-trim (with-output-to-string (lambda () (system "\"C:/Program Files/Git/usr/bin/date.exe\"")))))
(define hhmm (cadr (regexp-match #px"(\\d\\d:\\d\\d):\\d\\d" now)))
(define (win name label)
  (format "- ~a: ~a to ~a" label
          (cadr (regexp-match #px"(\\d\\d:\\d\\d:\\d\\d)" (file->string (format "~a/judge-~a-1.start.txt" L7 name))))
          (cadr (regexp-match #px"(\\d\\d:\\d\\d:\\d\\d)" (file->string (format "~a/judge-~a-1.end.txt" L7 name))))))
(define windows
  (string-join (list (win "omega" "ω laws (judge-omega-1.txt)") (win "eq" "equality (judge-eq-1.txt)")
                     (win "quant" "quantifiers (judge-quant-1.txt)") (win "taut" "tautologies and control (judge-taut-1.txt)")
                     (win "pmpchain" "pmp chain file (judge-pmpchain-1.txt)"))
               "\n"))
(define tables (file->string (string-append L7 "/judge-tables.md")))
(define sources (string-append (file->string (string-append S "/sources-list-v1.md")) "\n" (file->string (string-append S "/outputs-list-v1.md"))
                               "\n- `out\\*.index.txt`, `out\\*.manifest.txt`: every theorem with key and statement; sizes, hashes, the copy of the checker, the mutants\n"
                               "- `judge-*.txt` (rows), `judge-*.start.txt` / `.end.txt` (`date`), `judge-tables.md` (tables-v2.rkt from the rows)\n"
                               "- `src\\superseded\\`: earlier versions, unchanged\n"))
(define head (file->string (string-append S "/results-head-v1.md")))
(define results
  (for/fold ([t head]) ([p (list (cons "WRITTEN-TIME" hhmm) (cons "JUDGE-WINDOWS" windows) (cons "TABLES" tables) (cons "SOURCES" sources))])
    (string-replace t (car p) (cdr p) #:all? #f)))
(define mutcount (cadr (regexp-match #px"mutants (\\d+) \\((\\d+) REJECT by both\\)" tables)))
(define status (string-replace (string-replace (file->string (string-append S "/status-draft-v1.txt")) "STATUS-TIME" hhmm) "MUTCOUNT" mutcount))
(call-with-output-file (string-append L7 "/RESULTS.md") #:exists 'error (lambda (o) (write-string results o)))
(call-with-output-file (string-append L7 "/STATUS.txt") #:exists 'error (lambda (o) (write-string status o)))
(printf "written at ~a; mutants ~a\n" now mutcount)
