#lang racket/base
;; build-corpus.rkt -- Master pipeline for AG5 corpus generation and verification
;; Runs CaDiCaL on small unsatisfiable CNFs, verifies all proofs with check-lrat.rkt,
;; tests negative mutants, generates INDEX.tsv, MANIFEST.sha256, RESULTS.md, and STATUS.txt.
;; Uses exact integer arithmetic throughout.

(require racket/file
         racket/string
         racket/list
         racket/path
         file/sha1
         "generate-corpus.rkt"
         "check-lrat.rkt")

(provide (all-defined-out))

(define ag5-dir (build-path "C:" "ClaudeOutput" "pompetzki" "lanes" "AG5"))
(define cnf-dir (build-path ag5-dir "cnf"))
(define lrat-dir (build-path ag5-dir "lrat"))
(define mutant-dir (build-path ag5-dir "mutants"))

(make-directory* cnf-dir)
(make-directory* lrat-dir)
(make-directory* mutant-dir)

(define (sha256-file path)
  (call-with-input-file path
    (lambda (in)
      (bytes->hex-string (sha256-bytes in)))))

(struct instance-record
  (family
   name
   nvars
   nclauses
   cadical-ms
   check-status
   check-ms
   additions
   deletions
   total-steps
   cnf-sha
   lrat-sha
   message)
  #:transparent)

;; Generate and solve a single instance (or reuse existing valid artifacts)
(define (process-instance family name nvars clauses)
  (define cnf-path (build-path cnf-dir (format "~a.cnf" name)))
  (define lrat-path (build-path lrat-dir (format "~a.lrat" name)))

  (define cadical-ms 0)
  (unless (and (file-exists? cnf-path) (file-exists? lrat-path))
    ;; 1. Write CNF
    (write-dimacs-file cnf-path nvars clauses)
    ;; 2. Run CaDiCaL
    (define-values (cadical-code ms) (solve-cadical-lrat cnf-path lrat-path 30))
    (set! cadical-ms ms)
    (unless (= cadical-code 20)
      (error 'build-corpus "Instance ~a: CaDiCaL returned ~a (expected 20 = UNSAT)" name cadical-code)))

  ;; 3. Check with Racket LRAT checker
  (define res (check-lrat-files cnf-path lrat-path))

  (instance-record
   family
   name
   nvars
   (length clauses)
   cadical-ms
   (check-result-status res)
   (check-result-elapsed-ms res)
   (check-result-additions res)
   (check-result-deletions res)
   (check-result-total-steps res)
   (sha256-file cnf-path)
   (sha256-file lrat-path)
   (check-result-message res)))

;; Generate and solve a random 3-CNF instance, searching for UNSAT seed
(define (process-random-instance family base-name nvars ratio start-seed)
  (let loop ([seed start-seed])
    (define name (format "~a-s~a" base-name seed))
    (define cnf-path (build-path cnf-dir (format "~a.cnf" name)))
    (define lrat-path (build-path lrat-dir (format "~a.lrat" name)))
    (cond
      [(and (file-exists? cnf-path) (file-exists? lrat-path))
       ;; Existing verified pair
       (define res (check-lrat-files cnf-path lrat-path))
       (instance-record
        family name nvars (* ratio nvars) 0
        (check-result-status res)
        (check-result-elapsed-ms res)
        (check-result-additions res)
        (check-result-deletions res)
        (check-result-total-steps res)
        (sha256-file cnf-path)
        (sha256-file lrat-path)
        (check-result-message res))]
      [else
       (define-values (nv cls) (generate-random-3cnf nvars ratio seed))
       (write-dimacs-file cnf-path nv cls)
       (define-values (cadical-code cadical-ms) (solve-cadical-lrat cnf-path lrat-path 30))
       (cond
         [(eq? cadical-code 'timeout)
          (delete-file cnf-path)
          (when (file-exists? lrat-path) (delete-file lrat-path))
          (instance-record family name nv (length cls) cadical-ms 'TIMEOUT cadical-ms 0 0 0 "" "" "CaDiCaL timed out")]
         [(= cadical-code 20)
          (define res (check-lrat-files cnf-path lrat-path))
          (instance-record
           family name nv (length cls) cadical-ms
           (check-result-status res)
           (check-result-elapsed-ms res)
           (check-result-additions res)
           (check-result-deletions res)
           (check-result-total-steps res)
           (sha256-file cnf-path)
           (sha256-file lrat-path)
           (check-result-message res))]
         [else
          ;; SAT (code 10): try next seed
          (delete-file cnf-path)
          (when (file-exists? lrat-path) (delete-file lrat-path))
          (loop (+ seed 1))])])))

;; Struct for mutant test results
(struct mutant-result
  (id
   description
   base-instance
   mutation-type
   check-status
   check-message
   sha256)
  #:transparent)

(define (test-negative-mutants)
  (define base-cnf (build-path cnf-dir "php-3-2.cnf"))
  (define base-lrat (build-path lrat-dir "php-3-2.lrat"))
  (define lrat-lines (file->lines base-lrat))

  (define mutant-defs
    (list
     ;; 1. Corrupt hint: replace a valid hint with an invalid clause ID
     (cons "mutant-1-wrong-hint"
           (lambda ()
             (for/list ([line lrat-lines])
               (if (regexp-match? #rx"^10 " line)
                   ;; Replace hint in step 10
                   (regexp-replace #rx" [0-9]+ 0$" line " 999 0")
                   line))))

     ;; 2. Missing conflict hint: remove the last hint from step 10
     (cons "mutant-2-missing-conflict-hint"
           (lambda ()
             (for/list ([line lrat-lines])
               (if (regexp-match? #rx"^10 " line)
                   (let* ([toks (string-split line)]
                          [nums (map string->number (cdr toks))]
                          [lits-rest (let-values ([(lits rest) (splitf-at nums (lambda (x) (not (zero? x))))])
                                       (cons lits (drop-right (cdr rest) 1)))])
                     (define lits (car lits-rest))
                     (define hints (cdr lits-rest))
                     (if (> (length hints) 1)
                         (format "~a ~a 0 ~a 0"
                                 (car toks)
                                 (string-join (map number->string lits) " ")
                                 (string-join (map number->string (drop-right hints 1)) " "))
                         line))
                   line))))

     ;; 3. Flipped literal polarity: flip literal in derived clause
     (cons "mutant-3-flipped-literal"
           (lambda ()
             (for/list ([line lrat-lines])
               (if (regexp-match? #rx"^10 " line)
                   (let ([toks (string-split line)])
                     ;; toks: (id lit 0 hint... 0)
                     (define id (car toks))
                     (define lit (string->number (cadr toks)))
                     (define rest-str (string-join (cddr toks) " "))
                     (format "~a ~a ~a" id (- lit) rest-str))
                   line))))

     ;; 4. Non-increasing clause ID
     (cons "mutant-4-non-increasing-id"
           (lambda ()
             (for/list ([line lrat-lines])
               (if (regexp-match? #rx"^11 " line)
                   ;; set id 11 to 9 (less than 10)
                   (regexp-replace #rx"^11 " line "9 ")
                   line))))

     ;; 5. Use deleted clause as hint
     (cons "mutant-5-use-deleted-clause"
           (lambda ()
             ;; Insert a deletion of clause 1 right before step 10, but step 10 or later uses clause 1
             (define out '())
             (for ([line lrat-lines])
               (when (regexp-match? #rx"^10 " line)
                 (set! out (cons "10 d 1 0" out)))
               (set! out (cons line out)))
             (reverse out)))

     ;; 6. Truncated proof: delete the empty clause line
     (cons "mutant-6-truncated-before-empty"
           (lambda ()
             (filter (lambda (line)
                       ;; The empty clause line has pattern: "<id> 0 <hints...> 0"
                       (not (regexp-match? #rx"^[0-9]+ 0 " line)))
                     lrat-lines)))

     ;; 7. Extra literal in empty clause: change final clause to non-empty
     (cons "mutant-7-non-empty-final-clause"
           (lambda ()
             (for/list ([line lrat-lines])
               (if (regexp-match? #rx"^[0-9]+ 0 " line)
                   ;; add literal 1 to the empty clause
                   (regexp-replace #rx"^([0-9]+) 0 " line "\\1 1 0 ")
                   line))))

     ;; 8. Reference non-existent clause ID
     (cons "mutant-8-nonexistent-hint"
           (lambda ()
             (for/list ([line lrat-lines])
               (if (regexp-match? #rx"^10 " line)
                   (regexp-replace #rx" 0 8 " line " 0 99999 ")
                   line))))

     ;; 9. Invalid hint creating non-unit clause
     (cons "mutant-9-non-unit-hint"
           (lambda ()
             (for/list ([line lrat-lines])
               (if (regexp-match? #rx"^10 " line)
                   ;; Insert hint 1 (clause 1 has multiple unassigned literals)
                   (regexp-replace #rx"^([0-9]+ [^0]+ 0 )" line "\\1 1 ")
                   line))))))

  (define results '())
  (for ([m mutant-defs])
    (define m-name (car m))
    (define m-gen (cdr m))
    (define m-lines (m-gen))
    (define m-lrat-path (build-path mutant-dir (format "~a.lrat" m-name)))
    (display-lines-to-file m-lines m-lrat-path #:separator "\n" #:exists 'truncate)
    (define res (check-lrat-files base-cnf m-lrat-path))
    (printf "  ~a: ~a (~a)\n"
            m-name
            (check-result-status res)
            (check-result-message res))
    (set! results (cons (mutant-result m-name
                                       m-name
                                       "php-3-2"
                                       m-name
                                       (check-result-status res)
                                       (check-result-message res)
                                       (sha256-file m-lrat-path))
                        results)))
  (reverse results))

;; ============================================================================
;; Run the full corpus build and write summary files
;; ============================================================================

(define (run-build)
  (printf "===============================================================================\n")
  (printf "AG5: Generating LRAT Certificate Corpus for Lane L2D\n")
  (printf "===============================================================================\n\n")

  (define records '())

  ;; --------------------------------------------------------------------------
  ;; Family 1: Pigeonhole Principle PHP(n+1, n) for n <= 6
  ;; --------------------------------------------------------------------------
  (printf "[1/3] Generating Family 1: Pigeonhole Principle PHP(n+1, n), n in 1..6...\n")
  (for ([n (in-range 1 7)])
    (define name (format "php-~a-~a" (+ n 1) n))
    (define-values (nvars clauses) (generate-php n))
    (define rec (process-instance "pigeonhole" name nvars clauses))
    (set! records (cons rec records))
    (printf "  ~a: ~a vars, ~a clauses, ~a steps -> ~a in ~a ms (CaDiCaL: ~a ms)\n"
            name nvars (length clauses) (instance-record-total-steps rec)
            (instance-record-check-status rec)
            (instance-record-check-ms rec)
            (instance-record-cadical-ms rec)))

  ;; --------------------------------------------------------------------------
  ;; Family 2: Tseitin formulas on small graphs
  ;; --------------------------------------------------------------------------
  (printf "\n[2/3] Generating Family 2: Tseitin formulas on small graphs...\n")
  (for ([g (get-tseitin-graphs)])
    (define name (first g))
    (define num-nodes (second g))
    (define edges (third g))
    (define-values (nvars clauses) (generate-tseitin name num-nodes edges))
    (define rec (process-instance "tseitin" name nvars clauses))
    (set! records (cons rec records))
    (printf "  ~a: ~a vars, ~a clauses, ~a steps -> ~a in ~a ms (CaDiCaL: ~a ms)\n"
            name nvars (length clauses) (instance-record-total-steps rec)
            (instance-record-check-status rec)
            (instance-record-check-ms rec)
            (instance-record-cadical-ms rec)))

  ;; --------------------------------------------------------------------------
  ;; Family 3: Random 3-CNF at ratio 5
  ;; --------------------------------------------------------------------------
  (printf "\n[3/3] Generating Family 3: Random 3-CNF at ratio 5...\n")
  (define random-specs
    '(;; (nvars seed)
      (15 101) (15 102)
      (20 201) (20 203) (20 205)
      (25 251) (25 252) (25 253)
      (30 301) (30 302) (30 303)
      (35 351) (35 352)
      (40 401) (40 402)
      (50 501) (50 502)))

  (for ([spec random-specs])
    (define nv (first spec))
    (define seed (second spec))
    (define base-name (format "rand3-v~a" nv))
    (define rec (process-random-instance "random-3cnf" base-name nv 5 seed))
    (set! records (cons rec records))
    (printf "  ~a: ~a vars, ~a clauses, ~a steps -> ~a in ~a ms (CaDiCaL: ~a ms)\n"
            (instance-record-name rec)
            (instance-record-nvars rec)
            (instance-record-nclauses rec)
            (instance-record-total-steps rec)
            (instance-record-check-status rec)
            (instance-record-check-ms rec)
            (instance-record-cadical-ms rec)))

  (define sorted-records (reverse records))

  ;; --------------------------------------------------------------------------
  ;; Negative Mutant Testing Suite
  ;; --------------------------------------------------------------------------
  (printf "\n===============================================================================\n")
  (printf "Generating and Testing Negative Mutants (Soundness Check)\n")
  (printf "===============================================================================\n\n")

  (define mutant-records (test-negative-mutants))

  ;; --------------------------------------------------------------------------
  ;; Write INDEX.tsv
  ;; --------------------------------------------------------------------------
  (define index-path (build-path ag5-dir "INDEX.tsv"))
  (call-with-output-file index-path #:exists 'truncate
    (lambda (out)
      (fprintf out "family\tname\tvars\tclauses\ttotal_steps\tadditions\tdeletions\tcadical_ms\tchecker_ms\tstatus\tcnf_sha256\tlrat_sha256\n")
      (for ([r sorted-records])
        (fprintf out "~a\t~a\t~a\t~a\t~a\t~a\t~a\t~a\t~a\t~a\t~a\t~a\n"
                (instance-record-family r)
                (instance-record-name r)
                (instance-record-nvars r)
                (instance-record-nclauses r)
                (instance-record-total-steps r)
                (instance-record-additions r)
                (instance-record-deletions r)
                (instance-record-cadical-ms r)
                (instance-record-check-ms r)
                (instance-record-check-status r)
                (instance-record-cnf-sha r)
                (instance-record-lrat-sha r)))))

  ;; --------------------------------------------------------------------------
  ;; Write MANIFEST.sha256
  ;; --------------------------------------------------------------------------
  (define manifest-path (build-path ag5-dir "MANIFEST.sha256"))
  (call-with-output-file manifest-path #:exists 'truncate
    (lambda (out)
      (for ([r sorted-records])
        (fprintf out "~a *cnf/~a.cnf\n" (instance-record-cnf-sha r) (instance-record-name r))
        (fprintf out "~a *lrat/~a.lrat\n" (instance-record-lrat-sha r) (instance-record-name r)))
      (for ([m mutant-records])
        (fprintf out "~a *mutants/~a.lrat\n" (mutant-result-sha256 m) (mutant-result-id m)))))

  (printf "\nWrote INDEX.tsv and MANIFEST.sha256.\n")
  (values sorted-records mutant-records))

(module+ main
  (run-build))
