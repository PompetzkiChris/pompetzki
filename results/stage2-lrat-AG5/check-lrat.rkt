#lang racket/base
;; check-lrat.rkt -- Exact LRAT certificate checker in Racket
;; Part of Antigravity AG5 corpus for lane L2D.
;; Checks DIMACS CNF + CaDiCaL LRAT proofs using exact integer arithmetic.

(require racket/file
         racket/string
         racket/list
         racket/match
         racket/cmdline)

(provide check-lrat-files
         check-lrat-ports
         read-dimacs-cnf
         (struct-out check-result))

(struct check-result
  (status        ; 'ACCEPT or 'REJECT
   nvars         ; number of variables
   nclauses      ; number of original clauses
   additions     ; number of addition steps checked
   deletions     ; number of deletion steps processed
   total-steps   ; total lines / steps in LRAT
   elapsed-ms    ; time in exact milliseconds
   message)      ; detailed status / error message
  #:transparent)

;; Read a DIMACS CNF from an input port.
;; Returns (values nvars nclauses (vectorof (vectorof exact-integer?)))
(define (read-dimacs-cnf in)
  (define nvars 0)
  (define nclauses 0)
  (define clauses '())
  (define cur-clause '())
  (for ([line (in-lines in)])
    (define trimmed (string-trim line))
    (cond
      [(or (string=? trimmed "") (string-prefix? trimmed "c"))
       (void)]
      [(string-prefix? trimmed "p cnf")
       (define parts (string-split trimmed))
       (set! nvars (string->number (list-ref parts 2)))
       (set! nclauses (string->number (list-ref parts 3)))]
      [else
       (define nums (map string->number (string-split trimmed)))
       (for ([n nums])
         (cond
           [(zero? n)
            (set! clauses (cons (list->vector (reverse cur-clause)) clauses))
            (set! cur-clause '())]
           [else
            (set! cur-clause (cons n cur-clause))]))]))
  (unless (null? cur-clause)
    (error 'read-dimacs-cnf "CNF file ended with an unterminated clause"))
  (values nvars nclauses (list->vector (reverse clauses))))

;; Check a CNF and an LRAT proof from input ports.
;; Returns a check-result struct.
(define (check-lrat-ports cnf-port lrat-port)
  (define t0 (current-milliseconds))
  (define-values (nvars nclauses init-clauses) (read-dimacs-cnf cnf-port))

  ;; Active clause database: id -> (vectorof literal)
  (define db (make-hasheqv))
  (for ([c (in-vector init-clauses)] [i (in-naturals 1)])
    (hash-set! db i c))

  ;; Partial assignment vector: 0 unassigned, 1 true (+v), -1 false (-v)
  ;; We size it large enough for any variable appearing in the CNF or proof.
  (define max-var nvars)
  (define val (make-vector (+ max-var 1024) 0))

  (define (ensure-var-capacity! v)
    (when (>= v (vector-length val))
      (define new-cap (+ (* 2 v) 1024))
      (define new-val (make-vector new-cap 0))
      (vector-copy! new-val 0 val)
      (set! val new-val)))

  (define (lit-false? l)
    (define v (abs l))
    (ensure-var-capacity! v)
    (define s (vector-ref val v))
    (if (> l 0) (= s -1) (= s 1)))

  (define last-id nclauses)
  (define empty-derived? #f)
  (define additions-count 0)
  (define deletions-count 0)
  (define total-steps 0)

  (with-handlers
    ([exn:fail?
      (lambda (e)
        (define t1 (current-milliseconds))
        (check-result 'REJECT nvars nclauses additions-count deletions-count
                      total-steps (- t1 t0) (exn-message e)))])

    (for ([line (in-lines lrat-port)] #:break empty-derived?)
      (define trimmed (string-trim line))
      (unless (string=? trimmed "")
        (set! total-steps (add1 total-steps))
        (define toks (string-split trimmed))
        (define id (string->number (car toks)))
        (cond
          ;; Deletion line: <id> d <id1> <id2> ... 0
          [(equal? (cadr toks) "d")
           (set! deletions-count (add1 deletions-count))
           (define dels (map string->number (drop (drop-right toks 1) 2)))
           (for ([d dels])
             (hash-remove! db d))]

          ;; Addition line: <id> <lits...> 0 <hints...> 0
          [else
           (set! additions-count (add1 additions-count))
           (unless (> id last-id)
             (error 'check-lrat "Clause ID not strictly increasing: ~a <= ~a" id last-id))
           (set! last-id id)

           (define nums (map string->number (cdr toks)))
           (define-values (lits rest) (splitf-at nums (lambda (x) (not (zero? x)))))
           (define hints (drop-right (cdr rest) 1))

           ;; Check for RAT hints (negative numbers)
           (when (ormap negative? hints)
             (error 'check-lrat "Step ~a: RAT steps (negative hints) are not supported" id))

           ;; Setup assignment alpha by negating each literal in lits
           (define trail '())
           (for ([l lits])
             (define v (abs l))
             (ensure-var-capacity! v)
             (when (> v max-var) (set! max-var v))
             (vector-set! val v (if (> l 0) -1 1))
             (set! trail (cons v trail)))

           ;; Follow unit propagation hints
           (define conflict? #f)
           (define remaining-hints hints)
           (for ([h hints] #:break conflict?)
             (set! remaining-hints (cdr remaining-hints))
             (define cl (hash-ref db h
                                  (lambda ()
                                    (error 'check-lrat "Step ~a: Hint clause ~a not found in DB" id h))))
             ;; Count literals not falsified by alpha
             (define non-false '())
             (for ([l (in-vector cl)])
               (unless (lit-false? l)
                 (unless (member l non-false)
                   (set! non-false (cons l non-false)))))
             (cond
               ;; All literals false: conflict!
               [(null? non-false)
                (set! conflict? #t)]
               ;; Exactly one literal not false: unit propagate
               [(= (length non-false) 1)
                (define u (car non-false))
                (define uv (abs u))
                (ensure-var-capacity! uv)
                (when (= (vector-ref val uv) 0)
                  (vector-set! val uv (if (> u 0) 1 -1))
                  (set! trail (cons uv trail)))]
               ;; Multiple literals not false: hint is not unit
               [else
                (error 'check-lrat
                       "Step ~a: Hint clause ~a has ~a non-falsified literals (expected <= 1)"
                       id h (length non-false))]))

           ;; Revert trail
           (for ([v trail])
             (vector-set! val v 0))

           (unless conflict?
             (error 'check-lrat "Step ~a: Hints did not produce a conflict" id))

           (unless (null? remaining-hints)
             (error 'check-lrat "Step ~a: Conflict occurred before final hint (~a hints unused)"
                    id (length remaining-hints)))

           (if (null? lits)
               (set! empty-derived? #t)
               (hash-set! db id (list->vector lits)))])))

    (define t1 (current-milliseconds))
    (if empty-derived?
        (check-result 'ACCEPT nvars nclauses additions-count deletions-count
                      total-steps (- t1 t0) "Empty clause successfully derived via RUP")
        (check-result 'REJECT nvars nclauses additions-count deletions-count
                      total-steps (- t1 t0) "Proof ended without deriving empty clause"))))

;; Check CNF and LRAT from file paths.
(define (check-lrat-files cnf-path lrat-path)
  (call-with-input-file cnf-path
    (lambda (cnf-in)
      (call-with-input-file lrat-path
        (lambda (lrat-in)
          (check-lrat-ports cnf-in lrat-in))))))

;; CLI entry point
(module+ main
  (define args (current-command-line-arguments))
  (cond
    [(= (vector-length args) 2)
     (define cnf-file (vector-ref args 0))
     (define lrat-file (vector-ref args 1))
     (define res (check-lrat-files cnf-file lrat-file))
     (printf "[~a] ~a\n" (check-result-status res) (check-result-message res))
     (printf "  Vars: ~a, Clauses: ~a, Additions: ~a, Deletions: ~a, Total steps: ~a, Time: ~a ms\n"
             (check-result-nvars res)
             (check-result-nclauses res)
             (check-result-additions res)
             (check-result-deletions res)
             (check-result-total-steps res)
             (check-result-elapsed-ms res))
     (exit (if (eq? (check-result-status res) 'ACCEPT) 0 1))]
    [else
     (eprintf "Usage: racket check-lrat.rkt <CNF-FILE> <LRAT-FILE>\n")
     (exit 2)]))
