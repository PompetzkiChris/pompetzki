#lang racket/base
;; lrat-v1.rkt -- lane L2D, derived rule LRAT: a DIMACS CNF F over x1..xn and an LRAT refutation of F (RUP steps)
;; become the closed ZF theorem [S], S the bounded sentence (sigma1's language and translation)
;;     S  =  all x1<2 ... all xn<2  not (C1 and ... and Cm),   literal xi -> (xi = 1),  -xi -> not (xi = 1).
;; Not trusted. The derivation follows the LRAT proof step by step; no truth table over the 2^n assignments is built.
;;
;; Inside one theorem the frame variables 0,1,2 are the numerals (Chain(2)); p_i = i+2 stands for x_i.
;;  - e_i := (p_i = v1). C'_j := the clause j over the e_i, B_j := all z C'_j (vacuous), W := all z (B_1 & ... & B_m).
;;    W and the B_j are single atoms for the tautology test, so every T step costs linear time in m plus 2^(few).
;;  - Each input clause j: line W -> C'_j.  Each RUP step (lits L, hints h_1..h_r): one T step per hint, deriving
;;    W -> (L or u_t) for the unit u_t that hint t propagates, and W -> L at the conflict.
;;  - The empty clause gives W -> not (0 = 0); then not (B_1 & ... & B_m); then, through Chain(2) -> (A_i <-> e_i) with
;;    A_i = [x_i = 1] = exists u (N_1(u) & p_i = u), Chain(2) -> not (C_1 & ... & C_m) in sigma1's translation.
;;  - The n bounded quantifiers are introduced one by one (H, E with witness v2, NumEx(2)); the chain is eliminated.
;; Usage:
;;   racket lrat-v1.rkt emit CNF LRAT OUT.jdg        one file, plus OUT-mut/*.jdg, OUT.index.txt, OUT.manifest.txt
;;   racket lrat-v1.rkt judge LIST-OF-JDG... -- RESULTS.txt   both judges on each file (and its mutants)
(require racket/list racket/string racket/match racket/file racket/port (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt"))
(provide (all-defined-out))

;; ---------------------------------------------------------------- input
(define (read-dimacs path)
  (define toks (filter (lambda (l) (not (or (string-prefix? l "c") (string=? l "")))) (map string-trim (file->lines path))))
  (define hdr (string-split (car toks)))
  (unless (and (equal? (car hdr) "p") (equal? (cadr hdr) "cnf")) (error 'dimacs "header"))
  (define n (string->number (caddr hdr)))
  (define m (string->number (cadddr hdr)))
  (define nums (map string->number (append* (map string-split (cdr toks)))))
  (define cls (let loop ([ns nums] [cur '()] [acc '()])
                (cond [(null? ns) (reverse acc)]
                      [(= (car ns) 0) (loop (cdr ns) '() (cons (reverse cur) acc))]
                      [else (loop (cdr ns) (cons (car ns) cur) acc)])))
  (unless (= (length cls) m) (error 'dimacs "~a clauses, header says ~a" (length cls) m))
  (for* ([c cls] [l c]) (unless (<= 1 (abs l) n) (error 'dimacs "literal ~a out of range" l)))
  (values n cls))

;; LRAT: (list id lits hints) for addition lines; deletion lines are skipped
(define (read-lrat path)
  (for/list ([l (map string-trim (file->lines path))]
             #:unless (or (string=? l "") (string-prefix? l "c"))
             #:unless (let ([ws (string-split l)]) (and (> (length ws) 1) (equal? (cadr ws) "d"))))
    (define ns (map string->number (string-split l)))
    (define id (car ns))
    (define-values (lits rest) (splitf-at (cdr ns) (lambda (x) (not (= x 0)))))
    (define hints (takef (cdr rest) (lambda (x) (not (= x 0)))))
    (when (ormap negative? hints) (error 'lrat "line ~a: RAT hints are not supported (RUP only)" id))
    (list id lits hints)))

;; ---------------------------------------------------------------- formulas
(define (pv v) (+ v 2))                                   ; frame variable of x_v
(define (elit l) (if (> l 0) `(eq ,(pv l) 1) `(not (eq ,(pv (- l)) 1))))
(define BOT (Neg (Eqv 0 0)))
(define (disj lits) (if (null? lits) BOT (c `(or ,@(map elit lits)))))
(define (vac f) (All (ren add1 f)))                       ; all z f, z not free
(define (conj fs) (for/fold ([acc (car fs)]) ([f (cdr fs)]) (Kf acc f)))

;; the sentence in sigma1's language
(define (xsym v) (string->symbol (format "x~a" v)))
(define (slit l) (if (> l 0) `(= ,(xsym l) 1) `(not (= ,(xsym (- l)) 1))))
(define (sclause cl) `(or ,@(map slit cl)))
(define (sbody cls) `(not (and ,@(map sclause cls))))
(define (sentence n cls)
  (for/fold ([body (sbody cls)]) ([v (in-range n 0 -1)]) `(all ,(xsym v) 2 ,body)))

;; ---------------------------------------------------------------- the theorem
(define stat-hint-steps 0)
(define (inc-hint!) (set! stat-hint-steps (add1 stat-hint-steps)))

(define (lrat-thm! key n cls proof)
  (define m (length cls))
  (begin-thm! key (+ n 3))
  (set-Cc! (c (chain 2)))
  (define Cps (map disj cls))                             ; C'_j
  (define Bs (map vac Cps))
  (define GB (conj Bs))
  (define W (vac GB))
  (define w1 (V 0 (Imp W GB)))
  (define cl-lits (make-hash))                            ; clause id -> literals
  (define cl-line (make-hash))                            ; clause id -> line W -> C'
  (for ([cl cls] [Cp Cps] [B Bs] [j (in-naturals 1)])
    (define bj (V 0 (Imp B Cp)))
    (hash-set! cl-lits j cl)
    (hash-set! cl-line j (T (list w1 bj) (Imp W Cp))))
  (define refl (Y (Eqv 0 0)))
  ;; the RUP steps
  (define empty-line
    (for/or ([st proof])
      (match-define (list id L hints) st)
      (define val (make-hash))                            ; var -> #t/#f  (value of e_var)
      (define unit-line (make-hash))                      ; var -> line W -> (L or u)
      (for ([l L]) (hash-set! val (abs l) (< l 0)))
      (define (lit-true? l) (let ([v (hash-ref val (abs l) 'none)]) (and (not (eq? v 'none)) (eq? v (> l 0)))))
      (define (lit-false? l) (let ([v (hash-ref val (abs l) 'none)]) (and (not (eq? v 'none)) (not (eq? v (> l 0))))))
      (define done
        (for/or ([h hints] [t (in-naturals)])
          (define D (hash-ref cl-lits h (lambda () (error 'lrat "step ~a: hint ~a unknown" id h))))
          (when (ormap lit-true? D) (error 'lrat "step ~a: hint ~a is satisfied" id h))
          (define open (filter (lambda (l) (not (lit-false? l))) D))
          (define prem (cons (hash-ref cl-line h)
                             (remove-duplicates
                              (for/list ([l D] #:when (and (lit-false? l) (hash-ref unit-line (abs l) #f))) (hash-ref unit-line (abs l))))))
          (inc-hint!)
          (cond
            [(null? open)                                 ; conflict
             (define ln (T (if (null? L) (append prem (list refl)) prem) (Imp W (disj L))))
             ln]
            [(null? (cdr open))
             (define u (car open))
             (define ln (T prem (Imp W (disj (append L (list u))))))
             (hash-set! val (abs u) (> u 0))
             (hash-set! unit-line (abs u) ln)
             #f]
            [else (error 'lrat "step ~a: hint ~a is not unit (open ~a)" id h open)])))
      (unless done (error 'lrat "step ~a: no conflict" id))
      (hash-set! cl-lits id L)
      (hash-set! cl-line id done)
      (and (null? L) done)))
  (unless empty-line (error 'lrat "the proof does not reach the empty clause"))
  ;; not (B_1 & ... & B_m)
  (define g1 (Y (Imp GB W)))
  (define g2 (T (list empty-line g1 refl) (Neg GB)))
  ;; Chain(2) -> (A_i <-> e_i)
  (define A-form (make-hash))
  (define conv (make-hash))
  (define (A v) (hash-ref! A-form v (lambda () (c (tr `(= ,(xsym v) 1) (list (cons (xsym v) (pv v))))))))
  (define vars (remove-duplicates (map abs (append* cls))))
  (for ([v vars])
    (define p (pv v))
    (define e (Eqv p 1))
    (define n1 (numex-line 1))
    (define e1 (E 1 (Imp (c `(and ,(num 1 1) (eq ,p 1))) (A v))))
    (define a1 (T (list n1 e1) (cimp (Imp e (A v)))))
    (define q (fresh!))
    (define u1 (numuq-line 1 q))
    (define z1 (leib `(eq ,p ,HOLE) q 1))
    (define t1 (T (list u1 z1) (Imp (c `(and ,(num 1 q) (eq ,p ,q))) (cimp e))))
    (define l1 (L t1 q (Imp (A v) (cimp e))))
    (hash-set! conv v (T (list a1 l1) (cimp (Qf (A v) e)))))
  ;; per clause: Chain -> (BA_j -> B_j), with CA_j the clause in the A atoms
  (define CAs (for/list ([cl cls]) (c (sclause-tr cl))))
  (define BAs (map vac CAs))
  (define fcs
    (for/list ([cl cls] [CA CAs] [BA BAs] [Cp Cps] [B Bs])
      (define fa (V 0 (Imp BA CA)))
      (define fb (Y (Imp Cp B)))
      (T (list* fa fb (map (lambda (v) (hash-ref conv v)) (remove-duplicates (map abs cl)))) (cimp (Imp BA B)))))
  (define e4 (T (cons g2 fcs) (cimp (Neg (conj BAs)))))
  (define vacs (for/list ([CA CAs] [BA BAs]) (Y (Imp CA BA))))
  (define r-n (for/list ([v (in-range 1 (add1 n))]) (cons (xsym v) (pv v))))
  (define phi (c (tr (normalize (sbody cls)) r-n)))
  (define e5 (T (cons e4 vacs) (cimp phi)))
  ;; the bounded quantifiers, innermost first
  (define S (normalize (sentence n cls)))
  (define (sub-sentence k)                                ; the sentence after the first k quantifiers
    (let loop ([s S] [k k]) (if (= k 0) s (loop (cadddr s) (sub1 k)))))
  (define top
    (for/fold ([cur e5]) ([k (in-range n 0 -1)])
      (define p (pv k))
      (define inner (sub-sentence k))                     ; body under x_1..x_k
      (define r-k (take r-n k))
      (define r-k1 (take r-n (sub1 k)))
      (define l2 (T (list cur) (cimp (c `(imp (in ,p 2) ,(tr inner r-k))))))
      (define x (fresh-sym 'x))
      (define l3 (H p l2 (cimp (c `(all ,x (imp (in ,x 2) ,(tr inner (append r-k1 (list (cons (xsym k) x))))))))))
      (define whole (c (tr (sub-sentence (sub1 k)) r-k1)))
      (define l4 (E 2 (Imp (c `(and ,(num 2 2) (all ,x (imp (in ,x 2) ,(tr inner (append r-k1 (list (cons (xsym k) x)))))))) whole)))
      (T (list (numex-line 2) l3 l4) (cimp whole))))
  (define stmt (c (tr S '())))
  (elim-chain top 2 stmt)
  (end-thm! stmt '()))

(define (sclause-tr cl) (tr (normalize (sclause cl)) (for/list ([l cl]) (cons (xsym (abs l)) (pv (abs l))))))

;; ---------------------------------------------------------------- files
(define (emit-file cnf lrat out)
  (load-base!)
  (reset-batch!)
  (set! stat-hint-steps 0)
  (define-values (n cls) (read-dimacs cnf))
  (define proof (read-lrat lrat))
  (define t0 (current-milliseconds))
  (lrat-thm! `(LRAT ,(path->string (file-name-from-path cnf))) n cls proof)
  (define ms (- (current-milliseconds) t0))
  (define text (batch-text))
  (write-new out text)
  (define-values (rg ths) (read-jdg-text text))
  (define base (regexp-replace #rx"[.]jdg$" out ""))
  (define mdir (string-append base "-mut"))
  (make-directory* mdir)
  (define ths-keys (map car (reverse out-thms)))
  (define pflags (map caddr (reverse out-thms)))
  ;; twin: the sentence for F without its last clause (satisfiable or not, it is not the derived statement)
  (define twin (c (tr (normalize (sentence n (drop-right cls 1))) '())))
  (define muts (mutants text twin pflags))
  (define lines
    (list (format "~a  from ~a and ~a" out cnf lrat)
          (format "  CNF: ~a variables, ~a clauses; LRAT: ~a addition steps, ~a hints (one T step each)" n (length cls) (length proof) stat-hint-steps)
          (format "  theorems ~a (prelude ~a, generated ~a), steps ~a (prelude ~a), bytes ~a, build ~a ms"
                  (length ths) (hash-ref stats 'prelude 0) (hash-ref stats 'theorems 0)
                  (+ (hash-ref stats 'steps 0) (hash-ref stats 'prelude-steps 0)) (hash-ref stats 'prelude-steps 0)
                  (file-size out) ms)
          (format "  largest tautology test ~a calls" (hash-ref stats 'taut-max 0))
          (format "  sha256 ~a" (sha256-hex out))
          (format "  registry: ~a" (check-registry-text text))
          (format "  copy of the checker: ~a" (check-batch rg ths))))
  (for-each displayln lines)
  (define mlines
    (for/list ([mu muts])
      (match-define (list tag mtext) mu)
      (define mf (build-path mdir (string-append (path->string (file-name-from-path base)) "-" tag ".jdg")))
      (write-new mf mtext)
      (define-values (mrg mths) (read-jdg-text mtext))
      (format "  mutant ~a: copy of the checker ~a" tag (check-batch mrg mths))))
  (for-each displayln mlines)
  (write-new (string-append base ".index.txt")
             (string-join (for/list ([k ths-keys] [t ths] [i (in-naturals)])
                            (format "~a ~a ~a" i k (if (and (pair? k) (eq? (car k) 'replay)) "" (show (tof (car t)))))) "\n"))
  (write-new (string-append base ".manifest.txt") (string-join (append lines mlines) "\n")))

(define (judge-files files results)
  (define o (open-output-file results #:exists 'error))
  (for ([f files])
    (define full (path->string (path->complete-path f)))
    (match-define (list e1 t1 o1) (run-cmd JUDGE-DIR PMP (list "judge-v3.pmp" full)))
    (match-define (list e2 t2 o2) (run-cmd JUDGE-DIR RACKET (list "racket/judge.rkt" full)))
    (define row (format "~a | pmp ~a exit ~a ~a ms | racket ~a exit ~a ~a ms | pmp: ~a | racket: ~a"
                        f (verdict o1) e1 t1 (verdict o2) e2 t2 (one-line o1) (one-line o2)))
    (displayln row o) (flush-output o)
    (printf "~a\n" row) (flush-output))
  (close-output-port o))

(module+ main
  (define args (vector->list (current-command-line-arguments)))
  (match args
    [(list "emit" cnf lrat out) (emit-file cnf lrat out)]
    [(list "judge" more ...)
     (define-values (files rest) (splitf-at more (lambda (a) (not (equal? a "--")))))
     (judge-files files (cadr rest))]
    [_ (printf "usage: racket lrat-v1.rkt emit CNF LRAT OUT.jdg | judge FILE... -- RESULTS.txt\n")]))
