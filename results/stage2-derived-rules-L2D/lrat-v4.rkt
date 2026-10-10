#lang racket/base
;; lrat-v4.rkt -- lane L2D, derived rule LRAT, fourth version. lrat-v3.rkt with balanced conjunction trees: the
;; statement's conjunction of clauses, B_1 & ... & B_m and BA_1 & ... & BA_m are parenthesised as balanced binary
;; trees, so that no formula nests deeper than the pmp judge's interpreter allows (pompetzki.asm: MAXRET = 256 gosub
;; frames; probe files in probe/: propositional nesting fails between 240 and 320 levels, left-nested conjunctions
;; between 120 and 160 conjuncts, quantifier nesting passes at 240). v3's left-nested trees made pmp stop with
;; "gosub: too deep" on php5-4, rand14-80 and rand20-120.
;;
;; The sentence (sigma1's language and translation):
;;     S = all x1<2 ... all xn<2 not (C1 and ... and Cm),  the "and" a balanced tree,  xi -> (xi = 1), -xi -> not (xi = 1)
;; Derivation as in lrat-v1.rkt's header: one T step per LRAT hint over the opaque atoms W and B_j; the empty clause;
;; conversion to the A-atoms of the translation; the n bounded quantifiers; chain elimination.
;; Mutants: core-v1's generic ones plus input-goal-neg, rup-goal-neg, conflict-drop, cnf-flip (see lrat-v3.rkt).
;; Usage: racket lrat-v4.rkt emit CNF LRAT OUT.jdg | judge FILE... -- RESULTS.txt
(require racket/list racket/string racket/match racket/file racket/port racket/path
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (only-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/lrat-v2.rkt")
                  read-dimacs read-lrat pv elit BOT disj vac xsym slit sclause sclause-tr judge-files))
(provide (all-defined-out))

;; balanced trees
(define (halves xs) (split-at xs (quotient (length xs) 2)))
(define (bconj fs) (if (null? (cdr fs)) (car fs) (let-values ([(l r) (halves fs)]) (Kf (bconj l) (bconj r)))))
(define (btree op xs) (if (null? (cdr xs)) (car xs) (let-values ([(l r) (halves xs)]) (list op (btree op l) (btree op r)))))
(define (sbody cls) `(not ,(btree 'and (map sclause cls))))
(define (sentence n cls) (for/fold ([body (sbody cls)]) ([v (in-range n 0 -1)]) `(all ,(xsym v) 2 ,body)))

(define stat-hint-steps 0)
(define marks (make-hash))
(define (mark! k v) (unless (hash-ref marks k #f) (hash-set! marks k v)))

(define (depth f) (match f [(list (or 'E 'Q 'P) _ _) 1] [(list (or 'N 'A) a) (add1 (depth a))] [(list 'I a b) (add1 (max (depth a) (depth b)))]))

(define (lrat-thm! key n cls proof)
  (begin-thm! key (+ n 3))
  (set-Cc! (c (chain 2)))
  (define Cps (map disj cls))
  (define Bs (map vac Cps))
  (define GB (bconj Bs))
  (define W (vac GB))
  (define w1 (V 0 (Imp W GB)))
  (define cl-lits (make-hash))
  (define cl-line (make-hash))
  (for ([cl cls] [Cp Cps] [B Bs] [j (in-naturals 1)])
    (define bj (V 0 (Imp B Cp)))
    (hash-set! cl-lits j cl)
    (define ln (T (list w1 bj) (Imp W Cp)))
    (mark! 'input ln)
    (hash-set! cl-line j ln))
  (define refl (Y (Eqv 0 0)))
  (define empty-line
    (for/or ([st proof])
      (match-define (list id L hints) st)
      (define val (make-hash))
      (define unit-line (make-hash))
      (for ([l L]) (hash-set! val (abs l) (< l 0)))
      (define (lit-true? l) (let ([v (hash-ref val (abs l) 'none)]) (and (not (eq? v 'none)) (eq? v (> l 0)))))
      (define (lit-false? l) (let ([v (hash-ref val (abs l) 'none)]) (and (not (eq? v 'none)) (not (eq? v (> l 0))))))
      (define done
        (for/or ([h hints])
          (define D (hash-ref cl-lits h (lambda () (error 'lrat "step ~a: hint ~a unknown" id h))))
          (when (ormap lit-true? D) (error 'lrat "step ~a: hint ~a is satisfied" id h))
          (define open (filter (lambda (l) (not (lit-false? l))) D))
          (define prem (cons (hash-ref cl-line h)
                             (remove-duplicates
                              (for/list ([l D] #:when (and (lit-false? l) (hash-ref unit-line (abs l) #f))) (hash-ref unit-line (abs l))))))
          (set! stat-hint-steps (add1 stat-hint-steps))
          (cond
            [(null? open) (T (if (null? L) (append prem (list refl)) prem) (Imp W (disj L)))]
            [(null? (cdr open))
             (define u (car open))
             (define ln (T prem (Imp W (disj (append L (list u))))))
             (mark! 'hint ln)
             (hash-set! val (abs u) (> u 0))
             (hash-set! unit-line (abs u) ln)
             #f]
            [else (error 'lrat "step ~a: hint ~a is not unit (open ~a)" id h open)])))
      (unless done (error 'lrat "step ~a: no conflict" id))
      (hash-set! cl-lits id L)
      (hash-set! cl-line id done)
      (and (null? L) done)))
  (unless empty-line (error 'lrat "the proof does not reach the empty clause"))
  (hash-set! marks 'empty empty-line)
  (define g1 (Y (Imp GB W)))
  (define g2 (T (list empty-line g1 refl) (Neg GB)))
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
  (define CAs (for/list ([cl cls]) (c (sclause-tr cl))))
  (define BAs (map vac CAs))
  (define fcs
    (for/list ([cl cls] [CA CAs] [BA BAs] [Cp Cps] [B Bs])
      (define fa (V 0 (Imp BA CA)))
      (define fb (Y (Imp Cp B)))
      (T (list* fa fb (map (lambda (v) (hash-ref conv v)) (remove-duplicates (map abs cl)))) (cimp (Imp BA B)))))
  (define e4 (T (cons g2 fcs) (cimp (Neg (bconj BAs)))))
  (define vacs (for/list ([CA CAs] [BA BAs]) (Y (Imp CA BA))))
  (define r-n (for/list ([v (in-range 1 (add1 n))]) (cons (xsym v) (pv v))))
  (define phi (c (tr (normalize (sbody cls)) r-n)))
  (define e5 (T (cons e4 vacs) (cimp phi)))
  (define S (normalize (sentence n cls)))
  (define (sub-sentence k) (let loop ([s S] [k k]) (if (= k 0) s (loop (cadddr s) (sub1 k)))))
  (define top
    (for/fold ([cur e5]) ([k (in-range n 0 -1)])
      (define p (pv k))
      (define inner (sub-sentence k))
      (define r-k (take r-n k))
      (define r-k1 (take r-n (sub1 k)))
      (define l2 (T (list cur) (cimp (c `(imp (in ,p 2) ,(tr inner r-k))))))
      (define x (fresh-sym 'x))
      (define body-x (tr inner (append r-k1 (list (cons (xsym k) x)))))
      (define l3 (H p l2 (cimp (c `(all ,x (imp (in ,x 2) ,body-x))))))
      (define whole (c (tr (sub-sentence (sub1 k)) r-k1)))
      (define l4 (E 2 (Imp (c `(and ,(num 2 2) (all ,x (imp (in ,x 2) ,body-x)))) whole)))
      (T (list (numex-line 2) l3 l4) (cimp whole))))
  (define stmt (c (tr S '())))
  (elim-chain top 2 stmt)
  (end-thm! stmt '()))

(define (targeted rg ths n cls)
  (define tv (list->vector ths))
  (define last-i (sub1 (vector-length tv)))
  (match-define (list st sig steps hyps) (vector-ref tv last-i))
  (define (with-step k f)
    (structure-text rg (for/list ([x tv] [j (in-naturals)])
                         (if (= j last-i) (list st sig (for/list ([s steps] [i (in-naturals)]) (if (= i k) (f s) s)) hyps) x))))
  (define flipped (let ([c1 (car cls)]) (cons (cons (- (car c1)) (cdr c1)) (cdr cls))))
  (list
   (list "input-goal-neg" (with-step (hash-ref marks 'input) (match-lambda [(list 'T ls g) (list 'T ls (list 'n g))])))
   (list "rup-goal-neg" (with-step (hash-ref marks 'hint) (match-lambda [(list 'T ls g) (list 'T ls (list 'n g))])))
   (list "conflict-drop" (with-step (hash-ref marks 'empty) (match-lambda [(list 'T ls g) (list 'T (cdr ls) g)])))
   (list "cnf-flip" (structure-text rg (for/list ([x tv] [j (in-naturals)])
                                         (if (= j last-i) (list (compress (c (tr (normalize (sentence n flipped)) '()))) sig steps hyps) x))))))

(define (emit-file cnf lrat out)
  (load-base!)
  (reset-batch!)
  (set! stat-hint-steps 0)
  (hash-clear! marks)
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
  (define twin (c (tr (normalize (sentence n (drop-right cls 1))) '())))
  (define muts (append (targeted rg ths n cls) (mutants text twin pflags)))
  (define main (last ths))
  (define main-steps (length (caddr main)))
  (define maxdepth (for*/fold ([d 0]) ([t ths] [s (caddr t)]) (match s [(list (or 'T 'E 'V 'Y 'L 'H) _ ... g) (max d (depth (tof g)))] [_ d])))
  (define lines
    (list (format "~a  from ~a and ~a" out cnf lrat)
          (format "  CNF: ~a variables, ~a clauses; LRAT: ~a addition steps, ~a hints (one T step each)" n (length cls) (length proof) stat-hint-steps)
          (format "  theorems ~a (prelude ~a, generated ~a), steps ~a (prelude ~a; main theorem ~a), bytes ~a, build ~a ms"
                  (length ths) (hash-ref stats 'prelude 0) (hash-ref stats 'theorems 0)
                  (+ (hash-ref stats 'steps 0) (hash-ref stats 'prelude-steps 0)) (hash-ref stats 'prelude-steps 0) main-steps
                  (file-size out) ms)
          (format "  largest tautology test ~a calls; deepest formula in a step ~a levels; statement ~a levels"
                  (hash-ref stats 'taut-max 0) maxdepth (depth (tof (car main))))
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

(module+ main
  (define args (vector->list (current-command-line-arguments)))
  (match args
    [(list "emit" cnf lrat out) (emit-file cnf lrat out)]
    [(list "judge" more ...)
     (define-values (files rest) (splitf-at more (lambda (a) (not (equal? a "--")))))
     (judge-files files (cadr rest))]
    [_ (printf "usage: racket lrat-v4.rkt emit CNF LRAT OUT.jdg | judge FILE... -- RESULTS.txt\n")]))
