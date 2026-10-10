#lang racket/base
;; cert-v1.rkt -- lane L2D: certificate theorems over binary numerals (bin-v6.rkt). Not trusted; every step is checked
;; by core-v1's copy of the checker as it is built, and every file by both judges.
;;
;; A certificate theorem is closed:
;;     forall w p g o (Om(w) & Pr(p,w,w) & CapS(g,p,w) & Emp(o) -> E_1 & ... & E_M)     (balanced conjunction)
;; Each E_i is the statement of one entry lemma (proved separately, so contexts stay small):
;;   (Lin ((s a b) ...) c)   the integer identity  sum_k s_k a_k b_k = c,  a_k, b_k >= 1, s_k = +1 / -1:
;;        forall u_k v_k e (Bin_a_k(u_k) -> Bin_b_k(v_k) -> Bin_|c|(e) ->
;;             exists t_k, partial sums (Mu(u_k,v_k,t_k) & ... & Ad(..) & ... & P = N))
;;        P = the sum of the products with s = +1 (and |c| when c < 0), N = those with s = -1 (and c when c > 0).
;;   (CMul a b) (CAdd a b) (CNZ n)   the lemmas of bin-v6.rkt (a*b = c, a+b = c, n /= 0 for numerals).
;; Zero products are left out of a Lin entry (they add 0).
(require racket/list racket/match racket/string racket/file racket/path
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt")
         (except-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel-v6.rkt") ids)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel2-v2.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel3-v4.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/bin-v6.rkt"))
(provide (all-defined-out))

;; ------------------------------------------------------------------ the Lin entry
;; plan: inputs (list (cons var value) ...), products, sums; built from the spec
(struct plan (inputs prods psum nsum pval nval))
;; prods: list of (list ui vi a b ti);  psum/nsum: list of steps (list x y v xval yval) meaning Ad(x,y,v);
;; the final P and N: a variable (symbol), or 3 (o) when the side is 0
(define (lin-plan terms c names)
  ;; names: a procedure making a fresh name from a base
  (define inputs '())
  (define (in! val) (let ([v (names 'u)]) (set! inputs (cons (cons v val) inputs)) v))
  (define prods
    (for/list ([t terms])
      (match-define (list s a b) t)
      (define u (in! a)) (define v (in! b))
      (list u v a b (names 't) s)))
  (define e (and (not (= c 0)) (in! (abs c))))
  (define (side sgn const?)
    (define items (append (for/list ([p prods] #:when (= (list-ref p 5) sgn)) (cons (list-ref p 4) (* (list-ref p 2) (list-ref p 3))))
                          (if const? (list (cons e (abs c))) '())))
    (cond
      [(null? items) (values '() 3 0)]
      [else
       (for/fold ([steps '()] [cur (car (car items))] [val (cdr (car items))] #:result (values (reverse steps) cur val))
                 ([it (cdr items)])
         (define v (names 's))
         (values (cons (list cur (car it) v val (cdr it)) steps) v (+ val (cdr it))))]))
  (define-values (psum pv pval) (side 1 (< c 0)))
  (define-values (nsum nv nval) (side -1 (> c 0)))
  (unless (= pval nval) (error 'lin "not an identity: ~a vs ~a in ~a = ~a" pval nval terms c))
  (values (reverse inputs) prods psum nsum pv nv pval))

(define (bconj-dsl xs) (if (null? (cdr xs)) (car xs) (let-values ([(l r) (split-at xs (quotient (length xs) 2))]) `(and ,(bconj-dsl l) ,(bconj-dsl r)))))

;; the formula of a Lin entry, with input variables given (frame variables or names) and intermediates bound
(define (lin-formula terms c)
  (define cnt 0)
  (define (names base) (set! cnt (add1 cnt)) (string->symbol (format "~a~a" base cnt)))
  (define-values (inputs prods psum nsum pv nv pval) (lin-plan terms c names))
  (define mids (append (map (lambda (p) (list-ref p 4)) prods) (map caddr psum) (map caddr nsum)))
  (define rels (append (for/list ([p prods]) (Mu (list-ref p 0) (list-ref p 1) (list-ref p 4)))
                       (for/list ([s (append psum nsum)]) (Ad (car s) (cadr s) (caddr s)))
                       (list `(eq ,pv ,nv))))
  (define body (if (null? mids) (bconj-dsl rels) `(ex ,@mids ,(bconj-dsl rels))))
  (values inputs `(all ,@(map car inputs) (imp ,@(for/list ([i inputs]) (Bin (cdr i) (car i))) ,body))))

(define-syntax-rule (defcert name (key) body ...) (hash-set! generators 'name (lambda (key) body ...)))

;; the Lin lemma:  Ctx -> lin-formula
(defcert Lin (key)
  (match-define (list _ terms c) key)
  (define-values (inputs stmt) (lin-formula terms c))
  (begin-thm! key 4)
  (define k0 (kctx))
  ;; fresh frame variables for the inputs, hypotheses Bin
  (define ivars (for/list ([i inputs]) (fresh!)))
  (define env (for/hash ([i inputs] [v ivars]) (values (car i) v)))
  (define hyps (for/list ([i inputs] [v ivars]) (Bin (cdr i) v)))
  (define k (apply cx+ k0 hyps))
  (define cnt 0)
  (define (names base) (set! cnt (add1 cnt)) (string->symbol (format "~a~a" base cnt)))
  (define-values (inputs2 prods psum nsum pv nv pval) (lin-plan terms c names))
  ;; inputs2 have the same order and values as inputs; map their names to ivars
  (define var (make-hash))
  (for ([i inputs2] [v ivars]) (hash-set! var (car i) v))
  (hash-set! var 3 3)
  (define (V* x) (hash-ref var x))
  (define val (make-hash))
  (for ([i inputs2]) (hash-set! val (car i) (cdr i)))
  ;; introduce canonical values for all intermediates, collecting facts, then pack
  (define rel-facts '())
  (define order (append (for/list ([p prods]) (list 'p p)) (for/list ([s psum]) (list 's s)) (for/list ([s nsum]) (list 's s))))
  (define final
    (let loop ([k k] [todo order])
      (cond
        [(null? todo)
         ;; P = N
         (define eqf
           (cond [(equal? pv nv) (have k `(eq ,(V* pv) ,(V* nv)) (Y (Eqv (V* pv) (V* pv))))]
                 [else (lem k `(BinUq ,pval) (list (V* pv) (V* nv)))]))
         ;; the conjunction of relations, then exists-intro over the intermediates (innermost last)
         (define mids (append (map (lambda (p) (list-ref p 4)) prods) (map caddr psum) (map caddr nsum)))
         (define (rels-with sub)            ; sub: name -> variable or name
           (append (for/list ([p prods]) (Mu (sub (list-ref p 0)) (sub (list-ref p 1)) (sub (list-ref p 4))))
                   (for/list ([s (append psum nsum)]) (Ad (sub (car s)) (sub (cadr s)) (sub (caddr s))))
                   (list `(eq ,(sub pv) ,(sub nv)))))
         (define all-v (lambda (x) (if (and (symbol? x) (hash-has-key? var x)) (V* x) (if (eqv? x 3) 3 x))))
         (define body-fact (have k (bconj-dsl (rels-with all-v)) (cons eqf rel-facts)))
         ;; exists-intro from the last intermediate to the first
         (for/fold ([cur body-fact]) ([i (in-range (length mids) 0 -1)])
           (define bound (take mids (sub1 i)))            ; still frame variables: mids from index i-1 on are being bound
           (define here (list-ref mids (sub1 i)))
           (define inner (drop mids i))
           (define (sub x) (cond [(memq x inner) x] [(eq? x here) x] [else (all-v x)]))
           (define X `(ex ,here ,@(if (null? inner) '() inner) ,(bconj-dsl (rels-with sub))))
           (define X2 (if (null? inner) `(ex ,here ,(bconj-dsl (rels-with sub))) `(ex ,here (ex ,@inner ,(bconj-dsl (rels-with sub))))))
           (ex-i k cur (V* here) X2))]
        [else
         (match (car todo)
           [(list 'p (list u v a b t s))
            (ex-e k (lemma-fact k `(BinEx ,(* a b)))
              (lambda (k2 tv)
                (hash-set! var t tv)
                (hash-set! val t (* a b))
                (set! rel-facts (cons (lem k2 `(CMul ,a ,b) (list (V* u) (V* v) tv)) rel-facts))
                (loop k2 (cdr todo))))]
           [(list 's (list x y v xv yv))
            (ex-e k (lemma-fact k `(BinEx ,(+ xv yv)))
              (lambda (k2 sv)
                (hash-set! var v sv)
                (hash-set! val v (+ xv yv))
                (set! rel-facts (cons (lem k2 `(CAdd ,xv ,yv) (list (V* x) (V* y) sv)) rel-facts))
                (loop k2 (cdr todo))))])])))
  ;; close: forall inputs (Bin hyps -> body)
  (define body-f (concl k final))
  (define f1 (have k0 `(imp ,@hyps ,body-f) final))
  (define f2 (for/fold ([cur f1]) ([v (reverse ivars)]) (all-i k0 v cur)))
  (define goal (ac stmt))
  (define f3 (have k0 goal f2))
  (end-thm! (ac `(imp ,CTX-DSL ,stmt)) (ids 4)))

;; ------------------------------------------------------------------ the certificate theorem
(define (entry-stmt spec) (reg-stmt (ensure! spec)))      ; Ctx -> E
(define (cert-thm! key specs)
  (for ([s specs]) (ensure! s))
  (begin-thm! key 4)
  (define k (kctx))
  (define facts (for/list ([s specs]) (lemma-fact k s)))
  (define (combine fs)
    (if (null? (cdr fs)) (car fs)
        (let-values ([(l r) (split-at fs (quotient (length fs) 2))])
          (define a (combine l)) (define b (combine r))
          (have k (Kf (concl k a) (concl k b)) a b))))
  (define top (combine facts))
  (define g (for/fold ([cur top]) ([v '(3 2 1 0)]) (G cur v)))
  (end-thm! (line g) '()))
