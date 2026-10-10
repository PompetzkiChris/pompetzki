#lang racket/base
;; kernel-v1.rkt -- lane L2D: arithmetic on omega as ZF lemmas, from the replay's recursion theorem (95) and induction
;; principle (88). Not trusted; each lemma is checked by core-v1's copy of the checker as it is built, then by the judges.
;;
;; Frame variables of every kernel lemma: 0 = w, 1 = p, 2 = g, 3 = o, and
;;   Ctx := Om(w) & Pr(p,w,w) & CapS(g,p,w) & Emp(o)
;; g is the successor function on w (CapS, replay 127-131), o is zero.
;;   Ad(x,y,z) := exists a (Rec(a,w,g,w,x) & App(a,y,z))                     z = x + y
;;   Mu(x,y,z) := exists m exists a ((Rec(a,w,g,w,x) & Rec(m,w,a,w,o)) & App(m,y,z))   z = x * y
;; Rec(e,w,f,a,c) (Data.v Rec5): e : w -> a a function, e(0) = c, e(S n) = f(e(n)).
;; Lemma statements are  Ctx -> (h1 -> ... -> phi)  with free variables 0..3 and the lemma's own (4, 5, ...).
(require racket/list racket/match (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt"))
(provide (all-defined-out))

(define W 0) (define PP 1) (define GG 2) (define O 3)
(define CTX-DSL '(and (pr Om 0) (pr Pr 1 0 0) (pr CapS 2 1 0) (pr Emp 3)))
(define (ctx-hyps) (list (ac '(pr Om 0)) (ac '(pr Pr 1 0 0)) (ac '(pr CapS 2 1 0)) (ac '(pr Emp 3))))
(define (kctx) (mkcx (ctx-hyps)))

(define gs-n 0)
(define (gs base) (set! gs-n (add1 gs-n)) (string->symbol (format "~a_~a" base gs-n)))
(define (Ad x y z) (let ([a (gs 'a)]) `(ex ,a (and (pr Rec ,a 0 2 0 ,x) (pr App ,a ,y ,z)))))
(define (Mu x y z) (let ([a (gs 'a)] [m (gs 'm)]) `(ex ,m (ex ,a (and (and (pr Rec ,a 0 2 0 ,x) (pr Rec ,m 0 ,a 0 3)) (pr App ,m ,y ,z))))))

;; replay theorems, imported with their dependencies
(define (rp i) (import-replay! i))
;; Kf parts
(define (kparts f) (match f [(list 'N (list 'I a (list 'N b))) (values a b)] [_ (error 'kparts "not a conjunction: ~a" (show f))]))

;; the facts of the context about g and w: Fnc(g), Tot(g,w), Rng(g,w), and x,y in w & Suc(y,x) -> App(g,x,y)
(define (g-facts k)
  (list (use (rp 127) '(1 0 2)) (use (rp 128) '(1 0 2)) (use (rp 129) '(1 0 2)) (use (rp 131) '(1 0 2))))

;; Rec(e,w,f,a,c) unfolded, in context k where hyp line hl proves Rec(e,...): returns facts
;;   (values fnc tot rng zero step) each a fact in k
(define (rec-parts k hl e w f a c)
  (define d (defn 'Rec (list e w f a c)))
  (define body (def-rhs d))
  (define-values (b1 stp) (kparts body))
  (define-values (b2 b3) (kparts b1))
  (define-values (fnc tot) (kparts b2))
  (define-values (rng zer) (kparts b3))
  (values (have k fnc hl d) (have k tot hl d) (have k rng hl d) (have k zer hl d) (have k stp hl d)))

(define-syntax-rule (defkey name (key) body ...) (hash-set! generators 'name (lambda (key) body ...)))
(define (ids n) (for/list ([i n]) i))

;; RecAdd: Ctx -> (x in w -> exists a Rec(a,w,g,w,x))          x = 4
(defkey RecAdd (key)
  (begin-thm! key 5)
  (define k (kctx))
  (define x 4)
  (define gf (g-facts k))
  (define r (use (rp 95) '() 0 2 0 x))
  (define goal `(imp (in ,x 0) (ex e (pr Rec e 0 2 0 ,x))))
  (have k goal gf r)
  (end-thm! (ac `(imp ,CTX-DSL ,goal)) (ids 5)))

;; AddEx: Ctx -> (x in w -> (y in w -> exists z (z in w & Ad(x,y,z))))    x = 4, y = 5
(defkey AddEx (key)
  (begin-thm! key 6)
  (define x 4) (define y 5)
  (define k (cx+ (kctx) `(in ,x 0) `(in ,y 0)))
  (define ra (have k `(ex e (pr Rec e 0 2 0 ,x)) (U 'RecAdd (ids 5))))
  (define goal `(ex z (and (in z 0) ,(Ad x y 'z))))
  (define res
    (ex-e k ra
      (lambda (k2 a)
        (define hl (have k2 `(pr Rec ,a 0 2 0 ,x)))
        (define-values (fnc tot rng zer stp) (rec-parts k2 hl a 0 2 0 x))
        (define t1 (all-e k2 tot y))                       ; y in w -> exists z App(a,y,z)
        (define t2 (have k2 `(ex z (pr App ,a ,y z)) t1))
        (ex-e k2 t2
          (lambda (k3 z)
            (define rz (all-e k3 rng y z))                 ; App(a,y,z) -> z in w
            (define ad (ex-i k3 (have k3 `(and (pr Rec ,a 0 2 0 ,x) (pr App ,a ,y ,z)) hl) a (Ad x y z)))
            (ex-i k3 (have k3 `(and (in ,z 0) ,(Ad x y z)) ad rz) z goal))))))
  (have (kctx) `(imp (in ,x 0) (in ,y 0) ,goal) res)
  (end-thm! (ac `(imp ,CTX-DSL (imp (in ,x 0) (in ,y 0) ,goal))) (ids 6)))

;; AddUq: Ctx -> (y in w -> (Ad(x,y,z) -> (Ad(x,y,u) -> z = u)))      x = 4, y = 5, z = 6, u = 7
(defkey AddUq (key)
  (begin-thm! key 8)
  (define-values (x y z u) (values 4 5 6 7))
  (define k (cx+ (kctx) `(in ,y 0) (Ad x y z) (Ad x y u)))
  (define res
    (ex-e k (have k (Ad x y z))
      (lambda (k2 a1)
        (ex-e k2 (have k2 (Ad x y u))
          (lambda (k3 a2)
            (define h1 (have k3 `(pr Rec ,a1 0 2 0 ,x)))
            (define h2 (have k3 `(pr Rec ,a2 0 2 0 ,x)))
            (define-values (fnc1 tot1 rng1 zer1 stp1) (rec-parts k3 h1 a1 0 2 0 x))
            (define gt (use (rp 128) '(1 0 2)))           ; Tot(g,w)
            (define un (use (rp 133) (list 0 2 0 a1 x a2)))  ; Om, Tot(g,w), Rec a1, Rec a2 -> forall i in w forall v (App a1 <-> App a2)
            (define un2 (have k3 (rhs-of (line un)) un gt h1 h2))
            (define un3 (all-e k3 un2 y))
            (define un4 (have k3 (rhs-of (concl k3 un3)) un3))
            (define un5 (all-e k3 un4 u))                  ; App(a1,y,u) <-> App(a2,y,u)
            (define fa (use (rp 16) '() a1 y z u))         ; Fnc(a1) -> (App a1 y z & App a1 y u -> z = u)
            (have k3 `(eq ,z ,u) un5 fa fnc1)))))))
  (have (kctx) `(imp (in ,y 0) ,(Ad x y z) ,(Ad x y u) (eq ,z ,u)) res)
  (end-thm! (ac `(imp ,CTX-DSL (imp (in ,y 0) ,(Ad x y z) ,(Ad x y u) (eq ,z ,u)))) (ids 8)))
