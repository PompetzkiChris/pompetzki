#lang racket/base
;; kernel-v4.rkt (kernel-v3.rkt with every lemma key prefixed K: AddEx collided with a prelude name of core-v1) -- lane L2D: arithmetic on omega as ZF lemmas, from the replay's recursion theorem (95) and induction
;; principle (88). v1 used Tot/Rng/Fnc atoms without unfolding them; v2 unfolds them and adds the induction tactic.
;; Not trusted; each lemma is checked by core-v1's copy of the checker as it is built, then by the judges.
;;
;; Frame variables of every kernel lemma: 0 = w, 1 = p, 2 = g, 3 = o, and
;;   Ctx := Om(w) & Pr(p,w,w) & CapS(g,p,w) & Emp(o)
;; g is the successor function on w (CapS, replay 127-131), o is zero.
;;   Ad(x,y,z) := exists a (Rec(a,w,g,w,x) & App(a,y,z))                                   z = x + y
;;   Mu(x,y,z) := exists m exists a ((Rec(a,w,g,w,x) & Rec(m,w,a,w,o)) & App(m,y,z))       z = x * y
;; Rec(e,w,f,a,c) (Data.v Rec5): e : w -> a a function, e(0) = c, e(S n) = f(e(n)).
;; Lemma statements are  Ctx -> (h1 -> ... -> phi)  with free variables 0..3 and the lemma's own (4, 5, ...).
(require racket/list racket/match (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt"))
(provide (all-defined-out))

(define CTX-DSL '(and (pr Om 0) (pr Pr 1 0 0) (pr CapS 2 1 0) (pr Emp 3)))
(define (ctx-hyps) (list (ac '(pr Om 0)) (ac '(pr Pr 1 0 0)) (ac '(pr CapS 2 1 0)) (ac '(pr Emp 3))))
(define (kctx) (mkcx (ctx-hyps)))

(define gs-n 0)
(define (gs base) (set! gs-n (add1 gs-n)) (string->symbol (format "~a_~a" base gs-n)))
(define (Ad x y z) (let ([a (gs 'a)]) `(ex ,a (and (pr Rec ,a 0 2 0 ,x) (pr App ,a ,y ,z)))))
(define (Mu x y z) (let ([a (gs 'a)] [m (gs 'm)]) `(ex ,m (ex ,a (and (and (pr Rec ,a 0 2 0 ,x) (pr Rec ,m 0 ,a 0 3)) (pr App ,m ,y ,z))))))

(define (rp i) (import-replay! i))
(define (kparts f) (match f [(list 'N (list 'I a (list 'N b))) (values a b)] [_ (error 'kparts "not a conjunction: ~a" (show f))]))
(define (ids n) (for/list ([i n]) i))
(define-syntax-rule (defkey name (key) body ...) (hash-set! generators 'name (lambda (key) body ...)))

;; unfold a defined atom proved by fact l in context k: the fact body
(define (unf k p args l) (let ([d (defn p args)]) (have k (def-rhs d) l d)))
;; the consequent of a context-free line (a lemma instance  A -> B), as a fact in k (A must follow from k)
(define (cons-of k l) (have k (rhs-of (line l)) l))

;; Rec(e,w,f,a,c) proved by fact hl in k: (values fnc tot rng zero step); tot, rng unfolded to their bodies
(define (rec-parts k hl e w f a c)
  (define d (defn 'Rec (list e w f a c)))
  (define body (def-rhs d))
  (define-values (b1 stp) (kparts body))
  (define-values (b2 b3) (kparts b1))
  (define-values (fnc tot) (kparts b2))
  (define-values (rng zer) (kparts b3))
  (define tl (have k tot hl d))
  (define rl (have k rng hl d))
  (values (have k fnc hl d) (unf k 'Tot (list e w) tl) (unf k 'Rng (list e a) rl) (have k zer hl d) (have k stp hl d)))

;; x in w, from SucW / ZeroW
(define (sucw k x s . ls) (have k `(in ,s 0) (use (rp 84) '() 0 x s) ls))
(define (zerow k e . ls) (have k `(in ,e 0) (use (rp 83) '() 0 e) ls))
;; App(g,x,y) from x,y in w and Suc(y,x)
(define (gapp k x y . ls)
  (define u (use (rp 131) '(1 0 2)))
  (define f (cons-of k u))
  (have k `(pr App 2 ,x ,y) (all-e k f x y) ls))
;; s = t <-> symmetric use: from Eqv(a,b) get Eqv(b,a)
(define (eqsym k a b l) (have k `(eq ,b ,a) l (leibF `(eq ,LHOLE ,a) a b) (Y (Eqv a a))))

;; ------------------------------------------------------------------ addition: the recursion equations
;; RecAdd: Ctx -> (x in w -> exists a Rec(a,w,g,w,x))          x = 4
(defkey KRecAdd (key)
  (begin-thm! key 5)
  (define k (kctx))
  (define x 4)
  (define gf (list (use (rp 127) '(1 0 2)) (use (rp 128) '(1 0 2)) (use (rp 129) '(1 0 2))))
  (define r (use (rp 95) '() 0 2 0 x))
  (define goal `(imp (in ,x 0) (ex e (pr Rec e 0 2 0 ,x))))
  (have k goal gf r)
  (end-thm! (ac `(imp ,CTX-DSL ,goal)) (ids 5)))

;; AddEx: Ctx -> (x in w -> (y in w -> exists z (z in w & Ad(x,y,z))))    x = 4, y = 5
(defkey KAddEx (key)
  (begin-thm! key 6)
  (define x 4) (define y 5)
  (define k (cx+ (kctx) `(in ,x 0) `(in ,y 0)))
  (define ra (have k `(ex e (pr Rec e 0 2 0 ,x)) (U 'KRecAdd (ids 5))))
  (define goal `(ex z (and (in z 0) ,(Ad x y 'z))))
  (define res
    (ex-e k ra
      (lambda (k2 a)
        (define hl (have k2 `(pr Rec ,a 0 2 0 ,x)))
        (define-values (fnc tot rng zer stp) (rec-parts k2 hl a 0 2 0 x))
        (define t2 (have k2 `(ex z (pr App ,a ,y z)) (all-e k2 tot y)))
        (ex-e k2 t2
          (lambda (k3 z)
            (define rz (all-e k3 rng y z))
            (define ad (ex-i k3 (have k3 `(and (pr Rec ,a 0 2 0 ,x) (pr App ,a ,y ,z)) hl) a (Ad x y z)))
            (ex-i k3 (have k3 `(and (in ,z 0) ,(Ad x y z)) ad rz) z goal))))))
  (define fin `(imp (in ,x 0) (in ,y 0) ,goal))
  (have (kctx) fin res)
  (end-thm! (ac `(imp ,CTX-DSL ,fin)) (ids 6)))

;; AddUq: Ctx -> (y in w -> (Ad(x,y,z) -> (Ad(x,y,u) -> z = u)))      x = 4, y = 5, z = 6, u = 7
(defkey KAddUq (key)
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
            (define gt (use (rp 128) '(1 0 2)))
            (define un (use (rp 133) (list 0 2 0 a1 x a2)))
            (define un2 (have k3 (rhs-of (line un)) un gt h1 h2))
            (define un4 (have k3 (rhs-of (concl k3 (all-e k3 un2 y))) (all-e k3 un2 y)))
            (define un5 (all-e k3 un4 u))
            (define fa (use (rp 16) '() a1 y z u))
            (have k3 `(eq ,z ,u) un5 fa fnc1))))))
  (define fin `(imp (in ,y 0) ,(Ad x y z) ,(Ad x y u) (eq ,z ,u)))
  (have (kctx) fin res)
  (end-thm! (ac `(imp ,CTX-DSL ,fin)) (ids 8)))

;; AddZ: Ctx -> (x in w -> Ad(x,o,x))          x = 4
(defkey KAddZ (key)
  (begin-thm! key 5)
  (define x 4)
  (define k (cx+ (kctx) `(in ,x 0)))
  (define ra (have k `(ex e (pr Rec e 0 2 0 ,x)) (U 'KRecAdd (ids 5))))
  (define res
    (ex-e k ra
      (lambda (k2 a)
        (define hl (have k2 `(pr Rec ,a 0 2 0 ,x)))
        (define-values (fnc tot rng zer stp) (rec-parts k2 hl a 0 2 0 x))
        (define z1 (have k2 `(pr App ,a 3 ,x) (all-e k2 zer 3)))
        (ex-i k2 (have k2 `(and (pr Rec ,a 0 2 0 ,x) (pr App ,a 3 ,x)) hl z1) a (Ad x 3 x)))))
  (define fin `(imp (in ,x 0) ,(Ad x 3 x)))
  (have (kctx) fin res)
  (end-thm! (ac `(imp ,CTX-DSL ,fin)) (ids 5)))

;; AddW: Ctx -> (Ad(x,y,z) -> z in w)          x = 4, y = 5, z = 6
(defkey KAddW (key)
  (begin-thm! key 7)
  (define-values (x y z) (values 4 5 6))
  (define k (cx+ (kctx) (Ad x y z)))
  (define res
    (ex-e k (have k (Ad x y z))
      (lambda (k2 a)
        (define hl (have k2 `(pr Rec ,a 0 2 0 ,x)))
        (define-values (fnc tot rng zer stp) (rec-parts k2 hl a 0 2 0 x))
        (have k2 `(in ,z 0) (all-e k2 rng y z)))))
  (define fin `(imp ,(Ad x y z) (in ,z 0)))
  (have (kctx) fin res)
  (end-thm! (ac `(imp ,CTX-DSL ,fin)) (ids 7)))

;; AddS: Ctx -> (y in w -> Ad(x,y,z) -> Suc(y1,y) -> Suc(z1,z) -> Ad(x,y1,z1))    x=4 y=5 z=6 y1=7 z1=8
(defkey KAddS (key)
  (begin-thm! key 9)
  (define-values (x y z y1 z1) (values 4 5 6 7 8))
  (define k (cx+ (kctx) `(in ,y 0) (Ad x y z) `(pr Suc ,y1 ,y) `(pr Suc ,z1 ,z)))
  (define res
    (ex-e k (have k (Ad x y z))
      (lambda (k2 a)
        (define hl (have k2 `(pr Rec ,a 0 2 0 ,x)))
        (define-values (fnc tot rng zer stp) (rec-parts k2 hl a 0 2 0 x))
        (define zw (have k2 `(in ,z 0) (all-e k2 rng y z)))
        (define z1w (sucw k2 z z1 zw))
        (define ga (gapp k2 z z1 zw z1w))
        (define s1 (have k2 `(pr App ,a ,y1 ,z1) (all-e k2 stp y z y1 z1) ga))
        (ex-i k2 (have k2 `(and (pr Rec ,a 0 2 0 ,x) (pr App ,a ,y1 ,z1)) hl s1) a (Ad x y1 z1)))))
  (define fin `(imp (in ,y 0) ,(Ad x y z) (pr Suc ,y1 ,y) (pr Suc ,z1 ,z) ,(Ad x y1 z1)))
  (have (kctx) fin res)
  (end-thm! (ac `(imp ,CTX-DSL ,fin)) (ids 9)))

;; lemma instances as facts in k: the lemma's antecedent hypotheses must be facts or context
(define (add-ex k x y . ls) (have k `(ex z (and (in z 0) ,(Ad x y 'z))) (U 'KAddEx (list 0 1 2 3 x y)) ls))
(define (add-uq k x y z u . ls) (have k `(eq ,z ,u) (U 'KAddUq (list 0 1 2 3 x y z u)) ls))
(define (add-z k x . ls) (have k (Ad x 3 x) (U 'KAddZ (list 0 1 2 3 x)) ls))
(define (add-w k x y z . ls) (have k `(in ,z 0) (U 'KAddW (list 0 1 2 3 x y z)) ls))
(define (add-s k x y z y1 z1 . ls) (have k (Ad x y1 z1) (U 'KAddS (list 0 1 2 3 x y z y1 z1)) ls))
(define (suc-ex k x) (U (rp 268) (list x)))                       ; exists s Suc(s,x)  (no hypotheses)
(define (suc-uq k a b c . ls) (have k `(eq ,a ,b) (use (rp 27) '() a b c) ls))   ; Suc(a,c) & Suc(b,c) -> a = b
(define (emp-uq k a b . ls) (have k `(eq ,a ,b) (use (rp 33) '() a b) ls))      ; Emp(a) & Emp(b) -> a = b

;; ------------------------------------------------------------------ induction
;; in context k (containing Ctx): forall y (y in w -> phi(y)).  phi: variable -> formula (ac language).
;; base: k -> fact phi(o) in k.   step: (k d t lphi) -> fact phi(t) in k, where k has d in w, Suc(t,d), lphi = phi(d).
(define (induct k phi base step)
  (define z (gs 'z)) (define s (gs 's)) (define yb (gs 'y))
  (define ax (Y (ac `(all ,z (ex ,s (all ,yb (iff (in ,yb ,s) (and (in ,yb ,z) ,(phi yb)))))))))
  (define sp (S ax '(0)))
  (define lbase (base k))
  (ex-e k sp
    (lambda (k2 s)
      (define sd (have k2 (last (cx-hyps k2))))
      (define i88 (use (rp 88) '() 0 s))
      (define-values (BASE STEP)
        (match (line i88)
          [(list 'I (list 'N (list 'I (list 'N (list 'I _ (list 'N b))) (list 'N st))) _) (values b st)]))
      ;; base: forall e (Emp(e) -> e in s)
      (define e (fresh!))
      (define k3 (cx+ k2 `(pr Emp ,e)))
      (define eq3 (emp-uq k3 e 3))
      (define phe (have k3 (phi e) lbase eq3 (leibF `(not ,(phi LHOLE)) e 3)))
      (define ew (zerow k3 e))
      (define es (have k3 `(in ,e ,s) (all-e k3 sd e) phe ew))
      (define bl (all-i k2 e (have k2 `(imp (pr Emp ,e) (in ,e ,s)) es)))
      (unless (equal? (concl k2 bl) BASE) (error 'induct "base shape ~a vs ~a" (show (concl k2 bl)) (show BASE)))
      ;; step: forall d forall t ((d in s & d in w) & Suc(t,d) -> t in s)
      (define d (fresh!)) (define t (fresh!))
      (define k4 (cx+ k2 `(in ,d ,s) `(in ,d 0) `(pr Suc ,t ,d)))
      (define phd (have k4 (phi d) (all-e k4 sd d)))
      (define pht (step k4 d t phd))
      (define tw (sucw k4 d t))
      (define ts (have k4 `(in ,t ,s) (all-e k4 sd t) pht tw))
      (define st1 (have k2 `(imp (and (in ,d ,s) (in ,d 0) (pr Suc ,t ,d)) (in ,t ,s)) ts))
      (define sl (all-i k2 d (all-i k2 t st1)))
      (unless (equal? (concl k2 sl) STEP) (error 'induct "step shape ~a vs ~a" (show (concl k2 sl)) (show STEP)))
      ;; Sub(w,s), then forall y (y in w -> phi(y))
      (define sub (have k2 `(pr Sub 0 ,s) i88 bl sl))
      (define subb (unf k2 'Sub (list 0 s) sub))
      (define y (fresh!))
      (define py (have k2 `(imp (in ,y 0) ,(phi y)) (all-e k2 subb y) (all-e k2 sd y)))
      (all-i k2 y py))))

;; ------------------------------------------------------------------ laws of addition
;; L0: Ctx -> forall y (y in w -> Ad(o,y,y))
(defkey KL0 (key)
  (begin-thm! key 4)
  (define k (kctx))
  (define phi (lambda (v) (Ad 3 v v)))
  (define r (induct k phi
                    (lambda (k) (add-z k 3 (zerow k 3)))
                    (lambda (k d t lphi) (add-s k 3 d d t t lphi))))
  (define yy (gs 'y))
  (end-thm! (ac `(imp ,CTX-DSL (all ,yy (imp (in ,yy 0) ,(phi yy))))) (ids 4)))

;; L1: Ctx -> forall y (y in w -> forall x z x1 z1 (x in w -> Ad(x,y,z) -> Suc(x1,x) -> Suc(z1,z) -> Ad(x1,y,z1)))
(define (L1-phi v)
  (define-values (x z x1 z1) (values (gs 'x) (gs 'z) (gs 'x) (gs 'z)))
  `(all ,x ,z ,x1 ,z1 (imp (in ,x 0) ,(Ad x v z) (pr Suc ,x1 ,x) (pr Suc ,z1 ,z) ,(Ad x1 v z1))))
(defkey KL1 (key)
  (begin-thm! key 4)
  (define k (kctx))
  ;; phi(y) proved for fresh x z x1 z1 in a context with the four hypotheses, then generalised
  (define (close k y body)          ; body: (k2 x z x1 z1) -> fact Ad(x1,y,z1) in k2 = k + hyps
    (define-values (x z x1 z1) (values (fresh!) (fresh!) (fresh!) (fresh!)))
    (define k2 (cx+ k `(in ,x 0) (Ad x y z) `(pr Suc ,x1 ,x) `(pr Suc ,z1 ,z)))
    (define r (body k2 x z x1 z1))
    (define f (have k `(imp (in ,x 0) ,(Ad x y z) (pr Suc ,x1 ,x) (pr Suc ,z1 ,z) ,(Ad x1 y z1)) r))
    (define g (all-i k x (all-i k z (all-i k x1 (all-i k z1 f)))))
    (have k (L1-phi y) g))
  (define r
    (induct k L1-phi
      (lambda (k)
        (close k 3
          (lambda (k2 x z x1 z1)
            (define ow (zerow k2 3))
            (define zx (add-uq k2 x 3 z x ow (add-z k2 x)))           ; z = x
            (define x1w (sucw k2 x x1))
            (define a1 (add-z k2 x1 x1w))                               ; Ad(x1,o,x1)
            (define sz (have k2 `(pr Suc ,z1 ,x) zx (leibF `(pr Suc ,z1 ,LHOLE) z x)))
            (define e1 (suc-uq k2 z1 x1 x sz))                          ; z1 = x1
            (have k2 (Ad x1 3 z1) a1 (eqsym k2 z1 x1 e1) (leibF `(not ,(Ad x1 3 LHOLE)) z1 x1)))))
      (lambda (k d t lphi)
        (close k t
          (lambda (k2 x z x1 z1)
            (define tw (sucw k2 d t))
            (ex-e k2 (add-ex k2 x d)
              (lambda (k3 z0)
                (ex-e k3 (suc-ex k3 z0)
                  (lambda (k4 s1)
                    (define a1 (add-s k4 x d z0 t s1))                  ; Ad(x,t,s1)
                    (define zs (add-uq k4 x t z s1 tw a1))              ; z = s1
                    (define ih (all-e k4 lphi x z0 x1 s1))
                    (define a2 (have k4 (Ad x1 d s1) ih))               ; Ad(x1,d,s1)
                    (ex-e k4 (suc-ex k4 s1)
                      (lambda (k5 s2)
                        (define a3 (add-s k5 x1 d s1 t s2 a2))          ; Ad(x1,t,s2)
                        (define sz (have k5 `(pr Suc ,z1 ,s1) zs (leibF `(pr Suc ,z1 ,LHOLE) z s1)))
                        (define e1 (suc-uq k5 z1 s2 s1 sz))             ; z1 = s2
                        (have k5 (Ad x1 t z1) a3 (eqsym k5 z1 s2 e1) (leibF `(not ,(Ad x1 t LHOLE)) z1 s2)))))))))))))
  (define yy (gs 'y))
  (end-thm! (ac `(imp ,CTX-DSL (all ,yy (imp (in ,yy 0) ,(L1-phi yy))))) (ids 4)))

;; ------------------------------------------------------------------ test
(module+ main
  (load-base!)
  (reset-batch!)
  (define keys (map string->symbol (vector->list (current-command-line-arguments))))
  (for ([kk keys]) (ensure! kk))
  (define text (batch-text))
  (define-values (rg ths) (read-jdg-text text))
  (printf "theorems ~a steps ~a; copy of the checker: ~a\n" (length ths) (for/sum ([t ths]) (length (caddr t))) (check-batch rg ths))
  (for ([kk keys]) (printf "~a: ~a\n" kk (show (reg-stmt (reg-index kk))))))
