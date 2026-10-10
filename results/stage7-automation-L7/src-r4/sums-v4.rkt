#lang racket/base
;; sums-v4.rkt -- lane L7 round 2: chains of Add over lists of natural numbers, as generic lemmas with free variables.
;; Ch([], s) = Emp(s); Ch([x], s) = (s = x); Ch(X ++ [x], s) = exists p (Ch(X,p) & Add(p,x,s)).
;; Lemma families (atoms are the free variables 0..k-1 of each lemma; a use renames them, repeats allowed):
;;   (ChNat k)       Nat x1..xk & Ch(X,s) -> Nat s
;;   (ChUq k)        Nat x1..xk & Ch(X,s) & Ch(X,s2) -> s = s2
;;   (ChZero k)      Nat x1..xk & Ch(X,s) & Emp(s) -> Emp(x1)
;;   (Ins k p)       Nat x1..xk & Nat t & Ch(X,s) & Add(s,t,c) -> Ch(X with t inserted at position p, c)
;;   (App k1 k2)     Nat x.. & Nat z.. & Ch(X,a) & Ch(Z,b) & Add(a,b,c) -> Ch(X ++ Z, c)
;;   (Split k1 k2)   Nat x.. & Nat z.. & Ch(X ++ Z, c) -> exists a b (Ch(X,a) & Ch(Z,b) & Add(a,b,c))
(require "l7core-v1.rkt" "omega-base-v1.rkt" "omega-kind-v5.rkt" "omega-laws-v3.rkt" "order2-v4.rkt" racket/list racket/match)
(provide (all-defined-out))

(define (Ch lst s)
  (cond [(null? lst) `(pr Emp ,s)]
        [(null? (cdr lst)) `(eq ,s ,(car lst))]
        [else (let ([p (fresh-sym 'p)]) `(ex ,p (and ,(Ch (drop-right lst 1) p) ,(Add p (last lst) s))))]))
(define (Nats lst) (for/list ([x (remove-duplicates lst)]) `(pr Nat ,x)))
(define (conj* ds) (cond [(null? ds) '(eq 0 0)] [(null? (cdr ds)) (car ds)] [else (cons 'and ds)]))
(define (ch-body lst s) (match (c (Ch lst s)) [(list 'N (list 'A (list 'N b))) b]))     ; the matrix under exists p
(define (insert-at lst p t) (append (take lst p) (list t) (drop lst p)))

;; ---- ChNat
(define (chnat! k)
  (define key `(ChNat ,k))
  (need key
   (lambda ()
    (when (> k 1) (chnat! (sub1 k)))
    (lemma! key (add1 k)
     (lambda ()
       (define xs (range k)) (define s k)
       (define H (c (conj* (append (Nats xs) (list (Ch xs s))))))
       (define goal (c `(pr Nat ,s)))
       (if (= k 1)
           (T (list (leib `(not (pr Nat ,HOLE)) s 0)) (Imp H goal))
           (obt H '() (c (Ch xs s))
             (lambda (p _ H1)
               (T (list (U (reg-index `(ChNat ,(sub1 k))) (append (range (sub1 k)) (list p))) (lu '(NatOp add) p (sub1 k) s))
                  (Imp H1 goal))))))))))
(define (chnat-line lst s) (chnat! (length lst)) (U (reg-index `(ChNat ,(length lst))) (append lst (list s))))

;; ---- ChUq
(define (chuq! k)
  (define key `(ChUq ,k))
  (need key
   (lambda ()
    (when (> k 1) (chuq! (sub1 k)) (chnat! (sub1 k)))
    (lemma! key (+ k 2)
     (lambda ()
       (define xs (range k)) (define s k) (define s2 (add1 k))
       (define H (c (conj* (append (Nats xs) (list (Ch xs s) (Ch xs s2))))))
       (define goal (c `(eq ,s ,s2)))
       (if (= k 1)
           (T (list (leib `(not (eq ,s ,HOLE)) s2 0)) (Imp H goal))
           (let ([xk (sub1 k)] [xs1 (range (sub1 k))])
             (obt H '() (c (Ch xs s))
               (lambda (p _1 H1)
                 (obt H1 '() (c (Ch xs s2))
                   (lambda (p2 _2 H2)
                     (T (list (U (reg-index `(ChUq ,(sub1 k))) (append xs1 (list p p2)))
                              (leib `(not ,(Add HOLE xk s2)) p p2) (lu '(Uq add) p xk s s2))
                        (Imp H2 goal)))))))))))))
(define (chuq-line lst s s2) (chuq! (length lst)) (U (reg-index `(ChUq ,(length lst))) (append lst (list s s2))))

;; ---- ChZero
(define (chzero! k)
  (define key `(ChZero ,k))
  (need key
   (lambda ()
    (zerosum!)
    (when (> k 1) (chzero! (sub1 k)) (chnat! (sub1 k)))
    (lemma! key (add1 k)
     (lambda ()
       (define xs (range k)) (define s k)
       (define H (c (conj* (append (Nats xs) (list (Ch xs s) `(pr Emp ,s))))))
       (define goal (c `(pr Emp 0)))
       (if (= k 1)
           (T (list (leib `(pr Emp ,HOLE) s 0)) (Imp H goal))
           (let ([xk (sub1 k)] [xs1 (range (sub1 k))])
             (obt H '() (c (Ch xs s))
               (lambda (p _ H1)
                 (T (list (U (reg-index `(ChNat ,(sub1 k))) (append xs1 (list p))) (lu 'ZeroSum p xk s)
                          (U (reg-index `(ChZero ,(sub1 k))) (append xs1 (list p))))
                    (Imp H1 goal)))))))))))
(define (chzero-line lst s) (chzero! (length lst)) (U (reg-index `(ChZero ,(length lst))) (append lst (list s))))

;; ---- Ins: free variables x1..xk = 0..k-1, t = k, s = k+1, c = k+2
(define (ins! k p)
  (define key `(Ins ,k ,p))
  (need key
   (lambda ()
    (base!) (rcomm!)
    (when (and (> k 1) (< p k)) (ins! (sub1 k) p) (chnat! (sub1 k)))
    (lemma! key (+ k 3)
     (lambda ()
       (define xs (range k)) (define t k) (define s (+ k 1)) (define cc (+ k 2))
       (define H (c (conj* (append (Nats xs) (list `(pr Nat ,t) (Ch xs s) (Add s t cc))))))
       (define target (insert-at xs p t))
       (define goal (c (Ch target cc)))
       (cond
         [(= p k)
          (T (list (ex-i s goal)) (Imp H goal))]
         [(= k 1)                                           ; p = 0: [x] -> [t, x]
          (T (list (leib (Add HOLE t cc) s 0) (lu 'AddComm 0 t cc) (Y (Eqv t t)) (ex-i t goal)) (Imp H goal))]
         [else
          (define xk (sub1 k)) (define xs1 (range (sub1 k)))
          (obt H '() (c (Ch xs s))
            (lambda (q0 _1 H1)
              (define natq0 (U (reg-index `(ChNat ,(sub1 k))) (append xs1 (list q0))))
              (obt H1 (list natq0 (tot-add q0 t)) (ex-add q0 t)
                (lambda (q _2 H2)
                  (obt H2 (list (lu '(NatOp add) q0 t q) (tot-add q xk)) (ex-add q xk)
                    (lambda (c2 _3 H3)
                      (T (list natq0 (lu 'RComm q0 xk t s cc q c2) (leib `(not ,(Add q xk HOLE)) cc c2)
                               (U (reg-index `(Ins ,(sub1 k) ,p)) (append xs1 (list t q0 q))) (ex-i q goal))
                         (Imp H3 goal))))))))]))))))
(define (ins-line lst p t s cc) (ins! (length lst) p) (U (reg-index `(Ins ,(length lst) ,p)) (append lst (list t s cc))))

;; (v4: Ins with k = 1 and App with k2 = 1 use Leibniz forward. sums-v1.rkt stopped in the middle of App; v2 = v1 up to Ins, then App and Split written out; v3 = v2 with one closing
;;  parenthesis fewer at the end of Split and the ChNat it needs for X ++ Z'.)

;; ---- App: free variables x1..xk1 = 0.., z1..zk2 = k1.., a, b, c
(define (app! k1 k2)
  (define key `(App ,k1 ,k2))
  (need key
   (lambda ()
    (base!) (assoceq!) (chnat! k1)
    (when (> k2 1) (app! k1 (sub1 k2)) (chnat! (sub1 k2)))
    (lemma! key (+ k1 k2 3)
     (lambda ()
       (define xs (range k1)) (define zs (range k1 (+ k1 k2)))
       (define a (+ k1 k2)) (define b (+ k1 k2 1)) (define cc (+ k1 k2 2))
       (define H (c (conj* (append (Nats (append xs zs)) (list (Ch xs a) (Ch zs b) (Add a b cc))))))
       (define goal (c (Ch (append xs zs) cc)))
       (cond
         [(= k2 1)
          (T (list (leib (Add a HOLE cc) b (car zs)) (ex-i a goal)) (Imp H goal))]
         [else
          (define z (last zs)) (define zs1 (drop-right zs 1))
          (define nata (U (reg-index `(ChNat ,k1)) (append xs (list a))))
          (obt H '() (c (Ch zs b))
            (lambda (q _1 H1)
              (define natq (U (reg-index `(ChNat ,(sub1 k2))) (append zs1 (list q))))
              (obt H1 (list nata natq (tot-add a q)) (ex-add a q)
                (lambda (e _2 H2)
                  (obt H2 (list (tot-add e z)) (ex-add e z)
                    (lambda (c2 _3 H3)
                      (T (list nata natq (U (reg-index `(App ,k1 ,(sub1 k2))) (append xs zs1 (list a q e)))
                               (lu 'AssocEq a q z e c2 b cc) (leib (Add e z HOLE) c2 cc) (ex-i e goal))
                         (Imp H3 goal))))))))]))))))
(define (app-line xs zs a b cc) (app! (length xs) (length zs)) (U (reg-index `(App ,(length xs) ,(length zs))) (append xs zs (list a b cc))))

;; ---- Split: free variables x1..xk1 = 0.., z1..zk2 = k1.., c
(define (split-goal xs zs cc)
  (define A (fresh-sym 'a)) (define B (fresh-sym 'b))
  `(ex ,A (ex ,B (and ,(Ch xs A) ,(Ch zs B) ,(Add A B cc)))))
(define (ex-body-at ex t) (match ex [(list 'N (list 'A (list 'N b))) (ren (scons t sid) b)]))
(define (split! k1 k2)
  (define key `(Split ,k1 ,k2))
  (need key
   (lambda ()
    (base!) (assoceq!) (chnat! k1)
    (when (> k2 1) (split! k1 (sub1 k2)) (chnat! (sub1 k2)) (chnat! (+ k1 (sub1 k2))))
    (lemma! key (+ k1 k2 1)
     (lambda ()
       (define xs (range k1)) (define zs (range k1 (+ k1 k2))) (define cc (+ k1 k2))
       (define H (c (conj* (append (Nats (append xs zs)) (list (Ch (append xs zs) cc))))))
       (define G (c (split-goal xs zs cc)))
       (define (intro a b body-lines Hx)
         (define G1 (ex-body-at G a))                       ; exists B (Ch(xs,a) & Ch(zs,B) & Add(a,B,c))
         (T (append body-lines (list (ex-i b G1) (ex-i a G))) (Imp Hx G)))
       (cond
         [(= k2 1)
          (define z (car zs))
          (obt H '() (c (Ch (append xs zs) cc))
            (lambda (p _1 H1) (intro p z (list (Y (Eqv z z))) H1)))]
         [else
          (define z (last zs)) (define zs1 (drop-right zs 1))
          (obt H '() (c (Ch (append xs zs) cc))
            (lambda (p _1 H1)
              (define sp (U (reg-index `(Split ,k1 ,(sub1 k2))) (append xs zs1 (list p))))
              (define G2 (c (split-goal xs zs1 p)))
              (define natp (U (reg-index `(ChNat ,(+ k1 (sub1 k2)))) (append xs zs1 (list p))))
              (obt H1 (list sp natp) G2
                (lambda (a Pa H2)
                  (obt H2 '() Pa
                    (lambda (b1 _2 H3)
                      (define nata (U (reg-index `(ChNat ,k1)) (append xs (list a))))
                      (define natb1 (U (reg-index `(ChNat ,(sub1 k2))) (append zs1 (list b1))))
                      (obt H3 (list natb1 (tot-add b1 z)) (ex-add b1 z)
                        (lambda (b _3 H4)
                          (obt H4 (list nata (tot-add a b)) (ex-add a b)
                            (lambda (c2 _4 H5)
                              (intro a b (list nata natb1 (lu 'AssocEq a b1 z p cc b c2) (leib `(not ,(Add a b HOLE)) cc c2)
                                               (ex-i b1 (c (Ch zs b))))
                                     H5)))))))))))]))))))
(define (split-line xs zs cc) (split! (length xs) (length zs)) (U (reg-index `(Split ,(length xs) ,(length zs))) (append xs zs (list cc))))
