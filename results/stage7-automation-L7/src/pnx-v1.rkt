#lang racket/base
;; pnx-v1.rkt -- lane L7, item 3: quantifier handling. Natural-deduction macros (forall-intro = fa-i / G, exists-elim = ex-e,
;; exists-intro = ex-i, forall-elim = V) used as lemma generators: for any formula f over the registered symbols, the
;; theorem f <-> pi(f), pi(f) a prenex form (no Skolem functions; existentials stay as not-forall-not).
;; Generators (each writes the lines of one equivalence; v is a fresh frame variable):
;;   all-cong     from B(v) <-> P(v):  forall B <-> forall P              (G, distribution axiom, M)
;;   ex-cong      from B(v) <-> P(v):  exists B <-> exists P
;;   neg-all      not forall B <-> exists not B,  neg-ex  not exists B <-> forall not B
;;   all-imp      (forall B -> R) <-> exists (B -> R)           ex-imp   (exists B -> R) <-> forall (B -> R)
;;   imp-all      (P -> forall C) <-> forall (P -> C)           imp-ex   (P -> exists C) <-> exists (P -> C)
;; with x not free in R, P (de Bruijn: R, P shifted under the new binder).
(require "l7core-v1.rkt" "omega-base-v1.rkt" racket/list racket/match)
(provide (all-defined-out))

(define (qfree? f) (match f [(list 'A _) #f] [(list 'N a) (qfree? a)] [(list 'I a b) (and (qfree? a) (qfree? b))] [_ #t]))
(define (body-of-ex f) (match f [(list 'N (list 'A (list 'N b))) b] [_ #f]))
(define (inst0 b v) (ren (scons v sid) b))           ; the body b of a binder, at the frame variable v
(define (abs0 f v) (ren (absk v) f))                 ; f with v bound (the body of a new binder)

;; ---- congruence under binders. Lb: line B(v) <-> P(v)
(define (all-cong v Lb)
  (match-define (list 'N (list 'I (list 'I Bv Pv) _)) (line Lb))
  (define g1 (G (T (list Lb) (Imp Bv Pv)) v))
  (define g2 (G (T (list Lb) (Imp Pv Bv)) v))
  (match-define (list 'A (list 'I B P)) (line g1))
  (define m1 (M g1 (Y (Imp (All (Imp B P)) (Imp (All B) (All P))))))
  (define m2 (M g2 (Y (Imp (All (Imp P B)) (Imp (All P) (All B))))))
  (T (list m1 m2) (Qf (All B) (All P))))
(define (ex-cong v Lb)
  (match-define (list 'N (list 'I (list 'I Bv Pv) _)) (line Lb))
  (define c (all-cong v (T (list Lb) (Qf (Neg Bv) (Neg Pv)))))
  (T (list c) (Qf (Xf (abs0 Bv v)) (Xf (abs0 Pv v)))))

;; ---- the prenex lemmas, B the body of the binder, v fresh
;; not forall B <-> exists not B
(define (neg-all B v)
  (define c (all-cong v (T '() (Qf (inst0 B v) (Neg (Neg (inst0 B v)))))))
  (T (list c) (Qf (Neg (All B)) (Xf (Neg B)))))
;; not exists B <-> forall not B
(define (neg-ex B) (T '() (Qf (Neg (Xf B)) (All (Neg B)))))
;; (forall B -> R) <-> exists (B -> R^)
(define (all-imp B R v)
  (define Bv (inst0 B v))
  (define EX (Xf (abs0 (Imp Bv R) v)))
  (define la (V v (Imp (All B) Bv)))
  (define lc (ex-e v (T (list la) (Imp (Imp Bv R) (Imp (All B) R)))))
  (define ld (V v (Imp (All (Neg (abs0 (Imp Bv R) v))) (Neg (Imp Bv R)))))
  (define lf (fa-i v (T (list ld) (Imp (Neg EX) Bv))))
  (define lg (T (list ld) (Imp (Neg EX) (Neg R))))
  (define lh (T (list lf lg) (Imp (Imp (All B) R) EX)))
  (T (list lc lh) (Qf (Imp (All B) R) EX)))
;; (exists B -> R) <-> forall (B -> R^)
(define (ex-imp B R v)
  (define Bv (inst0 B v))
  (define EB (Xf B))
  (define AL (All (abs0 (Imp Bv R) v)))
  (define lc (fa-i v (T (list (ex-i v EB)) (Imp (Imp EB R) (Imp Bv R)))))
  (define ld (V v (Imp AL (Imp Bv R))))
  (define lf (ex-e v (T (list ld) (Imp Bv (Imp AL R)))))
  (define lg (T (list lf) (Imp AL (Imp EB R))))
  (T (list lc lg) (Qf (Imp EB R) AL)))
;; (P -> forall C) <-> forall (P^ -> C)
(define (imp-all P C v)
  (define Cv (inst0 C v))
  (define AL (All (abs0 (Imp P Cv) v)))
  (define la (V v (Imp (All C) Cv)))
  (define lc (fa-i v (T (list la) (Imp (Imp P (All C)) (Imp P Cv)))))
  (define ld (V v (Imp AL (Imp P Cv))))
  (define lf (fa-i v (T (list ld) (Imp (Kf AL P) Cv))))
  (define lg (T (list lf) (Imp AL (Imp P (All C)))))
  (T (list lc lg) (Qf (Imp P (All C)) AL)))
;; (P -> exists C) <-> exists (P^ -> C)
(define (imp-ex P C v)
  (define Cv (inst0 C v))
  (define EC (Xf C))
  (define EX (Xf (abs0 (Imp P Cv) v)))
  (define lc (ex-e v (T (list (ex-i v EC)) (Imp (Imp P Cv) (Imp P EC)))))
  (define ld (V v (Imp (All (Neg (abs0 (Imp P Cv) v))) (Neg (Imp P Cv)))))
  (define lf (fa-i v (T (list ld) (Imp (Neg EX) (Neg Cv)))))
  (define lg (T (list ld) (Imp (Neg EX) P)))
  (define lh (T (list lf lg) (Imp (Imp P EC) EX)))
  (T (list lc lh) (Qf (Imp P EC) EX)))

;; ---- prenex conversion with proof: (values pi line), line: f <-> pi
(define (pnx f)
  (cond
    [(qfree? f) (values f (T '() (Qf f f)))]
    [else
     (match f
       [(list 'A b)
        (define v (fresh!))
        (define-values (pv lv) (pnx (inst0 b v)))
        (values (All (abs0 pv v)) (all-cong v lv))]
       [(list 'N a)
        (define-values (pa la) (pnx a))
        (define-values (p2 l2) (neg-push pa))
        (values p2 (T (list la l2) (Qf f p2)))]
       [(list 'I a b)
        (define-values (pa la) (pnx a))
        (define-values (pb lb) (pnx b))
        (define-values (p2 l2) (imp-pull pa pb))
        (values p2 (T (list la lb l2) (Qf f p2)))])]))
;; P prenex: (values pi line), line: not P <-> pi
(define (neg-push P)
  (cond
    [(qfree? P) (values (Neg P) (T '() (Qf (Neg P) (Neg P))))]
    [(body-of-ex P)
     => (lambda (B)
          (define v (fresh!))
          (define-values (qv lq) (neg-push (inst0 B v)))
          (define c (all-cong v lq))                       ; forall not B <-> forall Q
          (define pi (All (abs0 qv v)))
          (values pi (T (list c (neg-ex B)) (Qf (Neg P) pi))))]
    [else
     (match-define (list 'A B) P)
     (define v (fresh!))
     (define-values (qv lq) (neg-push (inst0 B v)))        ; not B(v) <-> Q(v)
     (define c (ex-cong v (T (list lq) (Qf (Neg (inst0 B v)) qv))))   ; exists not B <-> exists Q
     (define pi (Xf (abs0 qv v)))
     (values pi (T (list c (neg-all B (fresh!))) (Qf (Neg P) pi)))]))
;; P, R prenex: (values pi line), line: (P -> R) <-> pi
(define (imp-pull P R)
  (cond
    [(and (qfree? P) (qfree? R)) (values (Imp P R) (T '() (Qf (Imp P R) (Imp P R))))]
    [(not (qfree? P))
     (cond
       [(body-of-ex P)
        => (lambda (B)
             (define v (fresh!))
             (define-values (sv ls) (imp-pull (inst0 B v) R))
             (define c (all-cong v ls))
             (define pi (All (abs0 sv v)))
             (values pi (T (list c (ex-imp B R (fresh!))) (Qf (Imp P R) pi))))]
       [else
        (match-define (list 'A B) P)
        (define v (fresh!))
        (define-values (sv ls) (imp-pull (inst0 B v) R))
        (define c (ex-cong v ls))
        (define pi (Xf (abs0 sv v)))
        (values pi (T (list c (all-imp B R (fresh!))) (Qf (Imp P R) pi)))])]
    [(body-of-ex R)
     => (lambda (C)
          (define v (fresh!))
          (define-values (sv ls) (imp-pull P (inst0 C v)))
          (define c (ex-cong v ls))
          (define pi (Xf (abs0 sv v)))
          (values pi (T (list c (imp-ex P C (fresh!))) (Qf (Imp P R) pi))))]
    [else
     (match-define (list 'A C) R)
     (define v (fresh!))
     (define-values (sv ls) (imp-pull P (inst0 C v)))
     (define c (all-cong v ls))
     (define pi (All (abs0 sv v)))
     (values pi (T (list c (imp-all P C (fresh!))) (Qf (Imp P R) pi)))]))

(define (max-free f) (match f [(list (or 'E 'Q) x y) (max x y)] [(list 'P _ a) (apply max -1 a)] [(list 'N a) (max-free a)]
                       [(list 'I a b) (max (max-free a) (max-free b))] [(list 'A a) (sub1 (max-free a))]))
(define (prefix-length f) (match f [(list 'A b) (add1 (prefix-length b))]
                            [(list 'N (list 'A (list 'N b))) (add1 (prefix-length b))] [_ 0]))
;; the theorem f <-> pi(f); returns pi
(define (pnx-thm! key f)
  (define n (max 1 (add1 (max-free f))))
  (define pi #f)
  (lemma! key n (lambda () (define-values (p l) (pnx f)) (set! pi p) l))
  pi)
