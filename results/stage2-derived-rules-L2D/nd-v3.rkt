#lang racket/base
;; nd-v3.rkt (nd-v2.rkt with LHOLE, which v2 dropped by mistake; v2 = v1 with compiled formulas shifted under binders) --
;; Not trusted; every step goes through core-v1's copy of the checker as it is added, and the judges check the files.
;;
;; A context cx is a list of hypothesis formulas h1..hk; a fact in cx is a line  (h1 & ... & hk) -> phi
;; (left-nested conjunction; the bare phi when k = 0). Hypotheses should be atoms for the tautology test (predicate
;; atoms, memberships, equalities, quantified formulas), so T steps stay linear in k.
;;
;; ac: the formula language of core-v1's compile, with predicate names from the whole symbol table of Data.v
;; (or a predicate number), so Rec, Pr, CapS, Tot, Rng, ... can be written.
(require racket/list racket/match (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt"))
(provide (all-defined-out))

;; ---------------------------------------------------------------- formulas
(define PSYM (hash 'Sub 5 'Sng 6 'Upr 7 'Opr 8 'App 9 'Fnc 10 'Inj 11 'Tot 12 'Rng 13 'Le 14 'Tr 15 'Ord 16
                   'Emp 17 'Suc 18 'Ind 19 'Om 20 'Pr 28 'Rec 30 'CapS 38 'Nat 72))
(define (ac F [bound '()])
  (define (var a)
    (cond [(exact-integer? a) (+ a (length bound))]
          [(symbol? a) (or (index-of bound a) (error 'ac "unbound ~a in ~a" a F))]
          [else (error 'ac "bad variable ~a" a)]))
  (define (r G) (ac G bound))
  (match F
    [(list 'in a b) (Mem (var a) (var b))]
    [(list 'eq a b) (Eqv (var a) (var b))]
    [(list 'pr name args ...) (Pr (if (exact-integer? name) name (hash-ref PSYM name)) (map var args))]
    [(list 'not G) (Neg (r G))]
    [(list 'imp G H) (Imp (r G) (r H))]
    [(list 'imp G H K ...) (Imp (r G) (r `(imp ,H ,@K)))]
    [(list 'and G) (r G)]
    [(list 'and G H ... Lst) (Kf (r (cons 'and (cons G H))) (r Lst))]
    [(list 'or G) (r G)]
    [(list 'or G H ... Lst) (Df (r (cons 'or (cons G H))) (r Lst))]
    [(list 'iff G H) (Qf (r G) (r H))]
    [(list 'all x G) (All (ac G (cons x bound)))]
    [(list 'all x y z ... G) (All (ac `(all ,y ,@z ,G) (cons x bound)))]
    [(list 'ex x G) (Xf (ac G (cons x bound)))]
    [(list 'ex x y z ... G) (Xf (ac `(ex ,y ,@z ,G) (cons x bound)))]
    [(? pair?) #:when (memq (car F) (quote (I N A E Q P))) (if (null? bound) F (ren (lambda (n) (+ n (length bound))) F))]   ; an already compiled formula
    [_ (error 'ac "bad formula ~a" F)]))

(define (conj-of hs) (if (null? hs) #f (for/fold ([a (car hs)]) ([h (cdr hs)]) (Kf a h))))
(define (rhs-of f) (match f [(list 'I _ b) b]))
(define (lhs-of f) (match f [(list 'I a _) a]))

;; ---------------------------------------------------------------- contexts
(struct cx (hyps conj))
(define cx0 (cx '() #f))
(define (mkcx hs) (cx hs (conj-of hs)))
(define (cx+ k . hs) (mkcx (append (cx-hyps k) (map (lambda (h) (if (pair? h) (if (memq (car h) '(I N A E Q P)) h (ac h)) h)) hs))))
(define (under k f) (if (cx-conj k) (Imp (cx-conj k) f) f))
(define (F f) (if (and (pair? f) (memq (car f) '(I N A E Q P))) f (ac f)))
;; the conclusion of a fact line in context k
(define (concl k l) (if (cx-conj k) (rhs-of (line l)) (line l)))

;; have: a tautological consequence of the given lines, in context k
(define (have k f . ls) (T (flatten ls) (under k (F f))))
;; discharge the last hypothesis: fact in k+h  ==>  fact h -> phi in k
(define (discharge k h l) (T (list l) (under k (Imp (F h) (concl (cx+ k h) l)))))

;; forall-intro of the frame variable v (not free in the hypotheses)
(define (all-i k v l)
  (define phi (concl k l))
  (if (cx-conj k) (H v l (under k (All (ren (absk v) phi)))) (G l v)))
;; forall-elim: fact  forall x phi  ==>  phi[t]  (t frame variable); several in a row
(define (all-e k l . ts)
  (for/fold ([cur l]) ([t ts])
    (define f (concl k cur))
    (match f
      [(list 'A phi)
       (define inst (ren (scons t sid) phi))
       (define v (V t (Imp f inst)))
       (T (list cur v) (under k inst))]
      [_ (error 'all-e "not a universal: ~a" (show f))])))
;; exists-intro: fact phi[t] ==> exists x phi, X given as a formula (ex x phi)
(define (ex-i k l t X)
  (define Xc (F X))
  (match Xc
    [(list 'N (list 'A (list 'N psi)))
     (define e (E t (Imp (ren (scons t sid) psi) Xc)))
     (T (list l e) (under k Xc))]))
;; exists-elim: lex is a fact  exists x psi  in k;  body receives (k', v) with k' = k + psi[v], v fresh, and returns
;; a fact in k'; the result is that conclusion as a fact in k (v must not occur in it).
(define (ex-e k lex body)
  (define X (concl k lex))
  (match X
    [(list 'N (list 'A (list 'N psi)))
     (define v (fresh!))
     (define pv (ren (scons v sid) psi))
     (define k2 (cx+ k pv))
     (define l2 (body k2 v))
     (define phi (concl k2 l2))
     (define t1 (T (list l2) (Imp pv (under k phi))))
     (define t2 (L t1 v (Imp X (under k phi))))
     (T (list lex t2) (under k phi))]
    [_ (error 'ex-e "not an existential: ~a" (show X))]))
;; Leibniz: (s = t) -> (F[s] -> F[t]), F a formula (ac language) with the hole symbol 'HOLE
(define LHOLE 999998)   ; the hole of a Leibniz formula: a frame variable number never used
(define (leibF Fm s t)
  (define a (ren (absk LHOLE) (F Fm)))
  (Z a (Imp (Eqv s t) (Imp (ren (scons s sid) a) (ren (scons t sid) a)))))
;; a lemma or registry entry with its free variables renamed: U r sig, then specialisations of leading foralls
(define (use r sig . ts) (let ([u (U r sig)]) (if (null? ts) u (S u ts))))
;; a definition: Pred(args) <-> body
(define (defn p args) (S (U (hash-ref def-entry (if (exact-integer? p) p (hash-ref PSYM p))) '()) args))
(define (def-rhs l) (match (line l) [(list 'N (list 'I (list 'I _ f) _)) f]))
