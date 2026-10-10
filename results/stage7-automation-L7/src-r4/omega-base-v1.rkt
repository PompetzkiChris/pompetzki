#lang racket/base
;; omega-base-v1.rkt -- lane L7, item 4: helpers and the basic lemmas for the general laws of omega.
(require "l7core-v1.rkt" racket/list racket/match)
(provide (all-defined-out))

;; ---- lemma instances
(define (rs name . args) (S (U (rp name) '()) args))   ; closed replay theorem, specialized
(define (ru name . sig) (U (rp name) sig))             ; replay theorem with free variables, renamed
(define (lu key . sig) (U (reg-index key) sig))         ; one of our lemmas, renamed
(define (need key build) (unless (have? key) (build)) key)

;; ---- formulas (DSL)
(define (Nat x) `(pr Nat ,x))
(define (Emp x) `(pr Emp ,x))
(define (Suc a b) `(pr Suc ,a ,b))
(define (Un g f p) (let ([b (fresh-sym 'b)]) `(all ,b (iff (in ,b ,g) (or (in ,b ,f) (eq ,b ,p))))))
(define (Dm f y) (let ([i (fresh-sym 'i)] [a (fresh-sym 'a)]) `(all ,i (all ,a (imp (pr App ,f ,i ,a) (or (in ,i ,y) (eq ,i ,y)))))))
(define (Op kind x y z) (fin-f kind x y z))
(define (Body kind f x y z) (fin-body kind f x y z))
(define (Cst kind x z z2) (if (eq? kind 'add) `(pr Suc ,z2 ,z) (add-f z x z2)))   ; the step: z2 = z+1, or z2 = z+x
(define (z0of kind x o) (if (eq? kind 'add) x o))                                   ; the value at 0

;; ---- quantifier tactics
;; strip n leading foralls of core f with fresh frame variables
(define (open-all f n)
  (let loop ([f f] [n n] [vs '()])
    (if (= n 0) (values (reverse vs) f)
        (match f [(list 'A b) (let ([v (fresh!)]) (loop (ren (scons v sid) b) (sub1 n) (cons v vs)))]))))
(define (close-all l vs) (for/fold ([l l]) ([v (reverse vs)]) (fa-i v l)))
;; hyp -> forall^n M: k gets the fresh variables and the opened matrix and returns the line hyp -> M
(define (prove-all F n k)
  (define-values (vs M) (open-all (if (string? F) F F) n))
  (close-all (k vs M) vs))
;; line exl: hyp -> exists x P(x) (or exists x P(x) alone); k gets a fresh v and the core P(v), returns a line P(v) -> (hyp -> G)
;; (or P(v) -> G); result: hyp -> G (or G)
(define (obtain exl k)
  (define ex (match (line exl) [(list 'I h e) e] [e e]))
  (define body (match ex [(list 'N (list 'A (list 'N b))) b]))
  (define v (fresh!))
  (define l1 (k v (ren (scons v sid) body)))
  (define l2 (ex-e v l1))
  (define goal (match (line l2) [(list 'I _ g) g]))
  (match (line exl)
    [(list 'I h e) #:when (match goal [(list 'I h2 _) (equal? h h2)] [_ #f]) (T (list exl l2) goal)]
    [_ (T (list exl l2) goal)]))
;; the core formula of a DSL formula
(define (cf x) (c x))

;; ======================================================================== basic lemmas
;; SngFun: Sng(f,p) & Opr(p,u,v) -> (App(f,i,a) <-> (u = i & v = a))                 f p u v i a = 0..5
(define (sngfun!)
  (need 'SngFun
   (lambda ()
    (lemma! 'SngFun 6
     (lambda ()
       (define-values (f p u v i a) (values 0 1 2 3 4 5))
       (define hyp `(and (pr Sng ,f ,p) (pr Opr ,p ,u ,v)))
       (define ua `(and (eq ,u ,i) (eq ,v ,a)))
       (define appd (unfold 'App (list f i a)))
       (define d (fresh!))
       (define l1 (T (list (rs "Z:SngMem" f p d) (leib `(pr Opr ,HOLE ,i ,a) d p) (rs "Z:Kur1" p u v i a) (rs "Z:Kur2" p u v i a))
                     (c `(imp (and (in ,d ,f) (pr Opr ,d ,i ,a)) (imp ,hyp ,ua)))))
       (define l2 (ex-e d l1))
       (define l3 (T (list (rs "Z:SngIn" f p) (leib `(pr Opr ,p ,HOLE ,v) u i) (leib `(pr Opr ,p ,i ,HOLE) v a) (rs "L:MemApp" f i a p))
                     (c `(imp ,hyp (imp ,ua (pr App ,f ,i ,a))))))
       (T (list appd l2 l3) (c `(imp ,hyp (iff (pr App ,f ,i ,a) ,ua)))))))))

;; UnFun: Un(g,f,p) & Opr(p,u,v) -> (App(g,i,a) <-> (App(f,i,a) or (u = i & v = a)))   g f p u v i a = 0..6
(define (unfun!)
  (need 'UnFun
   (lambda ()
    (lemma! 'UnFun 7
     (lambda ()
       (define-values (g f p u v i a) (values 0 1 2 3 4 5 6))
       (define hyp `(and ,(Un g f p) (pr Opr ,p ,u ,v)))
       (define hypc (c hyp))
       (define unc (c (Un g f p)))
       (define ua `(and (eq ,u ,i) (eq ,v ,a)))
       (define appg (unfold 'App (list g i a)))
       (define appf (unfold 'App (list f i a)))
       ;; ->
       (define d (fresh!))
       (define l1 (T (list (inst unc d) (rs "L:MemApp" f i a d) (leib `(pr Opr ,HOLE ,i ,a) d p) (rs "Z:Kur1" p u v i a) (rs "Z:Kur2" p u v i a))
                     (c `(imp (and (in ,d ,g) (pr Opr ,d ,i ,a)) (imp ,hyp (or (pr App ,f ,i ,a) ,ua))))))
       (define l2 (ex-e d l1))
       ;; <- from App(f,i,a)
       (define d2 (fresh!))
       (define l3 (T (list (inst unc d2) (rs "L:MemApp" g i a d2))
                     (c `(imp (and (in ,d2 ,f) (pr Opr ,d2 ,i ,a)) (imp ,hyp (pr App ,g ,i ,a))))))
       (define l4 (ex-e d2 l3))
       ;; <- from u = i & v = a
       (define l5 (T (list (inst unc p) (Y (Eqv p p)) (leib `(pr Opr ,p ,HOLE ,v) u i) (leib `(pr Opr ,p ,i ,HOLE) v a) (rs "L:MemApp" g i a p))
                     (c `(imp ,hyp (imp ,ua (pr App ,g ,i ,a))))))
       (T (list appg appf l2 l4 l5) (c `(imp ,hyp (iff (pr App ,g ,i ,a) (or (pr App ,f ,i ,a) ,ua))))))))))

;; NatZero: Emp(o) -> Nat(o)                                                              o = 0
(define (natzero!)
  (need 'NatZero
   (lambda ()
    (lemma! 'NatZero 1
     (lambda ()
       (define o 0)
       (define w (fresh!))
       (define l1 (T (list (rs "L:ZeroW" w o) (rs "H:NatW" w o)) (c `(imp (pr Om ,w) (imp (pr Emp ,o) (pr Nat ,o))))))
       (M (rs "K:OmEx") (ex-e w l1)))))))

;; NatTr: Nat(y) & k in m & m in y -> k in y                                             y k m = 0..2
(define (nattr!)
  (need 'NatTr
   (lambda ()
    (lemma! 'NatTr 3
     (lambda ()
       (define-values (y k m) (values 0 1 2))
       (define w (fresh!))
       (define l1 (T (list (rs "H:NatW" w y) (ru "H:NatOrd" w y) (ru "H:OrdTrans" y) (ru "H:TrE" y k m))
                     (c `(imp (pr Om ,w) (imp (and (pr Nat ,y) (in ,k ,m) (in ,m ,y)) (in ,k ,y))))))
       (M (rs "K:OmEx") (ex-e w l1)))))))

;; ======================================================================== induction over omega
;; phi: (lambda (n) DSL), parameters the frame variables 0..k-1.
;; Ind: (B & S) -> forall n (Nat n -> phi n),  B = forall o (Emp o -> phi o),
;;      S = forall n (Nat n -> (phi n -> forall m (Suc(m,n) -> phi m)))
(define (ind-B phi) (let ([o (fresh-sym 'o)]) `(all ,o (imp (pr Emp ,o) ,(phi o)))))
(define (ind-S phi) (let ([n (fresh-sym 'n)] [m (fresh-sym 'm)]) `(all ,n (imp (pr Nat ,n) (imp ,(phi n) (all ,m (imp (pr Suc ,m ,n) ,(phi m))))))))
(define (ind-C phi) (let ([n (fresh-sym 'n)]) `(all ,n (imp (pr Nat ,n) ,(phi n)))))
(define (ind! key k phi)
  (need key
   (lambda ()
    (lemma! key k
     (lambda ()
       (define n (fresh!)) (define w (fresh!)) (define h (fresh!))
       (define Bc (c (ind-B phi))) (define Sc (c (ind-S phi)))
       (define HhD (let ([d (fresh-sym 'd)]) `(all ,d (iff (in ,d ,h) (and (in ,d ,w) ,(phi d))))))
       (define Hh (c HhD))
       (define G `(and (pr Om ,w) ,HhD ,(ind-B phi) ,(ind-S phi)))
       (define Gc (c G))
       ;; IndLem's base premise
       (define e (fresh!))
       (define b1 (T (list (inst Bc e) (rs "L:ZeroW" w e) (inst Hh e)) (Imp Gc (c `(imp (pr Emp ,e) (in ,e ,h))))))
       (define base (fa-i e b1))
       ;; IndLem's step premise
       (define d6 (fresh!)) (define d7 (fresh!))
       (define allm (c (let ([m (fresh-sym 'm)]) `(all ,m (imp (pr Suc ,m ,d6) ,(phi m))))))
       (define s1 (T (list (inst Hh d6) (inst Hh d7) (rs "H:NatW" w d6) (inst Sc d6) (inst allm d7) (rs "L:SucW" w d6 d7))
                     (Imp Gc (c `(imp (and (in ,d6 ,h) (in ,d6 ,w) (pr Suc ,d7 ,d6)) (in ,d7 ,h))))))
       (define step (fa-i d6 (fa-i d7 s1)))
       (define sub (unfold 'Sub (list w h)))
       (define f1 (T (list base step (rs "L:IndLem" w h) sub (inst (def-body sub) n) (inst Hh n))
                     (Imp Gc (c `(imp (in ,n ,w) ,(phi n))))))
       (define BS `(and ,(ind-B phi) ,(ind-S phi)))
       (define Q `(imp (and (pr Om ,w) (in ,n ,w)) (imp ,BS ,(phi n))))
       (define f2 (T (list f1) (Imp Hh (c Q))))
       (define f3 (ex-e h f2))
       (define sep (Y (c (let ([a (fresh-sym 'a)] [hh (fresh-sym 'h)] [dd (fresh-sym 'd)])
                           `(all ,a (ex ,hh (all ,dd (iff (in ,dd ,hh) (and (in ,dd ,a) ,(phi dd))))))))))
       (define f4 (T (list (fa-e sep w) f3) (c Q)))
       (define f5 (ex-e w f4))
       (define f6 (T (list (unfold 'Nat (list n)) f5) (c `(imp ,BS (imp (pr Nat ,n) ,(phi n))))))
       (fa-i n f6))))))
;; the instance line of an induction: (B & S) -> forall n (Nat n -> phi n), parameters renamed to sig
(define (ind-line key sig) (U key sig))
