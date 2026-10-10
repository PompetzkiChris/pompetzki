#lang racket/base
;; engine.rkt -- lane L6: proves translated statements about the natural numbers as ZF derivations over omega.
;; Untrusted: every line it makes is checked at once by zfcore.rkt's copy of the checker, and the files by both judges.
;;
;; Statement language (leanstmt.rkt): terms x | n | (S t) | (+ t u) | (* t u); formulas (= t u) (< t u) (<= t u)
;; (not F) (and F G) (or F G) (imp F G) (iff F G) (nall x F) (some x F).
;; Translation [F] into ZF: sigma1.rkt's tr (terms by continuation: a numeral n gives exists u (N_n(u) & K(u)),
;; t+s gives exists u (Add(a,b,u) & K(u)), < is membership, <= is membership or equality), and
;; (nall x F) gives forall x (Nat(x) -> [F]), (some x F) gives exists x (Nat(x) & [F]) as sigma1's some.
;;
;; A derivation: obtain w with Om(w) (K:OmEx); introduce the variables (Nat(x) gives x in w by H:NatW); give every
;; term a value in w (Tot lemmas, H:SucEx, H:EmpEx); prove the "star" form of the formula over the values with
;; earlier theorems as hints, congruence closure for equality, and case splits; bridge back to [F].
(require racket/list racket/string racket/match "zfcore.rkt" "zfbatch.rkt" "zfnat.rkt")
(provide (all-defined-out))

;; ======================================================================== translation (sigma1.rkt's tr, plus nall)
(define (num n x)
  (if (= n 0) `(pr Emp ,x)
      (let ([y (fresh-sym 'y)]) `(ex ,y (and ,(num (sub1 n) y) (pr Suc ,x ,y))))))
(define (op-f op a b u) (if (eq? op '+) (add-f a b u) (mul-f a b u)))
(define (wrap t r K)
  (match t
    [(? exact-nonnegative-integer? n) (let ([u (fresh-sym 'u)]) `(ex ,u (and ,(num n u) ,(K u))))]
    [(? symbol? x) (K (cdr (or (assq x r) (error 'wrap "unbound ~a" x))))]
    [(list 'S a) (wrap a r (lambda (va) (let ([u (fresh-sym 'u)]) `(ex ,u (and (pr Suc ,u ,va) ,(K u))))))]
    [(list (and op (or '+ '*)) a b)
     (wrap a r (lambda (va) (wrap b r (lambda (vb) (let ([u (fresh-sym 'u)]) `(ex ,u (and ,(op-f op va vb u) ,(K u))))))))]))
(define (rel-dsl rel a b) (case rel [(=) `(eq ,a ,b)] [(<) `(in ,a ,b)] [(<=) `(or (in ,a ,b) (eq ,a ,b))]))
(define (tr F r)
  (match F
    [(list (and rel (or '= '< '<=)) a b) (wrap a r (lambda (va) (wrap b r (lambda (vb) (rel-dsl rel va vb)))))]
    [(list 'not A) `(not ,(tr A r))]
    [(list (and op (or 'and 'or 'imp 'iff)) A B) `(,op ,(tr A r) ,(tr B r))]
    [(list 'nall x A) (let ([x2 (fresh-sym x)]) `(all ,x2 (imp (pr Nat ,x2) ,(tr A (cons (cons x x2) r)))))]
    [(list 'some x A) (let ([x2 (fresh-sym x)]) `(ex ,x2 (and (pr Nat ,x2) ,(tr A (cons (cons x x2) r)))))]))

;; ======================================================================== numerals (sigma1.rkt's NumEx, NumUq)
;; Chain(n) = Emp(v0) & Suc(v1,v0) & ... & Suc(vn,v(n-1)) over the frame variables 0..n
(define (chain n)
  (if (= n 0) '(pr Emp 0) `(and (pr Emp 0) ,@(for/list ([k (in-range 1 (add1 n))]) `(pr Suc ,k ,(sub1 k))))))
(define (tt goal . ls) (T (flatten ls) (c goal)))
(defgen NumEx (key)                      ; Chain(n) -> N_n(v_n)
  (define n (cadr key))
  (begin-thm! key (add1 n))
  (define g `(imp ,(chain n) ,(num n n)))
  (if (= n 0) (tt g)
      (tt g (U `(NumEx ,(sub1 n)) (ids n)) (E (sub1 n) (c `(imp (and ,(num (sub1 n) (sub1 n)) (pr Suc ,n ,(sub1 n))) ,(num n n))))))
  (end-thm! (c g) (ids (add1 n))))
(defgen NumUq (key)                      ; Chain(n) -> (N_n(p) -> p = v_n),  p = n+1
  (define n (cadr key))
  (define p (add1 n))
  (begin-thm! key (+ n 2))
  (define g `(imp ,(chain n) (imp ,(num n p) (eq ,p ,n))))
  (if (= n 0)
      (tt g (spec 'EmpUq (list p 0)))
      (let* ([q (fresh!)]
             [l3 (tt `(imp (and ,(num (sub1 n) q) (pr Suc ,p ,q)) (imp ,(chain n) (eq ,p ,n)))
                     (U `(NumUq ,(sub1 n)) (append (ids n) (list q))) (leib `(pr Suc ,p ,HOLE) q (sub1 n)) (spec 'SucUq (list p n (sub1 n))))]
             [l4 (L l3 q (c `(imp ,(num n p) (imp ,(chain n) (eq ,p ,n)))))])
        (tt g l4)))
  (end-thm! (c g) (ids (+ n 2))))

;; Suc(s,y) -> y in s   (s = 0, y = 1), as sigma1.rkt's SucIn
(defgen SucIn (key)
  (begin-thm! key 2)
  (define l0 (unfold 'Suc '(0 1)))
  (tt '(imp (pr Suc 0 1) (in 1 0)) l0 (inst (def-body l0) 1) (Y (Eqv 1 1)))
  (end-thm! (c '(imp (pr Suc 0 1) (in 1 0))) (ids 2)))
;; Suc(s,x) -> (d in s <-> d in x or d = x)   (s = 0, x = 1, d = 2)
(defgen SucMem (key)
  (begin-thm! key 3)
  (define l0 (unfold 'Suc '(0 1)))
  (define g '(imp (pr Suc 0 1) (iff (in 2 0) (or (in 2 1) (eq 2 1)))))
  (tt g l0 (inst (def-body l0) 2))
  (end-thm! (c g) (ids 3)))

;; ======================================================================== engine state (per derivation)
;; W: the frame variable with Om(W) in the context; OMLINE: ctx |- Om(W)
(define W #f) (define OMLINE #f)
(define vals (make-hash))                ; engine term -> value variable
(define inw (make-hash))                 ; value variable -> line ctx |- v in W
(define apps '())                        ; (list op (arg-values) value) for every evaluated compound term
(define zero-var #f)                     ; a value variable with Emp in the context, if any
(define (reset-engine!) (hash-clear! vals) (hash-clear! inw) (set! apps '()) (set! zero-var #f))

;; engine terms: symbols naming introduced variables, integers, (S t) (+ t u) (* t u)
(define (subterms t)
  (match t
    [(list 'S a) (append (subterms a) (list t))]
    [(list (or '+ '*) a b) (append (subterms a) (subterms b) (list t))]
    [(? exact-nonnegative-integer? n) (append (if (> n 0) (subterms (sub1 n)) '()) (list t))]
    [_ (list t)]))
(define (subst-term t s)
  (match t
    [(? symbol? x) (cond [(assq x s) => cdr] [else x])]
    [(list 'S a) (list 'S (subst-term a s))]
    [(list (and op (or '+ '*)) a b) (list op (subst-term a s) (subst-term b s))]
    [_ t]))
(define (form-terms F s)
  (match F
    [(list (or '= '< '<=) a b) (list (subst-term a s) (subst-term b s))]
    [(list 'not A) (form-terms A s)]
    [(list (or 'and 'or 'imp 'iff) A B) (append (form-terms A s) (form-terms B s))]
    [(list (or 'nall 'some) x A) (form-terms A (cons (cons x x) s))]))
(define (val t) (or (hash-ref vals t #f) (error 'val "no value for ~a" t)))

;; give every term in ts a value; k is called inside; goal: the formula proven (no value variables in it)
(define (with-values ts goal k)
  (define todo (remove-duplicates (append-map subterms ts)))
  (let loop ([todo todo])
    (cond
      [(null? todo) (k)]
      [(hash-ref vals (car todo) #f) (loop (cdr todo))]
      [else
       (define t (car todo))
       (define (obtain exf on-value)        ; exf: core existential with a ctx line; on-value: v -> void, registers
         (define v (fresh!))
         (exE (car exf) (ex-body (cdr exf)) v goal
              (lambda () (on-value v) (loop (cdr todo)))))
       (match t
         [0
          (cond
            [zero-var (hash-set! vals 0 zero-var) (loop (cdr todo))]
            [else
             (define el (U 'EmpEx (list W)))
             (define f (concl el))
             (obtain (cons (have f el OMLINE) f)
                     (lambda (v) (hash-set! vals 0 v) (set! zero-var v)
                       (hash-set! inw v (have (c `(in ,v ,W)) (spec 'ZeroW (list W v)) OMLINE))))])]
         [(? (lambda (t) (or (exact-positive-integer? t) (and (pair? t) (eq? (car t) 'S)))))
          (define av (val (if (pair? t) (cadr t) (sub1 t))))
          (define pre (for/first ([ap apps] #:when (and (eq? (car ap) 'S) (equal? (cadr ap) (list av)))) (caddr ap)))
          (cond
            [pre (hash-set! vals t pre) (loop (cdr todo))]
            [else
             (define sl (U 'SucEx (list av)))
             (obtain (cons sl (line sl))
                     (lambda (v) (hash-set! vals t v) (set! apps (cons (list 'S (list av) v) apps))
                       (hash-set! inw v (have (c `(in ,v ,W)) (spec 'SucW (list W av v)) OMLINE (hash-ref inw av)))))])]
         [(list (and op (or '+ '*)) a b)
          (define kind (if (eq? op '+) 'add 'mul))
          (define av (val a)) (define bv (val b))
          (define tf (c (let ([z (fresh-sym 'z)]) `(ex ,z (and (in ,z ,W) ,(fin-f kind av bv z))))))
          (define tl (have tf (U `(Tot ,kind) (list W av bv)) OMLINE (hash-ref inw av) (hash-ref inw bv)))
          (obtain (cons tl tf)
                  (lambda (v) (hash-set! vals t v) (set! apps (cons (list op (list av bv) v) apps))
                    (hash-set! inw v (hyp (c `(in ,v ,W))))))]
         [_ (error 'with-values "no value for term ~a" t)])])))

(define (r-of s) (for/list ([p s]) (cons (car p) (val (cdr p)))))     ; statement var -> value variable

;; ======================================================================== bridges: ctx |- [F] <-> F*
;; F* (star form): the same formula over value variables: (= t u) becomes (eq val(t) val(u)), etc.
(define (star F s)
  (match F
    [(list (and rel (or '= '< '<=)) a b) (rel-dsl rel (val (subst-term a s)) (val (subst-term b s)))]
    [(list 'not A) `(not ,(star A s))]
    [(list (and op (or 'and 'or 'imp 'iff)) A B) `(,op ,(star A s) ,(star B s))]))

;; uniqueness of the value of a compound term or numeral: line ctx |- R(..,p) -> p = v  (p a frame variable)
(define (uq-of t p)
  (match t
    [(list 'S a) (spec 'SucUq (list p (val t) (val a)))]
    [(list '+ a b) (uq-line 'add W (val a) (val b) p (val t))]
    [(list '* a b) (uq-line 'mul W (val a) (val b) p (val t))]
    [(? exact-nonnegative-integer? n) (U `(NumUq ,n) (append (for/list ([k (in-range (add1 n))]) (val k)) (list p)))]))
(define (rel-of t u)                     ; R(args, u) as dsl, for the value variables of the arguments
  (match t
    [(list 'S a) `(pr Suc ,u ,(val a))]
    [(list '+ a b) (add-f (val a) (val b) u)]
    [(list '* a b) (mul-f (val a) (val b) u)]
    [(? exact-nonnegative-integer? n) (num n u)]))
(define (exists-line t)                  ; ctx |- R(args, val t)
  (match t
    [(? exact-nonnegative-integer? n) (have (c (num n (val t))) (U `(NumEx ,n) (for/list ([k (in-range (add1 n))]) (val k))))]
    [_ (hyp-any (c (rel-of t (val t))))]))
(define (hyp-any f) (have f))            ; f is a conjunct of an assumption in ctx

;; ctx |- wrap(t, K) <-> K(val t);  K: value (frame variable or HOLE) -> dsl.  Returns a list of lines (empty: identical)
(define (bridge-term t s K)
  (define ts (subst-term t s))
  (match t
    [(? symbol?) '()]
    [_
     (define u (fresh-sym 'u))
     (define (Rk v) (rel-of ts v))
     ;; the innermost layer:  exists u (R(args,u) & K(u)) <-> K(val t)
     (define layer-f (c `(ex ,u (and ,(Rk u) ,(K u)))))
     (define vt (val ts))
     (define p (fresh!))
     (define l1 (have (c `(imp (and ,(Rk p) ,(K p)) ,(K vt))) (uq-of ts p) (leib (K HOLE) p vt) OMLINE
                      (for/list ([a (args-of ts)]) (hash-ref inw a))))
     (define R (lctx-of l1))
     (define l2 (T (list l1) (Imp (c `(and ,(Rk p) ,(K p))) (form-under R (c (K vt))))))
     (define l3 (L l2 p (Imp layer-f (form-under R (c (K vt))))))
     (define l4 (have (Qf layer-f (c (K vt))) l3 (exI vt (ex-body layer-f)) (exists-line ts)))
     ;; the outer layers: the arguments
     (match t
       [(? exact-nonnegative-integer?) (list l4)]
       [(list 'S a) (append (bridge-term a s (lambda (va) (let ([u2 (fresh-sym 'u)]) `(ex ,u2 (and (pr Suc ,u2 ,va) ,(K u2)))))) (list l4))]
       [(list (and op (or '+ '*)) a b)
        (define va (val (subst-term a s)))
        (append (bridge-term a s (lambda (x) (wrap b (r-of s) (lambda (vb) (let ([u2 (fresh-sym 'u)]) `(ex ,u2 (and ,(op-f op x vb u2) ,(K u2))))))))
                (bridge-term b s (lambda (y) (let ([u2 (fresh-sym 'u)]) `(ex ,u2 (and ,(op-f op va y u2) ,(K u2))))))
                (list l4))])]))
(define (args-of ts)
  (match ts [(list 'S a) (list (val a))] [(list (or '+ '*) a b) (list (val a) (val b))]
         [(? exact-nonnegative-integer? n) (for/list ([k (in-range (add1 n))]) (val k))] [_ '()]))

;; all bridge lines for the atoms of F
(define (bridges F s)
  (match F
    [(list (and rel (or '= '< '<=)) a b)
     (define vb (val (subst-term b s)))
     (append (bridge-term a s (lambda (va) (wrap b (r-of s) (lambda (y) (rel-dsl rel va y)))))
             (bridge-term b s (lambda (y) (rel-dsl rel (val (subst-term a s)) y))))]
    [(list 'not A) (bridges A s)]
    [(list (or 'and 'or 'imp 'iff) A B) (append (bridges A s) (bridges B s))]))

;; ======================================================================== equality: congruence closure with proofs
;; facts: lines whose conclusion (under ctx) is an atom or a conjunction of atoms
(define (conjuncts f)                    ; core formula -> list of core conjuncts
  (match f [(list 'N (list 'I a (list 'N b))) (append (conjuncts a) (conjuncts b))] [_ (list f)]))
(define (ctx-atoms) (append-map conjuncts CTX))

(struct edge (a b why idx))              ; why: (list 'line l) l proves ctx |- a = b ; (list 'cong ap1 ap2)
(define (closure eqs)                    ; eqs: list of (a b line); returns (values rep edges)
  (define edges '())
  (define n 0)
  (define (add-edge! a b why) (set! edges (cons (edge a b why n) edges)) (set! n (add1 n)))
  (for ([e eqs]) (add-edge! (car e) (cadr e) (list 'line (caddr e))))
  (define (classes)
    (define parent (make-hash))
    (define (find x) (let ([p (hash-ref parent x x)]) (if (equal? p x) x (let ([r (find p)]) (hash-set! parent x r) r))))
    (for ([e edges]) (let ([ra (find (edge-a e))] [rb (find (edge-b e))]) (unless (equal? ra rb) (hash-set! parent ra rb))))
    find)
  (let loop ()
    (define find (classes))
    (define added
      (for*/or ([p apps] [q apps]
                #:when (and (eq? (car p) (car q)) (not (equal? (caddr p) (caddr q)))
                            (not (equal? (find (caddr p)) (find (caddr q))))
                            (andmap (lambda (x y) (equal? (find x) (find y))) (cadr p) (cadr q))))
        (add-edge! (caddr p) (caddr q) (list 'cong p q))
        #t))
    (when added (loop)))
  (define find (classes))
  ;; representative: the smallest variable of the class
  (define members (make-hash))
  (for ([e edges]) (for ([x (list (edge-a e) (edge-b e))]) (hash-update! members (find x) (lambda (l) (if (memv x l) l (cons x l))) '())))
  (define (rep x) (let ([r (find x)]) (apply min (hash-ref members r (list x)))))
  (values rep (reverse edges)))

;; a line ctx |- a = b, explained from the edges with index below lim
(define (prove-eq a b edges [lim +inf.0])
  (cond
    [(equal? a b) (refl a)]
    [else
     (define usable (filter (lambda (e) (< (edge-idx e) lim)) edges))
     ;; BFS
     (define prev (make-hash (list (cons a #f))))
     (let bfs ([frontier (list a)])
       (unless (or (null? frontier) (hash-ref prev b #f))
         (bfs (for*/list ([x frontier] [e usable]
                          #:when (or (equal? (edge-a e) x) (equal? (edge-b e) x))
                          [y (in-value (if (equal? (edge-a e) x) (edge-b e) (edge-a e)))]
                          #:unless (hash-has-key? prev y))
                (hash-set! prev y (cons x e)) y))))
     (unless (hash-ref prev b #f) (error 'prove-eq "~a and ~a are not connected" a b))
     (define path (let walk ([y b] [acc '()]) (match (hash-ref prev y) [#f acc] [(cons x e) (walk x (cons (list x y e) acc))])))
     ;; each hop x -> y: a line ctx |- x = y; chained by Z:EqTr
     (for/fold ([cur #f]) ([h path])
       (match-define (list x y e) h)
       (define hl (edge-line e x y edges))
       (if cur (have (Eqv a y) cur hl (spec 'EqTr (list a x y))) hl))]))
(define (edge-line e x y edges)          ; ctx |- x = y for the edge e between x and y
  (define l
    (match (edge-why e)
      [(list 'line l) l]
      [(list 'cong p q) (cong-line p q edges (edge-idx e))]))
  (if (equal? (edge-a e) x) l (have (Eqv x y) l (spec 'EqSym (list y x)))))
(define (cong-line p q edges lim)        ; ctx |- val(p) = val(q)
  (match-define (list op as u) p)
  (match-define (list _ bs v) q)
  (define (Rf args z) (match op ['S `(pr Suc ,z ,(car args))] ['+ (add-f (car args) (cadr args) z)] ['* (mul-f (car args) (cadr args) z)]))
  (define eqls (for/list ([x as] [y bs] #:unless (equal? x y)) (prove-eq x y edges lim)))
  ;; R(as,u) -> R(bs,u) by Leibniz, argument by argument
  (define leibs
    (for/list ([k (in-range (length as))] #:unless (equal? (list-ref as k) (list-ref bs k)))
      (define pre (append (take bs k) (list HOLE) (drop as (add1 k))))
      (leib (Rf pre u) (list-ref as k) (list-ref bs k))))
  (define uq (match op ['S (spec 'SucUq (list u v (car bs)))]
               ['+ (uq-line 'add W (car bs) (cadr bs) u v)]
               ['* (uq-line 'mul W (car bs) (cadr bs) u v)]))
  (have (Eqv u v) eqls leibs uq OMLINE (for/list ([x bs]) (hash-ref inw x)) (hyp-any (c (Rf as u))) (hyp-any (c (Rf bs v)))))

;; canonical form: every E, Q, P atom over class representatives; equality atoms ordered (smaller variable first)
(define (canon f rep)
  (match f
    [(list 'E x y) (Mem (rep x) (rep y))]
    [(list 'Q x y) (let ([a (rep x)] [b (rep y)]) (Eqv (min a b) (max a b)))]
    [(list 'P p args) (Pr p (map rep args))]
    [(list 'N a) (Neg (canon a rep))]
    [(list 'I a b) (Imp (canon a rep) (canon b rep))]
    [_ f]))
(define (atoms-of-core f)
  (match f [(list 'N a) (atoms-of-core a)] [(list 'I a b) (append (atoms-of-core a) (atoms-of-core b))] [_ (list f)]))
(define (leibc core s t)                 ; Leibniz on a core formula with HOLE
  (define a (ren (absk HOLE) core))
  (Z a (Imp (Eqv s t) (Imp (ren (scons s sid) a) (ren (scons t sid) a)))))
;; lines ctx |- atom <-> canonical atom (as Leibniz instances and equality lines), for atoms that change
(define (canon-lines atoms rep edges)
  (define (moves args mk)              ; rewrite the arguments one by one; mk: args -> core atom
    (append*
     (for/list ([k (in-range (length args))] #:unless (equal? (list-ref args k) (rep (list-ref args k))))
       (define x (list-ref args k)) (define x2 (rep x))
       (define pre (append (map rep (take args k)) (list HOLE) (drop args (add1 k))))
       (list (prove-eq x x2 edges) (leibc (mk pre) x x2) (leibc (Neg (mk pre)) x x2)))))
  (append*
   (for/list ([a (remove-duplicates atoms)])
     (match a
       [(list 'E x y) (moves (list x y) (lambda (l) (Mem (car l) (cadr l))))]
       [(list 'P p args) (moves args (lambda (l) (Pr p l)))]
       [(list 'Q x y)
        (define x2 (rep x)) (define y2 (rep y))
        (cond
          [(equal? x2 y2) (list (prove-eq x y edges) (refl x2))]
          [else
           (append (moves (list x y) (lambda (l) (Eqv (car l) (cadr l))))
                   (if (> x2 y2) (list (spec 'EqSym (list x2 y2)) (spec 'EqSym (list y2 x2))) '()))])]
       [_ '()]))))

;; ======================================================================== the star prover
;; facts: list of lines (ctx |- fact); goal: core star formula. Returns a line ctx |- goal.
(define (eq-atoms-of fs) (filter (lambda (f) (match f [(list 'Q x y) (not (equal? x y))] [_ #f])) fs))
;; (values line rep): the line, or #f when the canonical form is not a tautology (then nothing is emitted)
(define (glue facts goal)
  (define fact-forms (map line* facts))
  (define eqatoms (remove-duplicates (eq-atoms-of (append (ctx-atoms) (append-map conjuncts fact-forms)))))
  (define-values (rep edges) (closure (for/list ([q eqatoms]) (match q [(list 'Q x y) (list x y q)]))))
  (define ug (under goal))
  (define prem-forms (map line facts))
  (define all-atoms (remove-duplicates (append (atoms-of-core ug) (append-map atoms-of-core prem-forms))))
  (define reps (remove-duplicates (for*/list ([a all-atoms] #:when (memq (car a) '(E Q P))
                                              [x (match a [(list 'P _ args) args] [(list _ x y) (list x y)])])
                                    (rep x))))
  (define check (foldr Imp (canon ug rep) (append (map (lambda (f) (canon f rep)) prem-forms) (map (lambda (r) (Eqv r r)) reps))))
  (cond
    [(tautchk2 check)
     ;; emit: the equality lines behind the edges, the canonical-form lines, then the tautology
     (define lines-of (make-hash))
     (define edges2 (for/list ([e edges])
                      (match (edge-why e)
                        [(list 'line q) (struct-copy edge e [why (list 'line (hash-ref! lines-of q (lambda () (have q facts))))])]
                        [_ e])))
     (define cl (canon-lines (filter (lambda (a) (memq (car a) '(E Q P))) all-atoms) rep edges2))
     (values (have goal facts cl) rep)]
    [else (values #f rep)]))

(define (prove-star goal facts [depth 0] [tried '()])
  (match goal
    [(list 'N (list 'I (list 'I a b) (list 'N (list 'I b2 a2)))) #:when (and (equal? a a2) (equal? b b2))   ; iff
     (define l1 (prove-star (Imp a b) facts depth tried))
     (define l2 (prove-star (Imp b a) facts depth tried))
     (have goal l1 l2)]
    [(list 'N (list 'I a (list 'N b)))                                                                     ; and
     (have goal (prove-star a facts depth tried) (prove-star b facts depth tried))]
    [(list 'I a b) #:when (not (match a [(list 'N _) #t] [_ #f]))                                          ; imp
     (intro a b (lambda () (prove-star b (cons (hyp a) facts) depth tried)))]
    [(list 'N (and a (list 'Q x y))) #:when (and (not (equal? x y)) (not (member a CTX)))                 ; not x = y
     (have goal (intro a goal (lambda () (prove-star goal (cons (hyp a) facts) depth tried))))]
    [_
     (define-values (l rep) (glue facts goal))
     (or l
         (let* ([atoms (append (append-map atoms-of-core (map conjuncts CTX)) (append-map atoms-of-core (map line* facts)) (atoms-of-core goal))]
                [cands (filter (lambda (q) (and (not (member q tried)) (not (equal? (rep (cadr q)) (rep (caddr q))))))
                               (remove-duplicates (eq-atoms-of atoms)))])
           (cond
             [(or (null? cands) (> depth 3)) (fail-star goal facts)]
             [else
              (define a (car cands))
              (define b1 (intro a goal (lambda () (prove-star goal (cons (hyp a) facts) (add1 depth) (cons a tried)))))
              (define b2 (intro (Neg a) goal (lambda () (prove-star goal (cons (hyp (Neg a)) facts) (add1 depth) (cons a tried)))))
              (have goal b1 b2)])))]))
(define (fail-star goal facts)
  (eprintf "STAR FAILED: goal ~a\n" (show goal))
  (for ([f facts]) (eprintf "  fact: ~a\n" (show (line* f))))
  (for ([h CTX]) (eprintf "  ctx: ~a\n" (show h)))
  (error 'prove-star "no proof"))

;; ======================================================================== hints and statements
;; registered statements: name -> (list stmt vars) with stmt = (nall x1 (nall x2 ... body)) prenex, body quantifier-free
(define proven (make-hash))
(define (prenex-split F)                 ; (values vars body) when F is nall* over a quantifier-free body
  (let loop ([F F] [vs '()])
    (match F [(list 'nall x A) (loop A (cons x vs))] [_ (values (reverse vs) F)])))
(define (qf? F) (match F [(list (or 'nall 'some) _ _) #f] [(list 'not A) (qf? A)] [(list (or 'and 'or 'imp 'iff) A B) (and (qf? A) (qf? B))] [_ #t]))

;; a hint gives facts (lines ctx |- star) and needs terms evaluated.
;;   (thm NAME t ...)   an earlier theorem at the terms
;;   (ih t ...)         the induction hypothesis at the terms (only in an induction step)
;;   (zf KEY (arg ...) ) a ZF lemma instance by key, arguments: W or terms (their values)
(define current-ih #f)                   ; (list line-of-ctx-formula vars body s0)  in a step
(define (hint-terms h s)
  (match h
    [(list 'thm name ts ...) (define-values (vs body) (prenex-split (car (hash-ref proven name))))
                             (form-terms body (map cons vs (map (lambda (t) (subst-term t s)) ts)))]
    [(list 'ih ts ...) (match-define (list _ vs body s0) current-ih)
                       (form-terms body (append (map cons vs (map (lambda (t) (subst-term t s)) ts)) s0))]
    [(list (or 'zf 'zfs) key args) (for/list ([a args] #:unless (eq? a 'W)) (subst-term a s))]
    [(list 'releq key args term target) (append (for/list ([a args] #:unless (eq? a 'W)) (subst-term a s))
                                                (list (subst-term term s) (subst-term target s)))]))
(define (instantiate-chain f-line f ts)  ; f: forall x (Nat(x) -> ...) ; returns lines (V instances and Nat lines)
  (let loop ([f f] [ts ts] [acc '()])
    (cond
      [(null? ts) (reverse acc)]
      [else
       (define v (val (car ts)))
       (define vl (inst f v))
       (define g (match (line vl) [(list 'I _ g) g]))
       (define natl (have (c `(pr Nat ,v)) (spec 'NatW (list W v)) OMLINE (hash-ref inw v)))
       (loop (match g [(list 'I _ h) h]) (cdr ts) (list* natl vl acc))])))
(define (hint-facts h s)
  (match h
    [(list 'thm name ts ...)
     (match-define (list stmt _) (hash-ref proven name))
     (define-values (vs body) (prenex-split stmt))
     (define ts2 (map (lambda (t) (subst-term t s)) ts))
     (define u (U name '()))
     (define insts (instantiate-chain u (line u) ts2))
     (define s2 (map cons vs ts2))
     (define inst-f (c (tr body (r-of s2))))
     (define il (have inst-f u insts))
     (define bl (bridges body s2))
     (list (have (c (star body s2)) il bl))]
    [(list 'ih ts ...)
     (match-define (list ihl vs body s0) current-ih)
     (define ts2 (map (lambda (t) (subst-term t s)) ts))
     (define ihf (line* ihl))
     (define insts (instantiate-chain ihl ihf ts2))
     (define s2 (append (map cons vs ts2) s0))
     (define inst-f (c (tr body (r-of s2))))
     (define il (have inst-f ihl insts))
     (define bl (bridges body s2))
     (list (have (c (star body s2)) il bl))]
    [(list (and z (or 'zf 'zfs)) key args)
     (define sig (for/list ([a args]) (if (eq? a 'W) W (val (subst-term a s)))))
     (define u (if (eq? z 'zf) (U key sig) (spec key sig)))
     (cons (have (line u) u) (for/list ([v (remove-duplicates sig)] #:unless (equal? v W)) (hash-ref inw v)))]
    ;; a ZF lemma concluding R(args of term, val target): gives val(target) = val(term) by uniqueness
    [(list 'releq key args term target)
     (define sig (for/list ([a args]) (if (eq? a 'W) W (val (subst-term a s)))))
     (define u (U key sig))
     (define tm (subst-term term s)) (define tg (val (subst-term target s)))
     (define rl (have (concl u) u OMLINE (for/list ([v sig] #:unless (equal? v W)) (hash-ref inw v))))
     (list (have (Eqv tg (val tm)) rl (uq-of tm tg) OMLINE (for/list ([a (args-of tm)]) (hash-ref inw a)) (exists-line tm)))]))

;; ---- prove [F] under ctx for a quantifier-free F with env s (statement var -> engine term)
;; hyps: pending hypotheses (list (cons F s)) whose [F] are in ctx
(define (prove-qf F s hyps hints)
  (define goal (c (tr F (r-of* s))))
  (define terms (append (form-terms F s) (append-map (lambda (h) (form-terms (car h) (cdr h))) hyps)
                        (append-map (lambda (h) (hint-terms h s)) hints)))
  (with-values terms goal
    (lambda ()
      (define hyp-facts
        (for/list ([h hyps])
          (match-define (cons A sa) h)
          (have (c (star A sa)) (hyp (c (tr A (r-of sa)))) (bridges A sa))))
      (define hfacts (append-map (lambda (h) (hint-facts h s)) hints))
      (define st (prove-star (c (star F s)) (append hyp-facts hfacts)))
      (have goal st (bridges F s)))))
(define (r-of* s)                        ; before evaluation: variables only map to value variables already known
  (for/list ([p s]) (cons (car p) (or (hash-ref vals (cdr p) #f) (error 'r-of* "~a has no value yet" (cdr p))))))

;; ---- prove [F] under ctx for F with quantifiers in front of / inside implications
(define (prove-stmt F s hyps hints)
  (match F
    [(list 'nall x A)
     (define v (fresh!))
     (define xs (string->symbol (format "~a" x)))
     (define body-f (c `(imp (pr Nat ,v) ,(tr A (cons (cons x v) (r-of* s))))))
     (allI v body-f
           (lambda ()
             (intro (c `(pr Nat ,v)) (c (tr A (cons (cons x v) (r-of* s))))
                    (lambda ()
                      (hash-set! vals x v)
                      (hash-set! inw v (have (c `(in ,v ,W)) (spec 'NatW (list W v)) OMLINE))
                      (begin0 (prove-stmt A (cons (cons x x) s) hyps hints)
                              (hash-remove! vals x))))))]
    [(list 'imp A B) #:when (not (qf? B))
     (intro (c (tr A (r-of* s))) (c (tr B (r-of* s)))
            (lambda () (prove-stmt B s (cons (cons A s) hyps) hints)))]
    [_ (prove-qf F s hyps hints)]))

;; ---- a closed theorem: obtain w, prove, eliminate w
(define (with-omega goal thunk)
  (define ol (U 'OmEx '()))
  (define w (fresh!))
  (exE ol (ex-body (line ol)) w goal
       (lambda ()
         (set! W w)
         (set! OMLINE (hyp (c `(pr Om ,w))))
         (thunk))))

;; script: (auto hint ...) | (ind VAR (base hint ...) (step hint ...))
(define (prove-theorem! key F script)
  (reset-engine!)
  (begin-thm! key 0)
  (define goal (c (tr F '())))
  (define res
    (with-omega goal
      (lambda ()
        (match script
          [(list 'auto hints ...) (prove-stmt F '() '() hints)]
          [(list 'ind var (list 'base bh ...) (list 'step sh ...)) (prove-induction F var bh sh)]))))
  (end-thm! (line res) '())
  (hash-set! proven key (list F (let-values ([(vs b) (prenex-split F)]) vs))))

;; induction on VAR, a variable of the prenex prefix; the variables before it are introduced first
(define (prove-induction F var bh sh)
  (define-values (vs body) (prenex-split F))
  (define before (takef vs (lambda (x) (not (eq? x var)))))
  (define after (cdr (dropf vs (lambda (x) (not (eq? x var))))))
  (define (rebuild xs b) (foldr (lambda (x acc) (list 'nall x acc)) b xs))
  (define phiF (rebuild after body))                       ; the statement after VAR, VAR free
  (let intro-before ([xs before] [s '()])
    (cond
      [(pair? xs)
       (define x (car xs))
       (define v (fresh!))
       (define rest (rebuild (cdr xs) (list 'nall var phiF)))
       (define inner (c (tr rest (cons (cons x v) (r-of* s)))))
       (allI v (c `(imp (pr Nat ,v) (core ,inner)))
             (lambda ()
               (intro (c `(pr Nat ,v)) inner
                      (lambda ()
                        (hash-set! vals x v)
                        (hash-set! inw v (have (c `(in ,v ,W)) (spec 'NatW (list W v)) OMLINE))
                        (begin0 (intro-before (cdr xs) (cons (cons x x) s)) (hash-remove! vals x))))))]
      [else
       ;; ctx |- forall i (i in w -> phi(i)) by induct, then forall x (Nat(x) -> phi(x))
       (define r0 (r-of* s))
       (define (phi sym) (tr phiF (cons (cons var sym) r0)))
       (define saved-vals (hash-copy vals)) (define saved-inw (hash-copy inw)) (define saved-apps apps) (define saved-zero zero-var)
       (define (restore!) (set! vals (hash-copy saved-vals)) (set! inw (hash-copy saved-inw)) (set! apps saved-apps) (set! zero-var saved-zero))
       (define ind
         (induct W OMLINE phi
                 (lambda (e)
                   (restore!)
                   (hash-set! vals var e) (hash-set! vals 0 e) (set! zero-var e)
                   (hash-set! inw e (have (c `(in ,e ,W)) (spec 'ZeroW (list W e)) OMLINE))
                   (prove-stmt phiF (cons (cons var var) s) '() bh))
                 (lambda (y sv)
                   (restore!)
                   (hash-set! vals 'PRED y) (hash-set! vals var sv) (hash-set! vals (list 'S 'PRED) sv)
                   (hash-set! inw y (hyp (c `(in ,y ,W))))
                   (hash-set! inw sv (have (c `(in ,sv ,W)) (spec 'SucW (list W y sv)) OMLINE (hash-ref inw y)))
                   (set! apps (cons (list 'S (list y) sv) apps))
                   (set! current-ih (list (hyp (c (phi y))) after body (append (list (cons var 'PRED)) s)))
                   (begin0 (prove-stmt phiF (cons (cons var var) s) '() sh)
                           (set! current-ih #f)))))
       (restore!)
       (define x (fresh!))
       (define phx (c (phi x)))
       (allI x (c `(imp (pr Nat ,x) (core ,phx)))
             (lambda ()
               (have (c `(imp (pr Nat ,x) (core ,phx))) ind (inst (line* ind) x) (spec 'NatW (list W x)) OMLINE)))])))
(define (vals-set! h) (set! vals h))
