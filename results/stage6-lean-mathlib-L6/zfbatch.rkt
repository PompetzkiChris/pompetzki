#lang racket/base
;; zfbatch.rkt -- lane L6: the batch under construction (registry of 677 entries from replay-all.jdg, the prelude copied
;; from Theorem 29's replay, theorems built step by step and checked as they are built with zfcore.rkt's copy of the
;; checker), and a natural-deduction layer on top of the eleven JDG1 steps. Most of the batch code follows sigma1.rkt
;; (Stage 2); the context layer (CTX, have, intro, allI, exE, induct) is new.
(require racket/list racket/string racket/match racket/file "zfcore.rkt")
(provide (all-defined-out))

;; ======================================================================== registry and batch
(define REPLAY "C:/ClaudeOutput/pompetzki/judge/replay-all.jdg")
(define GEN "C:/ClaudeOutput/pompetzki/forcing-src/general/")
(define NBASE 677)                       ; 7 axioms + 670 definitions; the 29 hypothesis entries are left out
(define RBASE 706)

(define reg (make-vector 400000 #f))     ; (cons statement-core hyps)
(define nreg 0)
(define base-lines '())
(define out-thms '())                    ; reversed: (list key text prelude? statement-core)
(define names (make-hash))               ; key -> registry index
(define stats (make-hash))
(define def-entry (make-hash))           ; predicate symbol -> registry index of its definition
(define replay-thms #f)
(define replay-index (make-hash))        ; replay name "L:IndLem" -> theorem index in replay-all.jdg

(define (reg-stmt r) (car (vector-ref reg r)))
(define (reg-index key) (or (hash-ref names key #f) (error 'reg "no theorem ~a" key)))
(define (bump! k [n 1]) (hash-update! stats k (lambda (v) (+ v n)) 0))

(define (load-base!)
  (define lines (file->lines REPLAY))
  (unless (equal? (string-trim (car lines)) "JDG1") (error 'load "header"))
  (unless (equal? (string-trim (cadr lines)) (format "R ~a" RBASE)) (error 'load "registry size"))
  (set! base-lines (map string-trim (take (drop lines 2) NBASE)))
  (define-values (rg ths) (read-jdg-text (file->string REPLAY)))
  (set! replay-thms (list->vector ths))
  (for ([e (take rg NBASE)] [i (in-naturals)])
    (unless (null? (cadr e)) (error 'load "entry ~a has hypotheses" i))
    (vector-set! reg i (cons (tof (car e)) '())))
  (set! nreg NBASE)
  (for ([i (in-range 7 NBASE)])
    (let loop ([f (reg-stmt i)] [k 0])
      (match f
        [(list 'A b) (loop b (add1 k))]
        [(list 'N (list 'I (list 'I (list 'P p args) _) _)) #:when (equal? args (reverse (range k))) (hash-set! def-entry p i)]
        [_ (error 'load "entry ~a is not a definition" i)])))
  ;; names of the replay theorems, from the comments of RpB0.v .. RpB10.v, in order
  (define nms
    (apply append
           (for/list ([i (in-range 11)])
             (for/list ([l (file->lines (format "~aRpB~a.v" GEN i))]
                        #:when (regexp-match? #px"^\\(\\* [A-Z]+:[A-Za-z0-9_']+ \\*\\) Thm" l))
               (cadr (regexp-match #px"^\\(\\* ([A-Z]+:[A-Za-z0-9_']+) \\*\\)" l))))))
  (unless (= (length nms) (vector-length replay-thms)) (error 'load "replay names ~a, theorems ~a" (length nms) (vector-length replay-thms)))
  (for ([n nms] [i (in-naturals)]) (unless (hash-ref replay-index n #f) (hash-set! replay-index n i))))

(define (reset-batch!)
  (for ([i (in-range NBASE nreg)]) (vector-set! reg i #f))
  (set! nreg NBASE)
  (set! out-thms '())
  (hash-clear! names) (hash-clear! stats) (hash-clear! prelude-map)
  (set! stack '()) (set! CTX '()))

(define (batch-text)
  (string-append "JDG1\nR " (number->string NBASE) "\n" (string-join base-lines "\n") "\n"
                 "T " (number->string (length out-thms)) "\n"
                 (string-join (map cadr (reverse out-thms)) "\n") "\n"))

;; ---- theorems under construction (a stack: a lemma needed inside a proof is built and appended first)
(struct thm (key [lines #:mutable] [n #:mutable] [steps #:mutable] [next #:mutable] ctx lctx))
(define stack '())
(define CTX '())                         ; the assumptions of the current derivation, oldest first
(define (set-ctx! v) (set! CTX v))
(define (cur) (if (null? stack) (error 'thm "no theorem open") (car stack)))
(define (begin-thm! key next-free)
  (set! stack (cons (thm key (make-vector 64 #f) 0 '() next-free CTX (make-hasheqv)) stack))
  (set! CTX '()))
(define (fresh!) (let* ([t (cur)] [v (thm-next t)]) (set-thm-next! t (add1 v)) v))
(define (line l) (let ([t (cur)]) (if (< l (thm-n t)) (vector-ref (thm-lines t) l) (error 'line "no line ~a" l))))

(define verbose-fail #t)
(define (add-step! st)
  (define t (cur))
  (define r (sstep reg nreg (thm-lines t) (thm-n t) st))
  (when (string? r)
    (when verbose-fail
      (eprintf "FAILED in ~a, step ~a: ~a\n" (thm-key t) (thm-n t) r)
      (match st
        [(list 'T ls g) (eprintf "  goal ~a\n" (show g)) (for ([l ls]) (eprintf "  premise ~a: ~a\n" l (show (line l))))]
        [(list (or 'E 'V 'Y) _ ... g) (eprintf "  ~a\n" (show g))]
        [(list (or 'L 'H) a b g) (eprintf "  ~a\n  line: ~a\n" (show g) (show (line (if (eq? (car st) 'L) a b))))]
        [(list 'M a b) (eprintf "  M ~a: ~a\n  M ~a: ~a\n" a (show (line a)) b (show (line b)))]
        [_ (eprintf "  ~a\n" st)]))
    (error 'step "~a" r))
  (when (eq? (car st) 'T) (bump! 'taut-calls taut-calls) (hash-update! stats 'taut-max (lambda (v) (max v taut-calls)) 0))
  (define n (thm-n t))
  (when (= n (vector-length (thm-lines t)))
    (let ([v (make-vector (* 2 n) #f)]) (vector-copy! v 0 (thm-lines t)) (set-thm-lines! t v)))
  (vector-set! (thm-lines t) n (car r))
  (set-thm-n! t (add1 n))
  (set-thm-steps! t (cons st (thm-steps t)))
  n)

(define (U r sig) (add-step! (list 'U (if (exact-integer? r) r (ensure! r)) sig)))
(define (S l ts) (add-step! (list 'S l ts)))
(define (G l k) (add-step! (list 'G l k)))
(define (M i j) (add-step! (list 'M i j)))
(define (T ls g) (add-step! (list 'T ls g)))
(define (E t g) (add-step! (list 'E t g)))
(define (L l k g) (add-step! (list 'L l k g)))
(define (H k l g) (add-step! (list 'H k l g)))
(define (V t g) (add-step! (list 'V t g)))
(define (Z a g) (add-step! (list 'Z a g)))
(define (Y g) (add-step! (list 'Y g)))

(define theorem-log '())                 ; (list key steps statement-core) in order, for the listings
(define (end-thm! stmt sig)
  (define t (cur))
  (define steps (reverse (thm-steps t)))
  (define r (check-thm reg nreg stmt sig steps '()))
  (unless (eq? r #t)
    (eprintf "FAILED theorem ~a: ~a\n  statement: ~a\n" (thm-key t) r (show (ren (sigf sig) stmt)))
    (when (> (thm-n t) 0) (eprintf "  last line: ~a\n" (show (vector-ref (thm-lines t) (sub1 (thm-n t))))))
    (error 'thm "~a" r))
  (set! stack (cdr stack))
  (set! CTX (thm-ctx t))
  (vector-set! reg nreg (cons stmt '()))
  (hash-set! names (thm-key t) nreg)
  (set! out-thms (cons (list (thm-key t) (thm-text (list (compress stmt) sig (map core-step->dform steps) '())) #f stmt) out-thms))
  (bump! 'theorems) (bump! 'steps (length steps))
  (set! nreg (add1 nreg))
  (sub1 nreg))

;; ---- the prelude: hypothesis-free theorems of the replay, copied with their dependencies and checked again here
(define prelude-map (make-hash))
(define (import-replay! idx)
  (unless (hash-ref prelude-map idx #f)
    (match-define (list st sig steps hyps) (vector-ref replay-thms idx))
    (unless (null? hyps) (error 'prelude "replay theorem ~a has hypotheses" idx))
    (for ([s steps])
      (match s
        [(list 'U r _) (cond [(>= r RBASE) (import-replay! (- r RBASE))]
                             [(>= r NBASE) (error 'prelude "replay theorem ~a uses hypothesis entry ~a" idx r)]
                             [else (void)])]
        [_ (void)]))
    (define steps2 (for/list ([s steps])
                     (match s [(list 'U r sg) (list 'U (if (>= r RBASE) (hash-ref prelude-map (- r RBASE)) r) sg)] [_ s])))
    (define stmt (tof st))
    (define r (check-thm reg nreg stmt sig (map step-tof steps2) '()))
    (unless (eq? r #t) (error 'prelude "replay theorem ~a fails here: ~a" idx r))
    (vector-set! reg nreg (cons stmt '()))
    (hash-set! prelude-map idx nreg)
    (set! out-thms (cons (list (list 'replay idx) (thm-text (list st sig steps2 '())) #t stmt) out-thms))
    (bump! 'prelude) (bump! 'prelude-steps (length steps2))
    (set! nreg (add1 nreg)))
  (hash-ref prelude-map idx))

;; replay theorems used here, by their names in the Rocq replay
(define PRELUDE
  '((EqSym "Z:EqSym") (EqTr "Z:EqTr") (OprEx "Z:OprEx") (Kur1 "Z:Kur1") (Kur2 "Z:Kur2") (FncApp "Z:FncApp")
    (RngApp "Z:RngApp") (TotApp "Z:TotApp") (NoSelf "L:NoSelf") (NoTwo "L:NoTwo") (SucUq "L:SucUq") (MemApp "L:MemApp")
    (EmpUq "L:EmpUq") (ZeroW "L:ZeroW") (SucW "L:SucW") (PrEx "L:PrEx") (IndLem "L:IndLem") (RecThm "L:RecThm")
    (PrMem "L:PrMem") (EmpNo "L:EmpNo") (OmTr "L:OmTr") (SucInj "L:SucInj") (SucNe "L:SucNe") (NatW "H:NatW")
    (OrdT3 "H:OrdT3") (OrdTr "H:OrdTr") (SucEx "H:SucEx") (SubE "H:SubE") (NatOrd "H:NatOrd") (OmOrd0 "H:OmOrd0")
    (EmpEx "H:EmpEx") (OmEx "K:OmEx")))

(define generators (make-hash))
(define (ensure! key)
  (cond
    [(hash-ref names key #f) => values]
    [(and (symbol? key) (assq key PRELUDE))
     => (lambda (p)
          (define idx (or (hash-ref replay-index (cadr p) #f) (error 'prelude "no replay theorem ~a" (cadr p))))
          (define r (import-replay! idx))
          (hash-set! names key r)
          r)]
    [else ((hash-ref generators (if (pair? key) (car key) key) (lambda () (error 'ensure "no generator for ~a" key))) key)
          (reg-index key)]))
(define-syntax-rule (defgen kind (key) body ...) (hash-set! generators 'kind (lambda (key) body ...)))

;; ======================================================================== named formulas (sigma1.rkt's compile)
(define SYM (hash 'Sub 5 'Sng 6 'Upr 7 'Opr 8 'App 9 'Fnc 10 'Dom 12 'Rng 13 'Tr 15 'Ord 16 'Emp 17 'Suc 18
                  'Om 20 'Prod 28 'RecG 30 'Nat 72))
(define gensym-counter 0)
(define (fresh-sym base) (set! gensym-counter (add1 gensym-counter)) (string->symbol (format "~a#~a" base gensym-counter)))
(define (compile F [bound '()])
  (define (var a)
    (cond [(exact-integer? a) (+ a (length bound))]
          [(symbol? a) (or (index-of bound a) (error 'compile "unbound ~a" a))]
          [else (error 'compile "bad variable ~a" a)]))
  (define (cc F) (compile F bound))
  (match F
    [(list 'in a b) (Mem (var a) (var b))]
    [(list 'eq a b) (Eqv (var a) (var b))]
    [(list 'pr name args ...) (Pr (hash-ref SYM name) (map var args))]
    [(list 'not G) (Neg (cc G))]
    [(list 'imp G H) (Imp (cc G) (cc H))]
    [(list 'and G) (cc G)]
    [(list 'and G H ... L) (Kf (cc (cons 'and (cons G H))) (cc L))]
    [(list 'or G) (cc G)]
    [(list 'or G H ... L) (Df (cc (cons 'or (cons G H))) (cc L))]
    [(list 'iff G H) (Qf (cc G) (cc H))]
    [(list 'all x G) (All (compile G (cons x bound)))]
    [(list 'ex x G) (Xf (compile G (cons x bound)))]
    [(list 'core f) (if (null? bound) f (ren (lambda (n) (+ n (length bound))) f))]))
(define (c x) (compile x))

;; ======================================================================== the context layer
;; A line "ctx |- f" is the formula  (h1 & ... & hn) -> f  (left-nested conjunction of the assumptions it needs, a
;; subsequence of CTX), or f when it needs none. lctx records that subsequence for every line made by have/allI.
(define (conj fs) (for/fold ([a (car fs)]) ([f (cdr fs)]) (Kf a f)))
(define (under f) (if (null? CTX) f (Imp (conj CTX) f)))
(define (form-under C f) (if (null? C) f (Imp (conj C) f)))
(define (lctx-of l) (hash-ref (thm-lctx (cur)) l '()))
(define (set-lctx! l C) (hash-set! (thm-lctx (cur)) l C))
(define (line* l) (let ([C (lctx-of l)] [f (line l)]) (if (null? C) f (match f [(list 'I _ g) g]))))   ; conclusion of a ctx line
(define (concl l) (match (line l) [(list 'I _ f) f] [f f]))                                         ; conclusion of an implication
(define (collect-atoms! f h)
  (match f [(list 'N a) (collect-atoms! a h)] [(list 'I a b) (collect-atoms! a h) (collect-atoms! b h)] [_ (hash-set! h f #t)]))
(define (overlaps? f h)
  (match f [(list 'N a) (overlaps? a h)] [(list 'I a b) (or (overlaps? a h) (overlaps? b h))] [_ (hash-ref h f #f)]))
;; ctx |- f by a tautology from the lines ls; the line keeps the assumptions that share an atom with f or with a
;; premise, plus those the premises carry (all of CTX if that is not enough)
(define (have f . ls)
  (define prem (flatten ls))
  (define C
    (cond
      [(null? CTX) '()]
      [else
       (define need (make-hash))
       (for ([l prem]) (for ([a (lctx-of l)]) (hash-set! need a #t)))
       (define seen (make-hash))
       (collect-atoms! f seen)
       (for ([l prem]) (collect-atoms! (line* l) seen))
       (define C1 (filter (lambda (a) (or (hash-ref need a #f) (overlaps? a seen))) CTX))
       (if (or (equal? C1 CTX) (tautchk2 (foldr Imp (form-under C1 f) (map line prem)))) C1 CTX)]))
  (define l (T prem (form-under C f)))
  (set-lctx! l C)
  l)
(define (hyp f) (have f))
(define (with-ctx* fs thunk)
  (define old CTX)
  (set! CTX (append old fs))
  (define r (thunk))
  (set! CTX old)
  r)
(define-syntax-rule (with-ctx (A ...) body ...) (with-ctx* (list A ...) (lambda () body ...)))

;; ctx |- A -> B, from thunk proving ctx,A |- B
(define (intro A B thunk) (have (Imp A B) (with-ctx (A) (thunk))))
;; ctx |- forall x B (x a frame variable free in B, not in ctx), from thunk proving ctx |- B
(define (allI x B thunk)
  (define l (thunk))
  (define C (lctx-of l))
  (if (null? C) (G l x) (let ([r (H x l (form-under C (All (ren (absk x) B))))]) (set-lctx! r C) r)))
;; ctx |- B from exline (ctx |- Xf a) and thunk proving ctx, P |- B with P = a[x], x fresh, not in B
(define (exE exline a x B thunk)
  (define P (ren (scons x sid) a))
  (define l1 (with-ctx (P) (thunk)))
  (define R (remove P (lctx-of l1)))
  (define l2 (T (list l1) (Imp P (form-under R B))))
  (define l3 (L l2 x (Imp (Xf a) (form-under R B))))
  (have B exline l3))
;; context-free lines
(define (exI t a) (E t (Imp (ren (scons t sid) a) (Xf a))))                 ; a[t] -> exists a
(define (inst f t) (match f [(list 'A phi) (V t (Imp f (ren (scons t sid) phi)))] [_ (error 'inst "not a universal: ~a" (show f))]))
(define (inst* f ts)
  (let loop ([f f] [ts ts] [acc '()])
    (if (null? ts) (reverse acc)
        (let ([l (inst f (car ts))]) (match (line l) [(list 'I _ g) (loop g (cdr ts) (cons l acc))])))))
(define (spec name args) (S (U name '()) args))
(define (use name sig) (U name sig))
(define (unfold sym args) (S (U (hash-ref def-entry (hash-ref SYM sym)) '()) args))
(define (def-body l) (match (line l) [(list 'N (list 'I (list 'I _ f) _)) f]))
(define HOLE 999999)
(define (leib F s t)
  (define a (ren (absk HOLE) (c F)))
  (Z a (Imp (Eqv s t) (Imp (ren (scons s sid) a) (ren (scons t sid) a)))))
(define (refl v) (Y (Eqv v v)))
(define (ex-body f) (match f [(list 'N (list 'A (list 'N a))) a] [_ (error 'ex-body "not an existential: ~a" (show f))]))

;; ======================================================================== induction over omega
;; ctx |- Om(w) by omline; phi: (lambda (sym) dsl) with frame variables as integers;
;; base: (lambda (e) line) proving ctx, Emp(e) |- phi(e);
;; step: (lambda (y s) line) proving ctx, y in w, phi(y), Suc(s,y) |- phi(s).
;; Result: ctx |- forall i (i in w -> phi(i)). Separation instance {x in w | phi(x)} and L:IndLem.
(define (induct w omline phi base step)
  (define x (fresh-sym 'x)) (define r (fresh-sym 'r)) (define z (fresh-sym 'z))
  (define sepF (c `(all ,z (ex ,r (all ,x (iff (in ,x ,r) (and (in ,x ,z) ,(phi x))))))))
  (define sl (Y sepF))
  (define sw (S sl (list w)))
  (define a (ex-body (line sw)))
  (define rv (fresh!))
  (define (phic v) (c (phi v)))
  (define iv (fresh!))
  (define goal (c (let ([i (fresh-sym 'i)]) `(all ,i (imp (in ,i ,w) ,(phi i))))))
  (exE sw a rv goal
       (lambda ()
         (define R (last CTX))
         (define Rl (hyp R))
         (define (Rat v) (inst R v))
         ;; forall e (Emp(e) -> e in r)
         (define e (fresh!))
         (define base1
           (allI e (c `(imp (pr Emp ,e) (in ,e ,rv)))
                 (lambda ()
                   (intro (c `(pr Emp ,e)) (c `(in ,e ,rv))
                          (lambda ()
                            (have (c `(in ,e ,rv)) Rl (Rat e) (spec 'ZeroW (list w e)) omline (base e)))))))
         ;; forall y s (((y in r & y in w) & Suc(s,y)) -> s in r)
         (define y (fresh!)) (define s (fresh!))
         (define stepb (c `(imp (and (in ,y ,rv) (in ,y ,w) (pr Suc ,s ,y)) (in ,s ,rv))))
         (define step1
           (allI y (All (ren (absk s) stepb))
                 (lambda ()
                   (allI s stepb
                         (lambda ()
                           (intro (c `(and (in ,y ,rv) (in ,y ,w) (pr Suc ,s ,y))) (c `(in ,s ,rv))
                                  (lambda ()
                                    (define py (have (phic y) Rl (Rat y)))
                                    (define ps (with-ctx ((c `(in ,y ,w)) (phic y) (c `(pr Suc ,s ,y))) (step y s)))
                                    (have (c `(in ,s ,rv)) Rl (Rat y) (Rat s) py ps omline (spec 'SucW (list w y s))))))))))
         (define il (spec 'IndLem (list w rv)))
         (define sub (have (c `(pr Sub ,w ,rv)) il omline base1 step1))
         (define sd (unfold 'Sub (list w rv)))
         (allI iv (c `(imp (in ,iv ,w) ,(phi iv)))
               (lambda ()
                 (have (c `(imp (in ,iv ,w) ,(phi iv))) sub sd (inst (def-body sd) iv) Rl (Rat iv)))))))

;; after a failed derivation: drop the theorems under construction (finished theorems stay in the batch)
(define (abort-all!) (set! stack '()) (set! CTX '()))
