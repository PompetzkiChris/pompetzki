#lang racket/base
;; sigma1.rkt -- Stage 2 of PMP-BUILDOUT-2026-10-09: ZF derivations, in the judge's format JDG1, of arithmetic facts
;; about omega: von Neumann numerals; k in n for k < n and its negation; n /= m; bounded quantifiers over numerals;
;; successor, addition and multiplication as defined relations; every true bounded sentence; true Sigma-1 sentences.
;;
;; Not trusted. Every file it writes is checked by the two judges (judge-v3.pmp under pompetzki.exe, and
;; racket/judge.rkt); it also checks each theorem as it builds it with its own copy of Replay2.v's step semantics.
;;
;; The registry of every file is the first 677 entries of replay-all.jdg (the 7 axioms and 670 definitions of
;; RpInit.v, AX0 ++ DEF0, none with hypotheses); RpInitOk.REG0_ok makes each entry derivable in Gam, so by
;; Replay3.check_batch_ok every accepted theorem T (hypotheses []) has prov Gam (tof T).
;;
;; Usage:
;;   racket sigma1.rkt emit DIR                 write the layer files, their mutants and DIR/manifest.txt
;;   racket sigma1.rkt judge DIR RESULTS        run both judges on DIR/*.jdg and DIR/mut/*.jdg, write RESULTS
;;   racket sigma1.rkt sentence "SEXP" OUT.jdg  one sentence: [s] when true, not [s] when false
;;   racket sigma1.rkt check-registry FILE      the registry of FILE against AX0 ++ DEF0 of RpInit.v
;; Sentence syntax: terms  n | x | (S t) | (+ t u) | (* t u)
;;                  formulas (= t u) (< t u) (<= t u) (not F) (and F ...) (or F ...) (imp F G) (iff F G)
;;                           (all x t F) (ex x t F) [x < t]  (alle x t F) (exe x t F) [x <= t]
;;                           (some x F) [x in omega, unbounded; only where true, the witness found by search]
;; Exact integers only.
(require racket/list racket/string racket/match racket/file racket/port file/sha1)

;; ======================================================================== formulas (Syn.v form)
;; (E x y) Mem, (Q x y) Eqv, (P p args) Pr, (N a) Neg, (I a b) Imp, (A a) All
(define (Mem x y) (list 'E x y))
(define (Eqv x y) (list 'Q x y))
(define (Pr p args) (list 'P p args))
(define (Neg a) (list 'N a))
(define (Imp a b) (list 'I a b))
(define (All a) (list 'A a))
(define (Kf a b) (Neg (Imp a (Neg b))))
(define (Df a b) (Imp (Neg a) b))
(define (Qf a b) (Kf (Imp a b) (Imp b a)))
(define (Xf a) (Neg (All (Neg a))))

(define (sid n) n)
(define ((up s) n) (if (= n 0) 0 (add1 (s (sub1 n)))))
(define ((scons y s) n) (if (= n 0) y (s (sub1 n))))
(define ((absk k) j) (if (= j k) 0 (add1 j)))
(define (sigf sig) (let ([v (list->vector sig)]) (lambda (i) (if (< i (vector-length v)) (vector-ref v i) 0))))

(define (ren s f)
  (match f
    [(list 'E x y) (list 'E (s x) (s y))]
    [(list 'Q x y) (list 'Q (s x) (s y))]
    [(list 'P p a) (list 'P p (map s a))]
    [(list 'N a) (list 'N (ren s a))]
    [(list 'I a b) (list 'I (ren s a) (ren s b))]
    [(list 'A a) (list 'A (ren (up s) a))]))

(define (free? n f)
  (match f
    [(list (or 'E 'Q) x y) (or (= x n) (= y n))]
    [(list 'P _ a) (and (memv n a) #t)]
    [(list 'N a) (free? n a)]
    [(list 'I a b) (or (free? n a) (free? n b))]
    [(list 'A a) (free? (add1 n) a)]))

(define (closedk? k f)
  (match f
    [(list (or 'E 'Q) x y) (and (< x k) (< y k))]
    [(list 'P _ a) (andmap (lambda (x) (< x k)) a)]
    [(list 'N a) (closedk? k a)]
    [(list 'I a b) (and (closedk? k a) (closedk? k b))]
    [(list 'A a) (closedk? (add1 k) a)]))

(define (form-size f)
  (match f
    [(list (or 'E 'Q 'P) _ _) 1]
    [(list 'N a) (add1 (form-size a))] [(list 'I a b) (+ 1 (form-size a) (form-size b))] [(list 'A a) (add1 (form-size a))]))

;; ---- dform (Replay2.v): (e x y) (q x y) (p P args) (n a) (i a b) (a a) (k a b) (d a b) (b a b) (x a)
(define (tof d)
  (match d
    [(list 'e x y) (Mem x y)]
    [(list 'q x y) (Eqv x y)]
    [(list 'p p a) (Pr p a)]
    [(list 'n a) (Neg (tof a))]
    [(list 'i a b) (Imp (tof a) (tof b))]
    [(list 'a a) (All (tof a))]
    [(list 'k a b) (Kf (tof a) (tof b))]
    [(list 'd a b) (Df (tof a) (tof b))]
    [(list 'b a b) (Qf (tof a) (tof b))]
    [(list 'x a) (Xf (tof a))]))

;; a dform whose tof is f, using the abbreviations K D Q X where they fit
(define (compress f)
  (match f
    [(list 'E x y) (list 'e x y)]
    [(list 'Q x y) (list 'q x y)]
    [(list 'P p a) (list 'p p a)]
    [(list 'N (list 'A (list 'N a))) (list 'x (compress a))]
    [(list 'N (list 'I (list 'I a b) (list 'N (list 'I b2 a2))))
     #:when (and (equal? a a2) (equal? b b2))
     (list 'b (compress a) (compress b))]
    [(list 'N (list 'I a (list 'N b))) (list 'k (compress a) (compress b))]
    [(list 'N a) (list 'n (compress a))]
    [(list 'I (list 'N a) b) (list 'd (compress a) (compress b))]
    [(list 'I a b) (list 'i (compress a) (compress b))]
    [(list 'A a) (list 'a (compress a))]))

(define (dform->tokens d acc)
  (match d
    [(list (and t (or 'e 'q)) x y) (list* y x t acc)]
    [(list 'p p a) (append (reverse a) (list (length a) p 'p) acc)]
    [(list (and t (or 'n 'a 'x)) a) (dform->tokens a (cons t acc))]
    [(list (and t (or 'i 'k 'd 'b)) a b) (dform->tokens b (dform->tokens a (cons t acc)))]))
(define (tokens->string rev-toks)
  (string-join (map (lambda (t) (if (symbol? t) (symbol->string t) (number->string t))) (reverse rev-toks)) " "))
(define (dtext d) (tokens->string (dform->tokens d '())))
(define (form->text f) (dtext (compress f)))

;; ---- readable statements (listings only)
(define PNAME (hash 5 "Sub" 6 "Sng" 7 "Upr" 8 "Opr" 9 "App" 10 "Fnc" 17 "Emp" 18 "Suc" 20 "Om" 72 "Nat"))
(define (show f [depth 0])
  (define (v x) (if (< x depth) (format "x~a" (- depth 1 x)) (format "v~a" (- x depth))))
  (match f
    [(list 'E x y) (format "~a∈~a" (v x) (v y))]
    [(list 'Q x y) (format "~a=~a" (v x) (v y))]
    [(list 'P p a) (format "~a(~a)" (hash-ref PNAME p (lambda () (format "P~a" p))) (string-join (map v a) ","))]
    [(list 'N (list 'A (list 'N a))) (format "∃x~a ~a" depth (show a (add1 depth)))]
    [(list 'N (list 'I (list 'I a b) (list 'N (list 'I b2 a2)))) #:when (and (equal? a a2) (equal? b b2))
     (format "(~a ↔ ~a)" (show a depth) (show b depth))]
    [(list 'N (list 'I a (list 'N b))) (format "(~a ∧ ~a)" (show a depth) (show b depth))]
    [(list 'N a) (format "¬~a" (show a depth))]
    [(list 'I (list 'N (list 'A (list 'N a))) b) (format "(~a → ~a)" (show (Xf a) depth) (show b depth))]
    [(list 'I (list 'N a) b) (format "(~a ∨ ~a)" (show a depth) (show b depth))]
    [(list 'I a b) (format "(~a → ~a)" (show a depth) (show b depth))]
    [(list 'A a) (format "∀x~a ~a" depth (show a (add1 depth)))]))

;; ======================================================================== tautologies (Replay.v, ReplayT.v)
(define taut-calls 0)
(define (atoms-of f)
  (define seen (make-hash))
  (define acc '())
  (let walk ([f f])
    (match f
      [(list 'N a) (walk a)]
      [(list 'I a b) (walk a) (walk b)]
      [_ (unless (hash-ref seen f #f) (hash-set! seen f (length acc)) (set! acc (cons f acc)))]))
  (values (reverse acc) seen))
(define (topf idx f)
  (match f
    [(list 'N a) (list 'BN (topf idx a))]
    [(list 'I a b) (list 'BI (topf idx a) (topf idx b))]
    [_ (list 'BV (hash-ref idx f))]))
(define (mkN a) (match a ['BT 'BF] ['BF 'BT] [(list 'BN x) x] [_ (list 'BN a)]))
(define (mkI a c)
  (cond [(eq? a 'BF) 'BT] [(eq? c 'BT) 'BT] [(eq? a 'BT) c] [(eq? c 'BF) (mkN a)] [else (list 'BI a c)]))
(define (tobf p)
  (match p
    [(list 'BV n) p]
    [(list 'BN q) (mkN (tobf q))]
    [(list 'BI q r) (mkI (tobf q) (tobf r))]))
(define (bsubst v c b)
  (match b
    [(list 'BV n) (if (= n v) (if c 'BT 'BF) b)]
    [(list 'BN a) (mkN (bsubst v c a))]
    [(list 'BI a d) (mkI (bsubst v c a) (bsubst v c d))]
    [_ b]))
(define (somevar b)
  (match b [(list 'BV n) n] [(list 'BN a) (somevar a)] [(list 'BI a d) (or (somevar a) (somevar d))] [_ #f]))
(define (taut-bf k b)
  (set! taut-calls (add1 taut-calls))
  (cond [(eq? b 'BT) #t]
        [(eq? b 'BF) #f]
        [else (let ([v (somevar b)])
                (and (> k 0) v (taut-bf (sub1 k) (bsubst v #t b)) (taut-bf (sub1 k) (bsubst v #f b))))]))
(define (tautchk2 f)
  (set! taut-calls 0)
  (define-values (atl idx) (atoms-of f))
  (taut-bf (length atl) (tobf (topf idx f))))

;; ======================================================================== axiom shapes, steps, check_thm (Replay2.v)
(define (skip1 n) (if (= n 0) 0 (add1 n)))
(define (ins2 n) (if (< n 2) n (add1 n)))
(define (unskip n) (if (< n 2) 0 (sub1 n)))
(define (SepF g) (All (Xf (All (Qf (Mem 0 1) (Kf (Mem 0 2) (ren skip1 g)))))))
(define (CollF g)
  (All (Imp (All (Imp (Mem 0 1) (Xf g))) (Xf (All (Imp (Mem 0 2) (Xf (Kf (Mem 0 2) (ren ins2 g)))))))))
(define (isSep g)
  (match g
    [(list 'A (list 'N (list 'A (list 'N (list 'A (list 'N (list 'I (list 'I _ (list 'N (list 'I _ (list 'N F)))) _)))))))
     (and (not (free? 1 F)) (equal? g (SepF (ren unskip F))))]
    [_ #f]))
(define (isColl g)
  (match g
    [(list 'A (list 'I (list 'A (list 'I _ (list 'N (list 'A (list 'N F))))) _)) (equal? g (CollF F))]
    [_ #f]))
(define (isSepN g) (or (isSep g) (match g [(list 'A h) (isSepN h)] [_ #f])))
(define (isCollN g) (or (isColl g) (match g [(list 'A h) (isCollN h)] [_ #f])))
(define (axshape g)
  (or (match g [(list 'I a (list 'I _ a2)) (equal? a a2)] [_ #f])
      (match g [(list 'I (list 'I a (list 'I b c)) (list 'I (list 'I a2 b2) (list 'I a3 c2)))
                (and (equal? a a2) (equal? a a3) (equal? b b2) (equal? c c2))] [_ #f])
      (match g [(list 'I (list 'I (list 'N a) (list 'N b)) (list 'I b2 a2)) (and (equal? a a2) (equal? b b2))] [_ #f])
      (match g [(list 'I (list 'A (list 'I a b)) (list 'I (list 'A a2) (list 'A b2))) (and (equal? a a2) (equal? b b2))] [_ #f])
      (match g [(list 'I a (list 'A b)) (equal? b (ren add1 a))] [_ #f])
      (match g [(list 'Q x y) (= x y)] [_ #f])
      (isSepN g) (isCollN g)))

(define (specn f ts)
  (cond [(null? ts) f]
        [else (match f [(list 'A b) (specn (ren (scons (car ts) sid) b) (cdr ts))] [_ #f])]))

;; reg: vector of (cons statement hyps); a step's formulas are cores. Returns (cons line hyps) or a string.
(define (sstep reg nreg lines nlines st)
  (define (line l) (and (< l nlines) (vector-ref lines l)))
  (match st
    [(list 'U r sig) (if (< r nreg) (let ([e (vector-ref reg r)]) (cons (ren (sigf sig) (car e)) (cdr e))) "use: no such entry")]
    [(list 'S l ts) (let ([F (line l)]) (cond [(not F) "spec: no line"] [(specn F ts) => (lambda (G) (cons G '()))] [else "spec: not enough A"]))]
    [(list 'G l k) (let ([F (line l)]) (if F (cons (All (ren (absk k) F)) '()) "gen: no line"))]
    [(list 'M i j)
     (let ([a (line i)] [b (line j)])
       (match b [(list 'I a2 c) #:when (and a (equal? a a2)) (cons c '())] [_ "mp: premise mismatch"]))]
    [(list 'T ls g)
     (let ([ps (map line ls)])
       (cond [(memv #f ps) "taut: no line"]
             [(tautchk2 (foldr Imp g ps)) (cons g '())]
             [else "taut: not a tautology"]))]
    [(list 'E t g)
     (match g
       [(list 'I F (list 'N (list 'A (list 'N f)))) #:when (equal? F (ren (scons t sid) f)) (cons g '())]
       [_ "exi: shape"])]
    [(list 'L l k g)
     (match* (g (line l))
       [((list 'I (list 'N (list 'A (list 'N P2))) G2) (list 'I P G3))
        (if (and (equal? G2 G3) (equal? P2 (ren (absk k) P)) (not (free? k G2))) (cons g '()) "exel: conditions")]
       [(_ _) "exel: shape"])]
    [(list 'H k l g)
     (match* (g (line l))
       [((list 'I H (list 'A f2)) (list 'I H2 f))
        (if (and (equal? H H2) (equal? f2 (ren (absk k) f)) (not (free? k H))) (cons g '()) "alli: conditions")]
       [(_ _) "alli: shape"])]
    [(list 'V t g)
     (match g [(list 'I (list 'A f) G2) #:when (equal? G2 (ren (scons t sid) f)) (cons g '())] [_ "inst: shape"])]
    [(list 'Z a g)
     (match g
       [(list 'I (list 'Q s t) (list 'I X Y)) #:when (and (equal? X (ren (scons s sid) a)) (equal? Y (ren (scons t sid) a))) (cons g '())]
       [_ "leib: shape"])]
    [(list 'Y g) (if (axshape g) (cons g '()) "ax: not an axiom shape")]))

(define (nodup? l) (= (length l) (length (remove-duplicates l))))
(define (check-thm reg nreg stmt sig steps hyps)
  (define lines (make-vector (max 1 (length steps)) #f))
  (let loop ([sts steps] [n 0] [hs '()])
    (cond
      [(null? sts)
       (cond [(= n 0) "no lines"]
             [(not (equal? (vector-ref lines (sub1 n)) (ren (sigf sig) stmt))) "final: last line is not the statement"]
             [(not (nodup? sig)) "final: sig repeats"]
             [(not (closedk? (length sig) stmt)) "final: statement not closed"]
             [(not (andmap (lambda (h) (memv h hyps)) hs)) "final: a hypothesis used is not claimed"]
             [else #t])]
      [else
       (define r (sstep reg nreg lines n (car sts)))
       (if (string? r)
           (format "step ~a: ~a" n r)
           (begin (vector-set! lines n (car r)) (loop (cdr sts) (add1 n) (append hs (cdr r)))))])))

;; ======================================================================== JDG1 reading and writing
(define (make-reader toks)
  (define p 0)
  (define (nx) (begin0 (vector-ref toks p) (set! p (add1 p))))
  (define (num) (let ([t (nx)]) (or (string->number t) (error 'jdg "number expected, got ~a" t))))
  (define (lst) (for/list ([i (in-range (num))]) (num)))
  (define (dform)
    (define t (nx))
    (case t
      [("e" "q") (let* ([x (num)] [y (num)]) (list (string->symbol t) x y))]
      [("p") (let* ([pp (num)] [a (lst)]) (list 'p pp a))]
      [("n" "a" "x") (list (string->symbol t) (dform))]
      [("i" "k" "d" "b") (let* ([a (dform)] [b (dform)]) (list (string->symbol t) a b))]
      [else (error 'jdg "form tag expected, got ~a" t)]))
  (define (step)
    (define t (nx))
    (case t
      [("U") (let* ([r (num)] [s (lst)]) (list 'U r s))]
      [("S") (let* ([l (num)] [s (lst)]) (list 'S l s))]
      [("G" "M") (let* ([a (num)] [b (num)]) (list (string->symbol t) a b))]
      [("T") (let* ([ls (lst)] [g (dform)]) (list 'T ls g))]
      [("E" "V") (let* ([a (num)] [g (dform)]) (list (string->symbol t) a g))]
      [("L" "H") (let* ([a (num)] [b (num)] [g (dform)]) (list (string->symbol t) a b g))]
      [("Z") (let* ([a (dform)] [g (dform)]) (list 'Z a g))]
      [("Y") (list 'Y (dform))]
      [else (error 'jdg "step tag expected, got ~a" t)]))
  (values nx num lst dform step))

;; (values registry theorems): registry entries (list dform hyps), theorems (list dform sig steps hyps), dforms kept
(define (read-jdg-text s)
  (define-values (nx num lst dform step) (make-reader (list->vector (string-split s))))
  (unless (equal? (nx) "JDG1") (error 'jdg "header"))
  (unless (equal? (nx) "R") (error 'jdg "R"))
  (define rg (for/list ([i (in-range (num))]) (let* ([f (dform)] [h (lst)]) (list f h))))
  (unless (equal? (nx) "T") (error 'jdg "T"))
  (define ths (for/list ([i (in-range (num))])
                (let* ([f (dform)] [sig (lst)] [n (num)] [sts (for/list ([j n]) (step))] [h (lst)]) (list f sig sts h))))
  (values rg ths))

(define (step-tof st)
  (match st
    [(list 'T ls g) (list 'T ls (tof g))]
    [(list (and t (or 'E 'V)) a g) (list t a (tof g))]
    [(list (and t (or 'L 'H)) a b g) (list t a b (tof g))]
    [(list 'Z a g) (list 'Z (tof a) (tof g))]
    [(list 'Y g) (list 'Y (tof g))]
    [_ st]))

;; the whole batch with the copy of the checker: (list 'ACCEPT reg0 theorems steps reg1) or (list 'REJECT i why)
(define (check-batch rg ths)
  (define reg (make-vector (+ (length rg) (length ths) 1) #f))
  (for ([e rg] [i (in-naturals)]) (vector-set! reg i (cons (tof (car e)) (cadr e))))
  (let loop ([ts ths] [n (length rg)] [i 0] [steps 0])
    (cond [(null? ts) (list 'ACCEPT (length rg) i steps n)]
          [else
           (match-define (list st sig sts hyps) (car ts))
           (define stmt (tof st))
           (define r (check-thm reg n stmt sig (map step-tof sts) hyps))
           (if (eq? r #t)
               (begin (vector-set! reg n (cons stmt hyps)) (loop (cdr ts) (add1 n) (add1 i) (+ steps (length sts))))
               (list 'REJECT i r))])))

(define (nlist l) (string-join (map number->string (cons (length l) l)) " "))
(define (dform-step->text st)
  (match st
    [(list 'U r sig) (format "U ~a ~a" r (nlist sig))]
    [(list 'S l ts) (format "S ~a ~a" l (nlist ts))]
    [(list (and t (or 'G 'M)) a b) (format "~a ~a ~a" t a b)]
    [(list 'T ls g) (format "T ~a ~a" (nlist ls) (dtext g))]
    [(list (and t (or 'E 'V)) a g) (format "~a ~a ~a" t a (dtext g))]
    [(list (and t (or 'L 'H)) a b g) (format "~a ~a ~a ~a" t a b (dtext g))]
    [(list 'Z a g) (format "Z ~a ~a" (dtext a) (dtext g))]
    [(list 'Y g) (format "Y ~a" (dtext g))]))
(define (core-step->dform st)
  (match st
    [(list 'T ls g) (list 'T ls (compress g))]
    [(list (and t (or 'E 'V)) a g) (list t a (compress g))]
    [(list (and t (or 'L 'H)) a b g) (list t a b (compress g))]
    [(list 'Z a g) (list 'Z (compress a) (compress g))]
    [(list 'Y g) (list 'Y (compress g))]
    [_ st]))
(define (thm-text t)
  (match-define (list st sig steps hyps) t)
  (string-append (dtext st) " " (nlist sig) " " (number->string (length steps)) " "
                 (string-join (map dform-step->text steps) " ") " " (nlist hyps)))
(define (structure-text rg ths)
  (string-append "JDG1\nR " (number->string (length rg)) "\n"
                 (string-join (for/list ([e rg]) (string-append (dtext (car e)) " " (nlist (cadr e)))) "\n") "\n"
                 "T " (number->string (length ths)) "\n"
                 (string-join (map thm-text ths) "\n") "\n"))

;; ======================================================================== named formulas
;; F ::= (in a b) | (eq a b) | (pr NAME a ...) | (not F) | (imp F G) | (and F ...) | (or F ...) | (iff F G)
;;     | (all x F) | (ex x F)      a ::= frame variable (exact integer) | bound symbol
;; and / or with several arguments nest to the left.
(define SYM (hash 'Sub 5 'Opr 8 'App 9 'Fnc 10 'Emp 17 'Suc 18 'Om 20 'Nat 72))
(define gensym-counter 0)
(define (fresh-sym base) (set! gensym-counter (add1 gensym-counter)) (string->symbol (format "~a#~a" base gensym-counter)))
(define (compile F [bound '()])
  (define (var a)
    (cond [(exact-integer? a) (+ a (length bound))]
          [(symbol? a) (or (index-of bound a) (error 'compile "unbound ~a" a))]
          [else (error 'compile "bad variable ~a" a)]))
  (define (c F) (compile F bound))
  (match F
    [(list 'in a b) (Mem (var a) (var b))]
    [(list 'eq a b) (Eqv (var a) (var b))]
    [(list 'pr name args ...) (Pr (hash-ref SYM name) (map var args))]
    [(list 'not G) (Neg (c G))]
    [(list 'imp G H) (Imp (c G) (c H))]
    [(list 'and G) (c G)]
    [(list 'and G H ... L) (Kf (c (cons 'and (cons G H))) (c L))]
    [(list 'or G) (c G)]
    [(list 'or G H ... L) (Df (c (cons 'or (cons G H))) (c L))]
    [(list 'iff G H) (Qf (c G) (c H))]
    [(list 'all x G) (All (compile G (cons x bound)))]
    [(list 'ex x G) (Xf (compile G (cons x bound)))]))
(define (c x) (compile x))

;; ======================================================================== the batch
(define REPLAY "C:/ClaudeOutput/pompetzki/judge/replay-all.jdg")
(define NBASE 677)                       ; registry: 7 axioms + 670 definitions; the 29 hypothesis entries are left out
(define RBASE 706)                       ; registry size of replay-all.jdg before its theorems

(define reg (make-vector 400000 #f))     ; (cons statement-core hyps)
(define nreg 0)
(define base-lines '())                  ; the registry text, verbatim from replay-all.jdg
(define out-thms '())                    ; reversed: (list key text prelude?)
(define names (make-hash))               ; key -> registry index
(define stats (make-hash))
(define def-entry (make-hash))           ; predicate symbol -> registry index of its definition
(define replay-thms #f)

(define (reg-stmt r) (car (vector-ref reg r)))
(define (reg-index key) (or (hash-ref names key #f) (error 'reg "no theorem ~a" key)))
(define (have? key) (and (hash-ref names key #f) #t))
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
  (for ([i (in-range 7 NBASE)])          ; each definition: A^k (Q (P p [k-1 .. 0]) body)
    (let loop ([f (reg-stmt i)] [k 0])
      (match f
        [(list 'A b) (loop b (add1 k))]
        [(list 'N (list 'I (list 'I (list 'P p args) _) _)) #:when (equal? args (reverse (range k))) (hash-set! def-entry p i)]
        [_ (error 'load "entry ~a is not a definition" i)]))))

(define (reset-batch!)
  (for ([i (in-range NBASE nreg)]) (vector-set! reg i #f))
  (set! nreg NBASE)
  (set! out-thms '())
  (hash-clear! names) (hash-clear! stats) (hash-clear! prelude-map)
  (set! stack '()))

(define (batch-text)
  (string-append "JDG1\nR " (number->string NBASE) "\n" (string-join base-lines "\n") "\n"
                 "T " (number->string (length out-thms)) "\n"
                 (string-join (map cadr (reverse out-thms)) "\n") "\n"))

;; ---- theorems under construction: a stack (a lemma needed inside a proof is built and appended first)
(struct thm (key [lines #:mutable] [n #:mutable] [steps #:mutable] [next #:mutable]))
(define stack '())
(define (cur) (if (null? stack) (error 'thm "no theorem open") (car stack)))
(define (begin-thm! key next-free) (set! stack (cons (thm key (make-vector 64 #f) 0 '() next-free) stack)))
(define (fresh!) (let* ([t (cur)] [v (thm-next t)]) (set-thm-next! t (add1 v)) v))
(define (line l) (let ([t (cur)]) (if (< l (thm-n t)) (vector-ref (thm-lines t) l) (error 'line "no line ~a" l))))

(define (add-step! st)
  (define t (cur))
  (define r (sstep reg nreg (thm-lines t) (thm-n t) st))
  (when (string? r)
    (eprintf "FAILED in ~a, step ~a: ~a\n" (thm-key t) (thm-n t) r)
    (match st
      [(list 'T ls g) (eprintf "  goal ~a\n" (show g)) (for ([l ls]) (eprintf "  premise ~a: ~a\n" l (show (line l))))]
      [(list (or 'E 'V 'Y) _ ... g) (eprintf "  ~a\n" (show g))]
      [(list (or 'L 'H) a b g) (eprintf "  ~a\n  line: ~a\n" (show g) (show (line (if (eq? (car st) 'L) a b))))]
      [_ (eprintf "  ~a\n" st)])
    (error 'step "~a" r))
  (when (eq? (car st) 'T) (bump! 'taut-calls taut-calls) (hash-update! stats 'taut-max (lambda (v) (max v taut-calls)) 0))
  (define n (thm-n t))
  (when (= n (vector-length (thm-lines t)))
    (let ([v (make-vector (* 2 n) #f)]) (vector-copy! v 0 (thm-lines t)) (set-thm-lines! t v)))
  (vector-set! (thm-lines t) n (car r))
  (set-thm-n! t (add1 n))
  (set-thm-steps! t (cons st (thm-steps t)))
  n)

;; the eleven steps; formulas are cores; U takes a registry index or a theorem key
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

(define (end-thm! stmt sig)
  (define t (cur))
  (define steps (reverse (thm-steps t)))
  (define r (check-thm reg nreg stmt sig steps '()))
  (unless (eq? r #t)
    (eprintf "FAILED theorem ~a: ~a\n  statement: ~a\n" (thm-key t) r (show (ren (sigf sig) stmt)))
    (error 'thm "~a" r))
  (set! stack (cdr stack))
  (vector-set! reg nreg (cons stmt '()))
  (hash-set! names (thm-key t) nreg)
  (set! out-thms (cons (list (thm-key t) (thm-text (list (compress stmt) sig (map core-step->dform steps) '())) #f) out-thms))
  (bump! 'theorems) (bump! 'steps (length steps))
  (set! nreg (add1 nreg))
  (sub1 nreg))

;; ---- the prelude: hypothesis-free theorems of the replay of Theorem 29, copied with their dependencies
(define prelude-map (make-hash))         ; replay theorem index -> registry index here
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
    (set! out-thms (cons (list (list 'replay idx) (thm-text (list st sig steps2 '())) #t) out-thms))
    (bump! 'prelude) (bump! 'prelude-steps (length steps2))
    (set! nreg (add1 nreg)))
  (hash-ref prelude-map idx))

;; (replay index, name, expected statement); each is checked against the expected statement when imported
(define PRELUDE
  `((6 OprEx (all a (all b (ex c (pr Opr c a b)))))
    (14 Kur1 (all a (all b (all c (all d (all e (imp (and (pr Opr a b c) (pr Opr a d e)) (eq b d))))))))
    (15 Kur2 (all a (all b (all c (all d (all e (imp (and (pr Opr a b c) (pr Opr a d e)) (eq c e))))))))
    (16 FncApp (all a (all b (all c (all d (imp (pr Fnc a) (imp (and (pr App a b c) (pr App a b d)) (eq c d))))))))
    (25 NoSelf (all a (not (in a a))))
    (26 NoTwo (all a (all b (not (and (in a b) (in b a))))))
    (27 SucUq (all a (all b (all c (imp (and (pr Suc a c) (pr Suc b c)) (eq a b))))))
    (31 MemApp (all a (all b (all c (all d (imp (and (in d a) (pr Opr d b c)) (pr App a b c)))))))
    (33 EmpUq (all a (all b (imp (and (pr Emp a) (pr Emp b)) (eq a b)))))
    (34 ZeroW (all a (all b (imp (and (pr Om a) (pr Emp b)) (in b a)))))
    (35 SucW (all a (all b (all c (imp (and (pr Om a) (in b a) (pr Suc c b)) (in c a))))))
    (268 SucEx (ex a (pr Suc a 0)))
    (356 AddEx (ex a (all b (iff (in b a) (or (in b 0) (eq b 1))))))
    (402 OmEx (ex a (pr Om a)))))

;; ---- lemmas on demand
(define generators (make-hash))
(define (ensure! key)
  (cond
    [(hash-ref names key #f) => values]
    [(and (symbol? key) (assq key (map (lambda (e) (cons (cadr e) e)) PRELUDE)))
     => (lambda (p)
          (match-define (list idx name expect) (cdr p))
          (define r (import-replay! idx))
          (unless (equal? (reg-stmt r) (c expect)) (error 'prelude "replay theorem ~a is not ~a" idx name))
          (hash-set! names key r)
          r)]
    [else ((hash-ref generators (if (pair? key) (car key) key) (lambda () (error 'ensure "no generator for ~a" key))) key)
          (reg-index key)]))
(define-syntax-rule (defgen kind (key) body ...) (hash-set! generators 'kind (lambda (key) body ...)))

;; ======================================================================== arithmetic in ZF
(define HOLE 999999)                     ; where a Leibniz formula is abstracted; never a frame variable

;; Chain(n) = Emp(v0) & Suc(v1,v0) & ... & Suc(vn,v(n-1)): the frame variables 0..n are the numerals 0..n
(define (chain n)
  (if (= n 0) '(pr Emp 0)
      `(and (pr Emp 0) ,@(for/list ([k (in-range 1 (add1 n))]) `(pr Suc ,k ,(sub1 k))))))
;; N_n(x): x is the von Neumann numeral n.  N_0(x) = Emp(x), N_(n+1)(x) = exists y (N_n(y) & Suc(x,y))
(define (num n x)
  (if (= n 0) `(pr Emp ,x)
      (let ([y (fresh-sym 'y)]) `(ex ,y (and ,(num (sub1 n) y) (pr Suc ,x ,y))))))

;; Add(x,y,z): exists f (Fnc(f) & forall o (Emp(o) -> App(f,o,x)) & forall i (i in y -> exists a App(f,i,a))
;;                       & forall i j a b (i in y & Suc(j,i) & App(f,i,a) & App(f,j,b) -> Suc(b,a)) & App(f,y,z))
;; Mul(x,y,z): the same with App(f,o,o) for the value at 0 and Add(a,x,b) for the step.
(define (fin-parts kind f x y z)
  (define o (fresh-sym 'o)) (define i (fresh-sym 'i)) (define a (fresh-sym 'a))
  (define i2 (fresh-sym 'i)) (define j (fresh-sym 'j)) (define a2 (fresh-sym 'a)) (define b (fresh-sym 'b))
  (list `(pr Fnc ,f)
        (if (eq? kind 'add) `(all ,o (imp (pr Emp ,o) (pr App ,f ,o ,x))) `(all ,o (imp (pr Emp ,o) (pr App ,f ,o ,o))))
        `(all ,i (imp (in ,i ,y) (ex ,a (pr App ,f ,i ,a))))
        `(all ,i2 (all ,j (all ,a2 (all ,b (imp (and (in ,i2 ,y) (pr Suc ,j ,i2) (pr App ,f ,i2 ,a2) (pr App ,f ,j ,b))
                                                 ,(if (eq? kind 'add) `(pr Suc ,b ,a2) (fin-f 'add a2 x b)))))))
        `(pr App ,f ,y ,z)))
(define (fin-body kind f x y z) `(and ,@(fin-parts kind f x y z)))
(define (fin-f kind x y z) (let ([f (fresh-sym 'f)]) `(ex ,f ,(fin-body kind f x y z))))
(define (add-f x y z) (fin-f 'add x y z))
(define (mul-f x y z) (fin-f 'mul x y z))
(define (fin-val kind x k) (if (eq? kind 'add) (+ x k) (* k x)))
(define (fin-top kind x y) (if (eq? kind 'add) (+ x y) (max (* x y) x y)))

(define (memchar-dsl n)
  (define d (fresh-sym 'd))
  (if (= n 0) `(all ,d (not (in ,d 0)))
      `(all ,d (iff (in ,d ,n) (or ,@(for/list ([k (in-range n)]) `(eq ,d ,k)))))))

;; ---- tactics
(define (ids n) (range n))
(define (spec name args) (S (U name '()) args))
(define (unfold sym args) (S (U (hash-ref def-entry (hash-ref SYM sym)) '()) args))
(define (def-body l) (match (line l) [(list 'N (list 'I (list 'I _ f) _)) f]))
(define (inst f t)
  (match f [(list 'A phi) (V t (Imp f (ren (scons t sid) phi)))] [_ (error 'inst "not a universal: ~a" (show f))]))
(define (inst* f ts)
  (let loop ([f f] [ts ts] [acc '()])
    (if (null? ts) (reverse acc)
        (let ([l (inst f (car ts))]) (match (line l) [(list 'I _ g) (loop g (cdr ts) (cons l acc))])))))
(define (leib F s t)                     ; F with HOLE: (s = t) -> (F[s] -> F[t])
  (define a (ren (absk HOLE) (c F)))
  (Z a (Imp (Eqv s t) (Imp (ren (scons s sid) a) (ren (scons t sid) a)))))
(define (tt goal . ls) (T ls (c goal)))

(define (in-line k n) (U `(In ,k ,n) (ids (add1 n))))
(define (notin-line k n) (U `(NotIn ,k ,n) (ids (add1 k))))
(define (ne-line i j) (U `(Ne ,i ,j) (ids (add1 (max i j)))))
(define (memchar-line n) (U `(MemChar ,n) (ids (add1 n))))
(define (numex-line n) (U `(NumEx ,n) (ids (add1 n))))
(define (numuq-line n p) (U `(NumUq ,n) (append (ids (add1 n)) (list p))))
(define (natnum-line n) (U `(NatNum ,n) (ids (add1 n))))
(define (finex-line kind x y) (U `(FinEx ,kind ,x ,y) (ids (add1 (fin-top kind x y)))))
(define (finuq-line kind x y p) (U `(FinUq ,kind ,x ,y) (append (ids (add1 (fin-top kind x y))) (list p))))

;; Suc(s,y) -> y in s          (s = 0, y = 1)
(defgen SucIn (key)
  (begin-thm! key 2)
  (define l0 (unfold 'Suc '(0 1)))
  (tt '(imp (pr Suc 0 1) (in 1 0)) l0 (inst (def-body l0) 1) (Y (Eqv 1 1)))
  (end-thm! (c '(imp (pr Suc 0 1) (in 1 0))) (ids 2)))

;; Suc(s,y) -> (d in y -> d in s)    (s = 0, y = 1, d = 2)
(defgen SucSub (key)
  (begin-thm! key 3)
  (define l0 (unfold 'Suc '(0 1)))
  (define g '(imp (pr Suc 0 1) (imp (in 2 1) (in 2 0))))
  (tt g l0 (inst (def-body l0) 2))
  (end-thm! (c g) (ids 3)))

;; exists x Emp(x), from the axiom of infinity (registry entry 4)
(defgen EmpEx (key)
  (begin-thm! key 2)
  (define ax (U 4 '()))
  (define body (match (line ax) [(list 'N (list 'A (list 'N b))) b]))
  (define e1 (match body [(list 'N (list 'I (list 'N (list 'A (list 'N e1b))) _)) e1b]))
  (define ed (unfold 'Emp '(1)))
  (define goal (c (let ([x (fresh-sym 'x)]) `(ex ,x (pr Emp ,x)))))
  (define l2 (E 1 (Imp (Pr 17 '(1)) goal)))
  (define P (ren (scons 1 sid) e1))      ; e = 1, w = 0
  (define l3 (T (list ed l2) (Imp P goal)))
  (define l4 (L l3 1 (Imp (Neg (All (Neg e1))) goal)))
  (define l5 (T (list l4) (Imp body goal)))
  (define l6 (L l5 0 (Imp (line ax) goal)))
  (M ax l6)
  (end-thm! goal '()))

;; Chain(n) -> N_n(v_n)
(defgen NumEx (key)
  (define n (cadr key))
  (begin-thm! key (add1 n))
  (define g `(imp ,(chain n) ,(num n n)))
  (if (= n 0) (tt g)
      (tt g (numex-line (sub1 n)) (E (sub1 n) (c `(imp (and ,(num (sub1 n) (sub1 n)) (pr Suc ,n ,(sub1 n))) ,(num n n))))))
  (end-thm! (c g) (ids (add1 n))))

;; Chain(n) -> (N_n(p) -> p = v_n)      p = n+1
(defgen NumUq (key)
  (define n (cadr key))
  (define p (add1 n))
  (begin-thm! key (+ n 2))
  (define g `(imp ,(chain n) (imp ,(num n p) (eq ,p ,n))))
  (if (= n 0)
      (tt g (spec 'EmpUq (list p 0)))
      (let* ([q (fresh!)]
             [l3 (tt `(imp (and ,(num (sub1 n) q) (pr Suc ,p ,q)) (imp ,(chain n) (eq ,p ,n)))
                     (numuq-line (sub1 n) q) (leib `(pr Suc ,p ,HOLE) q (sub1 n)) (spec 'SucUq (list p n (sub1 n))))]
             [l4 (L l3 q (c `(imp ,(num n p) (imp ,(chain n) (eq ,p ,n)))))])
        (tt g l4)))
  (end-thm! (c g) (ids (+ n 2))))

;; Chain(n) -> v_k in v_n     (k < n)
(defgen In (key)
  (match-define (list _ k n) key)
  (begin-thm! key (add1 n))
  (define g `(imp ,(chain n) (in ,k ,n)))
  (if (= n (add1 k))
      (tt g (U 'SucIn (list n k)))
      (tt g (in-line k (sub1 n)) (U 'SucSub (list n (sub1 n) k))))
  (end-thm! (c g) (ids (add1 n))))

;; Chain(k) -> not v_k in v_n   (k >= n)
(defgen NotIn (key)
  (match-define (list _ k n) key)
  (begin-thm! key (add1 k))
  (define g `(imp ,(chain k) (not (in ,k ,n))))
  (if (= k n) (tt g (spec 'NoSelf (list k))) (tt g (in-line n k) (spec 'NoTwo (list k n))))
  (end-thm! (c g) (ids (add1 k))))

;; Chain(max) -> not v_i = v_j   (i /= j)
(defgen Ne (key)
  (match-define (list _ i j) key)
  (define m (max i j))
  (begin-thm! key (add1 m))
  (define g `(imp ,(chain m) (not (eq ,i ,j))))
  (if (< i j)
      (tt g (in-line i j) (spec 'NoSelf (list i)) (leib `(not (in ,i ,HOLE)) i j))
      (tt g (in-line j i) (spec 'NoSelf (list j)) (leib `(in ,j ,HOLE) i j)))
  (end-thm! (c g) (ids (add1 m))))

;; Chain(n) -> forall d (d in v_n <-> d = v_0 or ... or d = v_(n-1));   n = 0: Chain(0) -> forall d not d in v_0
(defgen MemChar (key)
  (define n (cadr key))
  (begin-thm! key (add1 n))
  (define g `(imp ,(chain n) ,(memchar-dsl n)))
  (cond
    [(= n 0) (tt g (unfold 'Emp '(0)))]
    [else
     (define d (fresh!))
     (define prem
       (if (= n 1)
           (let ([ed (unfold 'Emp '(0))]) (list ed (inst (def-body ed) d)))
           (list (memchar-line (sub1 n)) (inst (c (memchar-dsl (sub1 n))) d))))
     (define sd (unfold 'Suc (list n (sub1 n))))
     (define t (apply tt `(imp ,(chain n) (iff (in ,d ,n) (or ,@(for/list ([k (in-range n)]) `(eq ,d ,k)))))
                      (append prem (list sd (inst (def-body sd) d)))))
     (H d t (c g))])
  (end-thm! (c g) (ids (add1 n))))

;; Chain(n) -> Nat(v_n), Nat(x) = exists w (Om(w) & x in w): the numerals are natural numbers
(defgen NatNum (key)
  (define n (cadr key))
  (begin-thm! key (add1 n))
  (define w (fresh!))
  (define g `(imp ,(chain n) (pr Nat ,n)))
  (define nd (unfold 'Nat (list n)))
  (define ex (E w (c `(imp (and (pr Om ,w) (in ,n ,w)) ,(let ([d (fresh-sym 'd)]) `(ex ,d (and (pr Om ,d) (in ,n ,d))))))))
  (define steps (cons (spec 'ZeroW (list w 0)) (for/list ([k (in-range 1 (add1 n))]) (spec 'SucW (list w (sub1 k) k)))))
  (define t1 (T (list* nd ex steps) (c `(imp (pr Om ,w) (imp ,(chain n) (pr Nat ,n))))))
  (define t2 (L t1 w (c `(imp ,(let ([d (fresh-sym 'd)]) `(ex ,d (pr Om ,d))) (imp ,(chain n) (pr Nat ,n))))))
  (M (U 'OmEx '()) t2)
  (end-thm! (c g) (ids (add1 n))))

;; Emp(e) -> exists r forall d (d in r <-> d = q_0 or ... or d = q_m)      e = 0, q_k = k+1
(define (finset-mc r m [qof add1])
  (define d (fresh-sym 'd))
  `(all ,d (iff (in ,d ,r) (or ,@(for/list ([k (in-range (add1 m))]) `(eq ,d ,(qof k)))))))
(defgen FinSet (key)
  (define m (cadr key))
  (begin-thm! key (+ m 2))
  (define (target) (let ([r (fresh-sym 'r)]) `(ex ,r ,(finset-mc r m))))
  (define g `(imp (pr Emp 0) ,(target)))
  (define (addset r old new) (let ([d (fresh-sym 'd)]) `(all ,d (iff (in ,d ,r) (or (in ,d ,old) (eq ,d ,new))))))
  (define (ex-of f) (let ([r2 (fresh-sym 'r)]) `(ex ,r2 ,(f r2))))
  (cond
    [(= m 0)
     (define r (fresh!)) (define d (fresh!))
     (define aex (U 'AddEx '(0 1)))
     (define ed (unfold 'Emp '(0)))
     (define i3 (tt `(imp (and (pr Emp 0) ,(addset r 0 1)) (iff (in ,d ,r) (eq ,d 1)))
                    ed (inst (c (addset r 0 1)) d) (inst (def-body ed) d)))
     (define i4 (H d i3 (c `(imp (and (pr Emp 0) ,(addset r 0 1)) ,(finset-mc r 0)))))
     (define i6 (tt `(imp ,(addset r 0 1) (imp (pr Emp 0) ,(target))) i4 (E r (c `(imp ,(finset-mc r 0) ,(target))))))
     (define i7 (L i6 r (c `(imp ,(ex-of (lambda (r2) (addset r2 0 1))) (imp (pr Emp 0) ,(target))))))
     (M aex i7)]
    [else
     (define fs (U `(FinSet ,(sub1 m)) (ids (add1 m))))
     (define r1 (fresh!)) (define r (fresh!)) (define d (fresh!))
     (define old (finset-mc r1 (sub1 m)))
     (define new (finset-mc r m))
     (define add (addset r r1 (add1 m)))
     (define aex (U 'AddEx (list r1 (add1 m))))
     (define i3 (tt `(imp (and ,old ,add) (iff (in ,d ,r) (or ,@(for/list ([k (in-range (add1 m))]) `(eq ,d ,(add1 k))))))
                    (inst (c old) d) (inst (c add) d)))
     (define i4 (H d i3 (c `(imp (and ,old ,add) ,new))))
     (define i6 (tt `(imp ,add (imp ,old ,(target))) i4 (E r (c `(imp ,new ,(target))))))
     (define i7 (L i6 r (c `(imp ,(ex-of (lambda (r2) (addset r2 r1 (add1 m)))) (imp ,old ,(target))))))
     (define i9 (tt `(imp ,old (imp (pr Emp 0) ,(target))) (M aex i7)))
     (define i10 (L i9 r1 (c `(imp ,(ex-of (lambda (r2) (finset-mc r2 (sub1 m)))) (imp (pr Emp 0) ,(target))))))
     (tt g fs i10)])
  (end-thm! (c g) (ids (+ m 2))))

;; (Fin kind x y): ((Chain(top) & Opr(q_0,0,w_0) & ... & Opr(q_y,y,w_y)) & forall d (d in r <-> d = q_0 or ...))
;;                 -> Body(r),   w_k = x+k (add) or k*x (mul), q_k = top+1+k, r = top+y+2
(defgen Fin (key)
  (match-define (list _ kind x y) key)
  (define top (fin-top kind x y))
  (define (w k) (fin-val kind x k))
  (define (q k) (+ top 1 k))
  (define r (+ top y 2))
  (begin-thm! key (+ top y 3))
  (define Hd `(and (and ,(chain top) ,@(for/list ([k (in-range (add1 y))]) `(pr Opr ,(q k) ,k ,(w k)))) ,(finset-mc r y q)))
  (define hC (c Hd))
  (define McC (c (finset-mc r y q)))
  (define (HL f) (Imp hC (c f)))
  (define (val-form k) (let ([a (fresh-sym 'a)]) `(all ,a (imp (pr App ,r ,k ,a) (eq ,a ,(w k))))))
  (define parts (fin-parts kind r x y (w y)))
  (define mem (for/vector ([k (in-range (add1 y))])
                (T (list (inst McC (q k)) (Y (Eqv (q k) (q k)))) (HL `(in ,(q k) ,r)))))
  (define app (for/vector ([k (in-range (add1 y))])
                (T (list (vector-ref mem k) (spec 'MemApp (list r k (w k) (q k)))) (HL `(pr App ,r ,k ,(w k))))))
  ;; the value at k is w_k
  (define val
    (for/vector ([k (in-range (add1 y))])
      (define d (fresh!)) (define a (fresh!))
      (define cases
        (for/list ([j (in-range (add1 y))])
          (define l1 (leib `(pr Opr ,HOLE ,k ,a) d (q j)))
          (define goal `(imp (eq ,d ,(q j)) (imp (pr Opr ,d ,k ,a) (eq ,a ,(w k)))))
          (if (= j k)
              (T (list l1 (spec 'Kur2 (list (q k) k a k (w k)))) (HL goal))
              (T (list l1 (spec 'Kur1 (list (q j) k a j (w j))) (ne-line k j)) (HL goal)))))
      (define comb (T (cons (inst McC d) cases) (HL `(imp (and (in ,d ,r) (pr Opr ,d ,k ,a)) (eq ,a ,(w k))))))
      (define ex (T (list comb) (Imp (c `(and (in ,d ,r) (pr Opr ,d ,k ,a))) (Imp hC (Eqv a (w k))))))
      (define el (L ex d (Imp (c (let ([d2 (fresh-sym 'd)]) `(ex ,d2 (and (in ,d2 ,r) (pr Opr ,d2 ,k ,a))))) (Imp hC (Eqv a (w k))))))
      (define v1 (T (list (unfold 'App (list r k a)) el) (HL `(imp (pr App ,r ,k ,a) (eq ,a ,(w k))))))
      (H a v1 (HL (val-form k)))))
  (define (val-core k) (c (val-form k)))
  ;; Fnc(r)
  (define fnc
    (let* ([i (fresh!)] [a (fresh!)] [b (fresh!)] [d (fresh!)])
      (define cases
        (for/list ([j (in-range (add1 y))])
          (T (list (vector-ref val j) (leib `(pr Opr ,HOLE ,i ,a) d (q j))
                   (spec 'Kur1 (list (q j) i a j (w j))) (spec 'Kur2 (list (q j) i a j (w j)))
                   (leib `(pr App ,r ,HOLE ,b) i j) (inst (val-core j) b) (leib `(not (eq ,a ,HOLE)) b (w j)))
             (HL `(imp (eq ,d ,(q j)) (imp (pr Opr ,d ,i ,a) (imp (pr App ,r ,i ,b) (eq ,a ,b))))))))
      (define concl `(imp (pr App ,r ,i ,b) (eq ,a ,b)))
      (define comb (T (cons (inst McC d) cases) (HL `(imp (and (in ,d ,r) (pr Opr ,d ,i ,a)) ,concl))))
      (define ex (T (list comb) (Imp (c `(and (in ,d ,r) (pr Opr ,d ,i ,a))) (Imp hC (c concl)))))
      (define el (L ex d (Imp (c (let ([d2 (fresh-sym 'd)]) `(ex ,d2 (and (in ,d2 ,r) (pr Opr ,d2 ,i ,a))))) (Imp hC (c concl)))))
      (define f1 (T (list (unfold 'App (list r i a)) el) (HL `(imp (and (pr App ,r ,i ,a) (pr App ,r ,i ,b)) (eq ,a ,b)))))
      (define b2 (fresh-sym 'b)) (define a2 (fresh-sym 'a)) (define i2 (fresh-sym 'i))
      (define f2 (H b f1 (HL `(all ,b2 (imp (and (pr App ,r ,i ,a) (pr App ,r ,i ,b2)) (eq ,a ,b2))))))
      (define f3 (H a f2 (HL `(all ,a2 (all ,b2 (imp (and (pr App ,r ,i ,a2) (pr App ,r ,i ,b2)) (eq ,a2 ,b2)))))))
      (define f4 (H i f3 (HL `(all ,i2 (all ,a2 (all ,b2 (imp (and (pr App ,r ,i2 ,a2) (pr App ,r ,i2 ,b2)) (eq ,a2 ,b2))))))))
      (T (list (unfold 'Fnc (list r)) f4) (HL `(pr Fnc ,r)))))
  ;; the value at the empty set
  (define zero
    (let ([o (fresh!)])
      (define l1 (spec 'EmpUq (list o 0)))
      (define z1
        (if (eq? kind 'add)
            (T (list (vector-ref app 0) l1 (leib `(not (pr App ,r ,HOLE ,x)) o 0)) (HL `(imp (pr Emp ,o) (pr App ,r ,o ,x))))
            (T (list (vector-ref app 0) l1 (leib `(not (pr App ,r ,HOLE ,HOLE)) o 0)) (HL `(imp (pr Emp ,o) (pr App ,r ,o ,o))))))
      (H o z1 (HL (list-ref parts 1)))))
  ;; defined on y
  (define dom
    (let ([i (fresh!)])
      (define (exapp z) (let ([a (fresh-sym 'a)]) `(ex ,a (pr App ,r ,z ,a))))
      (define cases
        (for/list ([k (in-range y)])
          (T (list (vector-ref app k) (E (w k) (c `(imp (pr App ,r ,k ,(w k)) ,(exapp k)))) (leib `(not ,(exapp HOLE)) i k))
             (HL `(imp (eq ,i ,k) ,(exapp i))))))
      (define d1 (T (list* (memchar-line y) (inst (c (memchar-dsl y)) i) cases) (HL `(imp (in ,i ,y) ,(exapp i)))))
      (H i d1 (HL (list-ref parts 2)))))
  ;; the step
  (define (concl a b) (if (eq? kind 'add) `(pr Suc ,b ,a) (add-f a x b)))
  (define step
    (let* ([i (fresh!)] [j (fresh!)] [a (fresh!)] [b (fresh!)])
      (define (prem jj aa bb) `(and (in ,i ,y) (pr Suc ,jj ,i) (pr App ,r ,i ,aa) (pr App ,r ,jj ,bb)))
      (define cases
        (for/list ([k (in-range y)])
          (define common
            (list (vector-ref val k) (vector-ref val (add1 k))
                  (leib `(pr Suc ,j ,HOLE) i k) (spec 'SucUq (list j (add1 k) k))
                  (leib `(pr App ,r ,HOLE ,a) i k) (inst (val-core k) a)
                  (leib `(pr App ,r ,HOLE ,b) j (add1 k)) (inst (val-core (add1 k)) b)))
          (define extra
            (if (eq? kind 'add)
                (list (leib `(not (pr Suc ,HOLE ,a)) b (w (add1 k))) (leib `(not (pr Suc ,(w (add1 k)) ,HOLE)) a (w k)))
                (list (leib `(not ,(add-f HOLE x b)) a (w k)) (leib `(not ,(add-f (w k) x HOLE)) b (w (add1 k)))
                      (finex-line 'add (w k) x))))
          (T (append common extra) (HL `(imp (eq ,i ,k) (imp ,(prem j a b) ,(concl a b)))))))
      (define s1 (T (list* (memchar-line y) (inst (c (memchar-dsl y)) i) cases) (HL `(imp ,(prem j a b) ,(concl a b)))))
      (define a2 (fresh-sym 'a)) (define b2 (fresh-sym 'b)) (define j2 (fresh-sym 'j))
      (define s2 (H b s1 (HL `(all ,b2 (imp ,(prem j a b2) ,(concl a b2))))))
      (define s3 (H a s2 (HL `(all ,a2 (all ,b2 (imp ,(prem j a2 b2) ,(concl a2 b2)))))))
      (define s4 (H j s3 (HL `(all ,j2 (all ,a2 (all ,b2 (imp ,(prem j2 a2 b2) ,(concl a2 b2))))))))
      (H i s4 (HL (list-ref parts 3)))))
  (T (list fnc zero dom step (vector-ref app y)) (HL `(and ,@parts)))
  (end-thm! (Imp hC (c `(and ,@parts))) (ids (+ top y 3))))

;; (FinEx kind x y): Chain(top) -> Add(v_x, v_y, v_(x+y))   or   -> Mul(v_x, v_y, v_(x*y))
(defgen FinEx (key)
  (match-define (list _ kind x y) key)
  (define top (fin-top kind x y))
  (define (w k) (fin-val kind x k))
  (define (q k) (+ top 1 k))
  (define r (+ top y 2))
  (begin-thm! key (+ top y 3))
  (define C (chain top))
  (define pairs (for/list ([k (in-range (add1 y))]) `(pr Opr ,(q k) ,k ,(w k))))
  (define Hp `(and ,C ,@pairs))
  (define goal-f (fin-f kind x y (w y)))
  (define l2 (tt `(imp ,(finset-mc r y q) (imp ,Hp ,goal-f))
                 (U `(Fin ,kind ,x ,y) (ids (+ top y 3))) (E r (c `(imp ,(fin-body kind r x y (w y)) ,goal-f)))))
  (define l3 (L l2 r (c `(imp ,(let ([r2 (fresh-sym 'r)]) `(ex ,r2 ,(finset-mc r2 y q))) (imp ,Hp ,goal-f)))))
  (define l5 (tt `(imp ,Hp ,goal-f) l3 (U `(FinSet ,y) (cons 0 (for/list ([k (in-range (add1 y))]) (q k))))))
  (for/fold ([cur l5]) ([k (in-range y -1 -1)])
    (define Hprev (if (= k 0) C `(and ,C ,@(take pairs k))))
    (define t1 (tt `(imp ,(list-ref pairs k) (imp ,Hprev ,goal-f)) cur))
    (define t2 (L t1 (q k) (c `(imp ,(let ([pp (fresh-sym 'p)]) `(ex ,pp (pr Opr ,pp ,k ,(w k)))) (imp ,Hprev ,goal-f)))))
    (M (spec 'OprEx (list k (w k))) t2))
  (end-thm! (c `(imp ,C ,goal-f)) (ids (add1 top))))

;; (FinUq kind x y): Chain(top) -> (Add(v_x, v_y, p) -> p = v_(x+y))   p = top+1; the same for Mul
(defgen FinUq (key)
  (match-define (list _ kind x y) key)
  (define top (fin-top kind x y))
  (define (w k) (fin-val kind x k))
  (define p (add1 top))
  (begin-thm! key (+ top 2))
  (define f (fresh!))
  (define C (chain top))
  (define parts (fin-parts kind f x y p))
  (define body `(and ,@parts))
  (define hC (c `(and ,C ,body)))
  (define (HL g) (Imp hC (c g)))
  (define start (T (list (inst (c (list-ref parts 1)) 0)) (HL `(pr App ,f 0 ,(w 0)))))
  (define fin
    (if (= y 0)
        (T (list (spec 'FncApp (list f 0 p (w 0))) start) (HL `(eq ,p ,(w 0))))
        (let loop ([k 0] [cur start])
          (define in0 (in-line k y))
          (cond
            [(< (add1 k) y)
             (define exa (let ([a (fresh-sym 'a)]) `(ex ,a (pr App ,f ,(add1 k) ,a))))
             (define ex1 (T (list (in-line (add1 k) y) (inst (c (list-ref parts 2)) (add1 k))) (HL exa)))
             (define b (fresh!))
             (define sl (inst* (c (list-ref parts 3)) (list k (add1 k) (w k) b)))
             (define un (if (eq? kind 'add) (spec 'SucUq (list b (w (add1 k)) (w k))) (finuq-line 'add (w k) x b)))
             (define tgt (c `(pr App ,f ,(add1 k) ,(w (add1 k)))))
             (define t1 (T (list* in0 cur un (leib `(pr App ,f ,(add1 k) ,HOLE) b (w (add1 k))) sl)
                           (Imp (c `(pr App ,f ,(add1 k) ,b)) (Imp hC tgt))))
             (define t2 (L t1 b (Imp (c exa) (Imp hC tgt))))
             (loop (add1 k) (T (list ex1 t2) (Imp hC tgt)))]
            [else
             (define sl (inst* (c (list-ref parts 3)) (list k y (w k) p)))
             (define un (if (eq? kind 'add) (spec 'SucUq (list p (w y) (w k))) (finuq-line 'add (w k) x p)))
             (T (list* in0 cur un sl) (HL `(eq ,p ,(w y))))]))))
  (define g1 (T (list fin) (Imp (c body) (Imp (c C) (Eqv p (w y))))))
  (define g2 (L g1 f (Imp (c (fin-f kind x y p)) (Imp (c C) (Eqv p (w y))))))
  (define g `(imp ,C (imp ,(fin-f kind x y p) (eq ,p ,(w y)))))
  (tt g g2)
  (end-thm! (c g) (ids (+ top 2))))

;; line l: Chain(N) -> G, G without the variables 0..N  ==>  line G (SucEx for v_N .. v_1, EmpEx for v_0)
(define (elim-chain l N Gc)
  (define l1
    (for/fold ([cur l]) ([k (in-range N 0 -1)])
      (define Cp (c (chain (sub1 k))))
      (define t1 (T (list cur) (Imp (c `(pr Suc ,k ,(sub1 k))) (Imp Cp Gc))))
      (define t2 (L t1 k (Imp (c (let ([s (fresh-sym 's)]) `(ex ,s (pr Suc ,s ,(sub1 k))))) (Imp Cp Gc))))
      (M (U 'SucEx (list (sub1 k))) t2)))
  (define t2 (L l1 0 (Imp (c (let ([e (fresh-sym 'e)]) `(ex ,e (pr Emp ,e)))) Gc)))
  (M (U 'EmpEx '()) t2))

;; ======================================================================== bounded sentences
(define SOME-LIMIT 1000)                 ; witnesses for (some x F) are searched below this

(define (normalize F)
  (match F
    [(list (or 'and 'or) A) (normalize A)]
    [(list (and op (or 'and 'or)) A B ... Z) (list op (normalize (cons op (cons A B))) (normalize Z))]
    [(list 'not A) (list 'not (normalize A))]
    [(list (and op (or 'imp 'iff)) A B) (list op (normalize A) (normalize B))]
    [(list (and q (or 'all 'ex 'alle 'exe)) x t A) (list q x t (normalize A))]
    [(list 'some x A) (list 'some x (normalize A))]
    [_ F]))

(define (ev-term t r)
  (match t
    [(? exact-nonnegative-integer?) t]
    [(? symbol?) (cdr (or (assq t r) (error 'ev "unbound ~a" t)))]
    [(list 'S a) (add1 (ev-term a r))]
    [(list '+ a b) (+ (ev-term a r) (ev-term b r))]
    [(list '* a b) (* (ev-term a r) (ev-term b r))]))
(define (q-range q n) (if (memq q '(alle exe)) (range (add1 n)) (range n)))
(define (witness x A r) (for/first ([k (in-range SOME-LIMIT)] #:when (ev A (cons (cons x k) r))) k))
(define (ev F r)
  (match F
    [(list '= a b) (= (ev-term a r) (ev-term b r))]
    [(list '< a b) (< (ev-term a r) (ev-term b r))]
    [(list '<= a b) (<= (ev-term a r) (ev-term b r))]
    [(list 'not A) (not (ev A r))]
    [(list 'and A B) (and (ev A r) (ev B r))]
    [(list 'or A B) (or (ev A r) (ev B r))]
    [(list 'imp A B) (or (not (ev A r)) (ev B r))]
    [(list 'iff A B) (eq? (ev A r) (ev B r))]
    [(list (and q (or 'all 'alle)) x t A) (for/and ([k (q-range q (ev-term t r))]) (ev A (cons (cons x k) r)))]
    [(list (and q (or 'ex 'exe)) x t A) (for/or ([k (q-range q (ev-term t r))]) (ev A (cons (cons x k) r)))]
    [(list 'some x A) (and (witness x A r) #t)]))

;; the largest numeral the derivation names
(define (tmax t r)
  (match t
    [(? exact-nonnegative-integer?) t]
    [(? symbol?) (ev-term t r)]
    [(list 'S a) (max (tmax a r) (ev-term t r))]
    [(list (or '+ '*) a b) (max (tmax a r) (tmax b r) (ev-term t r))]))
(define (fmax F r)
  (match F
    [(list (or '= '< '<=) a b) (max (tmax a r) (tmax b r))]
    [(list 'not A) (fmax A r)]
    [(list (or 'and 'or 'imp 'iff) A B) (max (fmax A r) (fmax B r))]
    [(list q x t A) #:when (memq q '(all ex alle exe))
     (apply max (tmax t r) (for/list ([k (q-range q (ev-term t r))]) (fmax A (cons (cons x k) r))))]
    [(list 'some x A) (let ([k (witness x A r)]) (max k (fmax A (cons (cons x k) r))))]))

;; [t] by continuation: a numeral n gives exists u (N_n(u) & K(u)); a variable x gives K(x); S t gives
;; [t](a. exists u (Suc(u,a) & K(u))); t+s gives [t](a. [s](b. exists u (Add(a,b,u) & K(u)))); t*s with Mul
(define (op-f op a b u) (if (eq? op '+) (add-f a b u) (mul-f a b u)))
(define (wrap t r K)
  (match t
    [(? exact-nonnegative-integer? n) (let ([u (fresh-sym 'u)]) `(ex ,u (and ,(num n u) ,(K u))))]
    [(? symbol? x) (K (cdr (assq x r)))]
    [(list 'S a) (wrap a r (lambda (va) (let ([u (fresh-sym 'u)]) `(ex ,u (and (pr Suc ,u ,va) ,(K u))))))]
    [(list (and op (or '+ '*)) a b)
     (wrap a r (lambda (va) (wrap b r (lambda (vb) (let ([u (fresh-sym 'u)]) `(ex ,u (and ,(op-f op va vb u) ,(K u))))))))]))
(define (bq-tr q x b A r)
  (define x2 (fresh-sym x))
  (define in-set (if (memq q '(alle exe)) `(or (in ,x2 ,b) (eq ,x2 ,b)) `(in ,x2 ,b)))
  (define body (tr A (cons (cons x x2) r)))
  (if (memq q '(all alle)) `(all ,x2 (imp ,in-set ,body)) `(ex ,x2 (and ,in-set ,body))))
(define (rel-dsl rel a b) (case rel [(=) `(eq ,a ,b)] [(<) `(in ,a ,b)] [(<=) `(or (in ,a ,b) (eq ,a ,b))]))
(define (tr F r)
  (match F
    [(list (and rel (or '= '< '<=)) a b) (wrap a r (lambda (va) (wrap b r (lambda (vb) (rel-dsl rel va vb)))))]
    [(list 'not A) `(not ,(tr A r))]
    [(list (and op (or 'and 'or 'imp 'iff)) A B) `(,op ,(tr A r) ,(tr B r))]
    [(list (and q (or 'all 'ex 'alle 'exe)) x t A) (wrap t r (lambda (b) (bq-tr q x b A r)))]
    [(list 'some x A) (let ([x2 (fresh-sym x)]) `(ex ,x2 (and (pr Nat ,x2) ,(tr A (cons (cons x x2) r)))))]))

;; ---- the prover: lines Chain(N) -> [F] (F true) or Chain(N) -> not [F] (F false)
(define Cc #f)
(define (cimp f) (Imp Cc f))

(define (prove-ex-R m R-tr ex-thunk uq-thunk K-tr K-prove)
  (define-values (tv kl) (K-prove m))
  (define (phi v) `(and ,(R-tr v) ,(K-tr v)))
  (define goal (let ([u (fresh-sym 'u)]) `(ex ,u ,(phi u))))
  (cond
    [tv (values #t (T (list (ex-thunk) kl (E m (c `(imp ,(phi m) ,goal)))) (cimp (c goal))))]
    [else
     (define p (fresh!))
     (define t1 (T (list kl (uq-thunk p) (leib (K-tr HOLE) p m)) (Imp (c (phi p)) (Neg Cc))))
     (define t2 (L t1 p (Imp (c goal) (Neg Cc))))
     (values #f (T (list t2) (cimp (Neg (c goal)))))]))

(define (pwrap t r K-tr K-prove)
  (match t
    [(? exact-nonnegative-integer? n)
     (prove-ex-R n (lambda (u) (num n u)) (lambda () (numex-line n)) (lambda (p) (numuq-line n p)) K-tr K-prove)]
    [(? symbol? x) (K-prove (cdr (assq x r)))]
    [(list 'S a)
     (pwrap a r (lambda (va) (let ([u (fresh-sym 'u)]) `(ex ,u (and (pr Suc ,u ,va) ,(K-tr u)))))
            (lambda (m1)
              (prove-ex-R (add1 m1) (lambda (u) `(pr Suc ,u ,m1))
                          (lambda () (T '() (cimp (Pr 18 (list (add1 m1) m1)))))
                          (lambda (p) (T (list (spec 'SucUq (list p (add1 m1) m1))) (cimp (Imp (Pr 18 (list p m1)) (Eqv p (add1 m1))))))
                          K-tr K-prove)))]
    [(list (and op (or '+ '*)) a b)
     (define kind (if (eq? op '+) 'add 'mul))
     (pwrap a r
            (lambda (va) (wrap b r (lambda (vb) (let ([u (fresh-sym 'u)]) `(ex ,u (and ,(op-f op va vb u) ,(K-tr u)))))))
            (lambda (m1)
              (pwrap b r
                     (lambda (vb) (let ([u (fresh-sym 'u)]) `(ex ,u (and ,(op-f op m1 vb u) ,(K-tr u)))))
                     (lambda (m2)
                       (prove-ex-R (if (eq? op '+) (+ m1 m2) (* m1 m2)) (lambda (u) (op-f op m1 m2 u))
                                   (lambda () (finex-line kind m1 m2)) (lambda (p) (finuq-line kind m1 m2 p))
                                   K-tr K-prove)))))]))

(define (atomic rel m1 m2)
  (define g (c (rel-dsl rel m1 m2)))
  (case rel
    [(=) (if (= m1 m2) (values #t (T (list (Y (Eqv m1 m1))) (cimp g))) (values #f (T (list (ne-line m1 m2)) (cimp (Neg g)))))]
    [(<) (if (< m1 m2) (values #t (T (list (in-line m1 m2)) (cimp g))) (values #f (T (list (notin-line m1 m2)) (cimp (Neg g)))))]
    [(<=) (cond [(< m1 m2) (values #t (T (list (in-line m1 m2)) (cimp g)))]
                [(= m1 m2) (values #t (T (list (Y (Eqv m1 m1))) (cimp g)))]
                [else (values #f (T (list (notin-line m1 m2) (ne-line m1 m2)) (cimp (Neg g))))])]))

(define (prove F r)
  (match F
    [(list (and rel (or '= '< '<=)) a b)
     (pwrap a r (lambda (va) (wrap b r (lambda (vb) (rel-dsl rel va vb))))
            (lambda (m1) (pwrap b r (lambda (vb) (rel-dsl rel m1 vb)) (lambda (m2) (atomic rel m1 m2)))))]
    [(list 'not A)
     (define-values (t l) (prove A r))
     (if t (values #f (T (list l) (cimp (Neg (Neg (c (tr A r))))))) (values #t l))]
    [(list (and op (or 'and 'or 'imp 'iff)) A B)
     (define ta (ev A r)) (define tb (ev B r))
     (define tv (case op [(and) (and ta tb)] [(or) (or ta tb)] [(imp) (or (not ta) tb)] [(iff) (eq? ta tb)]))
     (define need
       (case op
         [(and) (cond [(not ta) '(a)] [(not tb) '(b)] [else '(a b)])]
         [(or) (cond [ta '(a)] [tb '(b)] [else '(a b)])]
         [(imp) (cond [(not ta) '(a)] [tb '(b)] [else '(a b)])]
         [(iff) '(a b)]))
     (define ls (append (if (memq 'a need) (let-values ([(t l) (prove A r)]) (list l)) '())
                        (if (memq 'b need) (let-values ([(t l) (prove B r)]) (list l)) '())))
     (define f (c (tr F r)))
     (values tv (T ls (if tv (cimp f) (cimp (Neg f)))))]
    [(list (and q (or 'all 'ex 'alle 'exe)) x t A)
     (pwrap t r (lambda (b) (bq-tr q x b A r)) (lambda (n) (bounded q x n A r)))]
    [(list 'some x A)
     (define k (witness x A r))
     (unless k (error 'prove "no witness below ~a for ~a" SOME-LIMIT F))
     (define-values (t lk) (prove A (cons (cons x k) r)))
     (define whole (c (tr F r)))
     (define (FA z) (tr A (cons (cons x z) r)))
     (values #t (T (list (natnum-line k) lk (E k (Imp (c `(and (pr Nat ,k) ,(FA k))) whole))) (cimp whole)))]))

(define (bounded q x n A r)
  (define le? (memq q '(alle exe)))
  (define (F z) (tr A (cons (cons x z) r)))
  (define (setf z) (if le? `(or (in ,z ,n) (eq ,z ,n)) `(in ,z ,n)))
  (define whole (c (bq-tr q x n A r)))
  (define ks (q-range q n))
  (define (truth k) (ev A (cons (cons x k) r)))
  (define (line-at k) (let-values ([(t l) (prove A (cons (cons x k) r))]) l))
  (define (memb k)
    (if (< k n) (T (list (in-line k n)) (cimp (c (setf k)))) (T (list (Y (Eqv n n))) (cimp (c (setf k))))))
  (define (cases p neg?)
    (for/list ([k ks])
      (define lk (line-at k))
      (if neg?
          (T (list lk (leib (F HOLE) p k)) (cimp (c `(imp (eq ,p ,k) (not ,(F p))))))
          (T (list lk (leib `(not ,(F HOLE)) p k)) (cimp (c `(imp (eq ,p ,k) ,(F p))))))))
  (define (all-cases neg?)
    (define p (fresh!))
    (define body (if neg? `(not ,(F p)) (F p)))
    (values p (T (list* (memchar-line n) (inst (c (memchar-dsl n)) p) (cases p neg?)) (cimp (c `(imp ,(setf p) ,body))))))
  (cond
    [(memq q '(all alle))
     (cond
       [(andmap truth ks) (let-values ([(p comb) (all-cases #f)]) (values #t (H p comb (cimp whole))))]
       [else
        (define k (for/first ([k ks] #:unless (truth k)) k))
        (values #f (T (list (memb k) (line-at k) (inst whole k)) (cimp (Neg whole))))])]
    [(ormap truth ks)
     (define k (for/first ([k ks] #:when (truth k)) k))
     (values #t (T (list (memb k) (line-at k) (E k (Imp (c `(and ,(setf k) ,(F k))) whole))) (cimp whole)))]
    [else
     (define-values (p comb) (all-cases #t))
     (define t1 (T (list comb) (Imp (c `(and ,(setf p) ,(F p))) (Neg Cc))))
     (define t2 (L t1 p (Imp whole (Neg Cc))))
     (values #f (T (list t2) (cimp (Neg whole))))]))

;; the closed theorem of a sentence: [s] when s is true, not [s] when it is false
(define (sentence-thm! key s0)
  (define s (normalize s0))
  (define N (fmax s '()))
  (define tv (ev s '()))
  (begin-thm! key (add1 N))
  (set! Cc (c (chain N)))
  (define-values (t l) (prove s '()))
  (unless (eq? t tv) (error 'sentence "truth mismatch"))
  (define stmt (if tv (c (tr s '())) (Neg (c (tr s '())))))
  (elim-chain l N stmt)
  (end-thm! stmt '()))

;; ======================================================================== the closed layer theorems
;; body over the frame variables vars (all above N); the statement is its universal closure over vars
(define (closed-thm! key N vars body-dsl prem-thunk)
  (begin-thm! key (+ N 1 (length vars)))
  (set! Cc (c (chain N)))
  (define G0 (c body-dsl))
  (define e (elim-chain (T (prem-thunk) (cimp G0)) N G0))
  (define final (for/fold ([cur e]) ([v (reverse vars)]) (G cur v)))
  (end-thm! (line final) '()))
(define (vars-after N k) (for/list ([i (in-range k)]) (+ N 1 i)))

;; exists x N_n(x)
(define (thm-num-exist! n)
  (begin-thm! `(NumExist ,n) (add1 n))
  (set! Cc (c (chain n)))
  (define goal (c (let ([x (fresh-sym 'x)]) `(ex ,x ,(num n x)))))
  (elim-chain (T (list (numex-line n) (E n (Imp (c (num n n)) goal))) (cimp goal)) n goal)
  (end-thm! goal '()))
;; forall x y (N_n(x) -> (N_n(y) -> x = y))
(define (thm-num-unique! n)
  (match-define (list p q) (vars-after n 2))
  (closed-thm! `(NumUnique ,n) n (list p q) `(imp ,(num n p) (imp ,(num n q) (eq ,p ,q)))
               (lambda () (list (numuq-line n p) (numuq-line n q) (leib `(not (eq ,p ,HOLE)) q n)))))
;; forall w x (Om(w) -> (N_n(x) -> x in w))
(define (thm-num-nat! n)
  (match-define (list w p) (vars-after n 2))
  (closed-thm! `(NumNat ,n) n (list w p) `(imp (pr Om ,w) (imp ,(num n p) (in ,p ,w)))
               (lambda () (append (list (spec 'ZeroW (list w 0)) (numuq-line n p) (leib `(not (in ,HOLE ,w)) p n))
                                  (for/list ([k (in-range 1 (add1 n))]) (spec 'SucW (list w (sub1 k) k)))))))
;; forall x y (N_k(x) -> (N_n(y) -> x in y))   (k < n);   ... -> not x in y   (k >= n)
(define (thm-mem! k n)
  (define N (max k n))
  (match-define (list p q) (vars-after N 2))
  (if (< k n)
      (closed-thm! `(Mem ,k ,n) N (list p q) `(imp ,(num k p) (imp ,(num n q) (in ,p ,q)))
                   (lambda () (list (numuq-line k p) (numuq-line n q) (in-line k n)
                                    (leib `(not (in ,HOLE ,q)) p k) (leib `(not (in ,k ,HOLE)) q n))))
      (closed-thm! `(Mem ,k ,n) N (list p q) `(imp ,(num k p) (imp ,(num n q) (not (in ,p ,q))))
                   (lambda () (list (numuq-line k p) (numuq-line n q) (notin-line k n)
                                    (leib `(in ,HOLE ,q) p k) (leib `(in ,k ,HOLE) q n))))))
;; forall x y (N_n(x) -> (N_m(y) -> not x = y))   (n /= m)
(define (thm-neq! n m)
  (define N (max n m))
  (match-define (list p q) (vars-after N 2))
  (closed-thm! `(Neq ,n ,m) N (list p q) `(imp ,(num n p) (imp ,(num m q) (not (eq ,p ,q))))
               (lambda () (list (numuq-line n p) (numuq-line m q) (ne-line n m)
                                (leib `(eq ,HOLE ,q) p n) (leib `(eq ,n ,HOLE) q m)))))
;; forall y (N_n(y) -> forall x (x in y <-> N_0(x) or ... or N_(n-1)(x)));  n = 0: ... forall x not x in y
(define (thm-mem-num! n)
  (match-define (list q p) (vars-after n 2))
  (begin-thm! `(MemNum ,n) (+ n 3))
  (set! Cc (c (chain n)))
  (define (body x) (if (= n 0) `(not (in ,x ,q)) `(iff (in ,x ,q) (or ,@(for/list ([k (in-range n)]) (num k x))))))
  (define lks
    (for/list ([k (in-range n)])
      (T (list (numuq-line k p) (numex-line k) (leib `(not ,(num k HOLE)) p k)) (cimp (c `(iff ,(num k p) (eq ,p ,k)))))))
  (define t (T (list* (numuq-line n q) (memchar-line n) (inst (c (memchar-dsl n)) p)
                      (leib `(in ,p ,HOLE) q n) (leib `(not (in ,p ,HOLE)) q n) lks)
               (cimp (c `(imp ,(num n q) ,(body p))))))
  (define hyp (c `(and ,(chain n) ,(num n q))))
  (define x (fresh-sym 'x))
  (define t2 (H p (T (list t) (Imp hyp (c (body p)))) (Imp hyp (c `(all ,x ,(body x))))))
  (define G0 (c `(imp ,(num n q) (all ,x ,(body x)))))
  (define g (G (elim-chain (T (list t2) (cimp G0)) n G0) q))
  (end-thm! (line g) '()))
;; forall x z (N_a(x) -> (Suc(z,x) <-> N_(a+1)(z)))
(define (thm-suc-graph! a)
  (define N (add1 a))
  (match-define (list p r) (vars-after N 2))
  (closed-thm! `(SucGraph ,a) N (list p r) `(imp ,(num a p) (iff (pr Suc ,r ,p) ,(num (add1 a) r)))
               (lambda () (list (numuq-line a p) (numuq-line (add1 a) r) (numex-line (add1 a))
                                (spec 'SucUq (list r (add1 a) a)) (leib `(pr Suc ,r ,HOLE) p a)
                                (leib `(not ,(num (add1 a) HOLE)) r (add1 a))
                                (leib `(not (pr Suc ,HOLE ,p)) r (add1 a)) (leib `(not (pr Suc ,(add1 a) ,HOLE)) p a)))))
;; forall x y z (N_a(x) -> (N_b(y) -> (Op(x,y,z) <-> N_s(z))))     Op = Add (s = a+b) or Mul (s = a*b)
(define (thm-op-graph! kind a b)
  (define N (fin-top kind a b))
  (define s (if (eq? kind 'add) (+ a b) (* a b)))
  (define (op x y z) (fin-f kind x y z))
  (match-define (list p q r) (vars-after N 3))
  (closed-thm! `(,(if (eq? kind 'add) 'AddGraph 'MulGraph) ,a ,b) N (list p q r)
               `(imp ,(num a p) (imp ,(num b q) (iff ,(op p q r) ,(num s r))))
               (lambda () (list (numuq-line a p) (numuq-line b q) (numuq-line s r) (numex-line s)
                                (finex-line kind a b) (finuq-line kind a b r)
                                (leib (op HOLE q r) p a) (leib (op a HOLE r) q b) (leib `(not ,(num s HOLE)) r s)
                                (leib `(not ,(op a b HOLE)) r s) (leib `(not ,(op HOLE q r)) p a)
                                (leib `(not ,(op a HOLE r)) q b)))))

;; ======================================================================== random bounded sentences (exact LCG)
(define lcg-state 20261009)
(define (rnd n)
  (set! lcg-state (modulo (+ (* lcg-state 6364136223846793005) 1442695040888963407) 18446744073709551616))
  (modulo (arithmetic-shift lcg-state -33) n))
(define (pick l) (list-ref l (rnd (length l))))
(define (rand-term vars depth)
  (define leaf (lambda () (if (and (pair? vars) (< (rnd 3) 2)) (pick vars) (rnd 4))))
  (if (= depth 0) (leaf)
      (case (rnd 5)
        [(0 1) (leaf)]
        [(2) (list 'S (rand-term vars (sub1 depth)))]
        [(3) (list '+ (rand-term vars (sub1 depth)) (rand-term vars (sub1 depth)))]
        [else (list '* (leaf) (leaf))])))
(define (rand-formula vars depth)
  (if (= depth 0)
      (list (pick '(= < <=)) (rand-term vars 1) (rand-term vars 1))
      (case (rnd 9)
        [(0) (list 'not (rand-formula vars (sub1 depth)))]
        [(1) (list (pick '(and or imp iff)) (rand-formula vars (sub1 depth)) (rand-formula vars (sub1 depth)))]
        [(2 3 4 5) (let ([x (string->symbol (format "x~a" (length vars)))])
                     (list (pick '(all ex alle exe)) x (if (and (pair? vars) (= (rnd 2) 0)) (pick vars) (add1 (rnd 4)))
                           (rand-formula (cons x vars) (sub1 depth))))]
        [else (rand-formula vars 0)])))

;; ======================================================================== the layers
(define LAYERS
  (list
   (list "01-numerals" "von Neumann numerals: existence, uniqueness, membership in omega"
         (append (for/list ([n (in-range 13)]) `(exist ,n)) (for/list ([n (in-range 13)]) `(unique ,n))
                 (for/list ([n (in-range 13)]) `(nat ,n))))
   (list "02-membership" "k in n for k < n, not k in n for k >= n"
         (for*/list ([k (in-range 10)] [n (in-range 10)]) `(mem ,k ,n)))
   (list "03-distinct" "n /= m"
         (for*/list ([n (in-range 10)] [m (in-range 10)] #:unless (= n m)) `(neq ,n ,m)))
   (list "04-bounded" "bounded quantifiers over numerals"
         (append (for/list ([n (in-range 10)]) `(memnum ,n))
                 (map (lambda (s) `(sent ,s))
                      '((all x 5 (< x 5)) (all x 0 (= x 7)) (ex x 6 (= x 5)) (ex x 0 (= x 0))
                        (alle x 4 (<= x 4)) (exe x 3 (= x 3)) (all x 4 (ex y 5 (< x y)))
                        (all x 4 (all y 4 (or (< x y) (or (= x y) (< y x))))) (ex x 4 (all y 4 (<= y x)))
                        (all x 5 (not (< x 0))) (alle x 3 (exe y 3 (= x y))) (all x 6 (< x 4))))))
   (list "05-arithmetic" "successor, addition and multiplication as defined relations"
         (append (for/list ([a (in-range 10)]) `(suc ,a))
                 (for*/list ([a (in-range 9)] [b (in-range 9)] #:when (<= (+ a b) 8)) `(add ,a ,b))
                 (for*/list ([a (in-range 4)] [b (in-range 4)]) `(mul ,a ,b))))
   (list "06-sentences" "true bounded sentences, hand-picked and random (false ones as their negations)"
         (append
          (map (lambda (s) `(sent ,s))
               '((= (+ 2 3) 5) (not (= (+ 2 2) 5)) (= (* 3 4) 12) (< (* 2 3) (+ 4 3))
                 (= (S (S (+ 1 (* 2 2)))) 7) (all x 4 (ex y 5 (= (S x) y))) (all x 5 (< x 4))
                 (exe x 3 (= (+ x x) 6)) (alle x 3 (<= (* x x) 9)) (iff (< 3 5) (not (< 5 3)))
                 (ex x 5 (= (* x 2) 7)) (all x (+ 2 1) (< (* x x) (S (* 2 2))))
                 (all x 3 (all y 3 (= (+ x y) (+ y x)))) (all x 3 (all y 3 (= (* x y) (* y x))))
                 (all x 3 (= (* x (+ 1 1)) (+ x x))) (all n 6 (or (= n 0) (ex m n (= (S m) n))))
                 (all n 7 (ex k 4 (or (= n (* 2 k)) (= n (S (* 2 k))))))
                 (all a 6 (all b 6 (imp (= (* a b) 5) (or (= a 1) (= b 1)))))
                 (not (all a 5 (all b 5 (imp (= (* a b) 4) (or (= a 1) (= b 1))))))
                 (ex x 10 (= (* x x) 9)) (all x 4 (all y 4 (imp (< x y) (< (+ x 1) (+ y 1)))))))
          (for/list ([i (in-range 40)]) `(sent ,(rand-formula '() 3)))))
   (list "07-sigma1" "true Sigma-1 sentences: unbounded exists over omega, witness by search"
         (map (lambda (s) `(sent ,s))
              '((some x (= (* x x) 16)) (some x (some y (and (< 1 x) (and (< x y) (= (* x y) 6)))))
                (all n 4 (some m (= (+ n n) m))) (some p (and (< 4 p) (alle a p (alle b p (imp (= (* a b) p) (or (= a 1) (= b 1)))))))
                (some x (and (< 1 x) (= (+ x 2) (* x 2)))))))))

(define (job->thm! j)
  (match j
    [(list 'exist n) (thm-num-exist! n)]
    [(list 'unique n) (thm-num-unique! n)]
    [(list 'nat n) (thm-num-nat! n)]
    [(list 'mem k n) (thm-mem! k n)]
    [(list 'neq n m) (thm-neq! n m)]
    [(list 'memnum n) (thm-mem-num! n)]
    [(list 'suc a) (thm-suc-graph! a)]
    [(list 'add a b) (thm-op-graph! 'add a b)]
    [(list 'mul a b) (thm-op-graph! 'mul a b)]
    [(list 'sent s) (sentence-thm! `(Sent ,s) s)]))

;; a false statement for the semantic mutant of the last theorem
(define (twin j)
  (define (all2 f) (let ([x (fresh-sym 'x)] [y (fresh-sym 'y)]) `(all ,x (all ,y ,(f x y)))))
  (define (all3 f) (let ([x (fresh-sym 'x)] [y (fresh-sym 'y)] [z (fresh-sym 'z)]) `(all ,x (all ,y (all ,z ,(f x y z))))))
  (match j
    [(list 'exist n) `(not ,(let ([x (fresh-sym 'x)]) `(ex ,x ,(num n x))))]
    [(list 'unique n) (all2 (lambda (x y) `(imp ,(num n x) (imp ,(num n y) (not (eq ,x ,y))))))]
    [(list 'nat n) (all2 (lambda (w x) `(imp (pr Om ,w) (imp ,(num n x) (not (in ,x ,w))))))]
    [(list 'mem k n) (all2 (lambda (x y) `(imp ,(num k x) (imp ,(num n y) ,(if (< k n) `(not (in ,x ,y)) `(in ,x ,y))))))]
    [(list 'neq n m) (all2 (lambda (x y) `(imp ,(num n x) (imp ,(num m y) (eq ,x ,y)))))]
    [(list 'memnum n) (let ([y (fresh-sym 'y)] [x (fresh-sym 'x)])
                        `(all ,y (imp ,(num n y) (all ,x (iff (in ,x ,y) (or ,@(for/list ([k (in-range (add1 n))]) (num k x))))))))]
    [(list 'suc a) (all2 (lambda (x z) `(imp ,(num a x) (iff (pr Suc ,z ,x) ,(num (+ a 2) z)))))]
    [(list (and op (or 'add 'mul)) a b)
     (define s (if (eq? op 'add) (+ a b 1) (add1 (* a b))))
     (all3 (lambda (x y z) `(imp ,(num a x) (imp ,(num b y) (iff ,(fin-f op x y z) ,(num s z))))))]
    [(list 'sent s) (let ([s (normalize s)]) (if (ev s '()) `(not ,(tr s '())) (tr s '())))]))

;; build one file: (list text build-ms stats keys prelude-flags)
(define (build-file jobs)
  (reset-batch!)
  (define t0 (current-milliseconds))
  (for ([j jobs]) (job->thm! j))
  (define ths (reverse out-thms))
  (list (batch-text) (- (current-milliseconds) t0) (hash-copy stats) (map car ths) (map caddr ths)))

;; ---- mutated copies: (list tag text)
(define (mutants text twin-core prelude-flags)
  (define-values (rg ths) (read-jdg-text text))
  (define tv (list->vector ths))
  (define pv (list->vector prelude-flags))
  (define nth (vector-length tv))
  (define (with-thm i t) (structure-text rg (for/list ([x tv] [j (in-naturals)]) (if (= j i) t x))))
  (define (first-step pred)
    (for*/first ([i (in-range nth)] #:unless (vector-ref pv i)
                 [sv (in-value (list->vector (caddr (vector-ref tv i))))] [k (in-range (vector-length sv))]
                 #:when (pred (vector-ref sv k)))
      (list i k)))
  (define (replace-step i k f)
    (match-define (list st sig steps hyps) (vector-ref tv i))
    (with-thm i (list st sig (for/list ([s steps] [j (in-naturals)]) (if (= j k) (f s) s)) hyps)))
  (define last-i (sub1 nth))
  (match-define (list lst lsig lsteps lhyps) (vector-ref tv last-i))
  (define suc-entry (hash-ref def-entry 18))
  (filter
   values
   (list
    (list "neg-final" (with-thm last-i (list (list 'n lst) lsig lsteps lhyps)))
    (list "twin-final" (with-thm last-i (list (compress twin-core) lsig lsteps lhyps)))
    (match (first-step (lambda (s) (eq? (car s) 'T)))
      [(list i k) (list "taut-goal" (replace-step i k (lambda (s) (list 'T (cadr s) (list 'n (caddr s))))))] [_ #f])
    (match (first-step (lambda (s) (and (eq? (car s) 'M) (not (= (cadr s) (caddr s))))))
      [(list i k) (list "mp-swap" (replace-step i k (lambda (s) (list 'M (caddr s) (cadr s)))))] [_ #f])
    (match (first-step (lambda (s) (eq? (car s) 'U)))
      [(list i k) (list "use-shift" (replace-step i k (lambda (s) (list 'U (add1 (cadr s)) (caddr s)))))] [_ #f])
    (match (first-step (lambda (s) (match s [(list 'Z _ (list 'i (list 'q a b) _)) (not (= a b))] [_ #f])))
      [(list i k) (list "leib-swap" (replace-step i k (lambda (s) (match s [(list 'Z a (list 'i (list 'q x y) r)) (list 'Z a (list 'i (list 'q y x) r))]))))] [_ #f])
    (match (first-step (lambda (s) (eq? (car s) 'E)))
      [(list i k) (list "exi-witness" (replace-step i k (lambda (s) (list 'E (add1 (cadr s)) (caddr s)))))] [_ #f])
    (match (first-step (lambda (s) (eq? (car s) 'L)))
      [(list i k) (list "exel-var" (replace-step i k (lambda (s) (list 'L (cadr s) (add1 (caddr s)) (cadddr s)))))] [_ #f])
    (list "drop-step" (with-thm last-i (list lst lsig (drop-right lsteps 1) lhyps)))
    (list "registry-suc"
          (structure-text (for/list ([e rg] [i (in-naturals)])
                            (if (= i suc-entry)
                                (list (let loop ([d (car e)])   ; Suc2: d1 in s <-> d1 in y or d1 = y  becomes  ... or d1 = s
                                        (match d
                                          [(list 'a x) (list 'a (loop x))]
                                          [(list 'b x y) (list 'b (loop x) (loop y))]
                                          [(list 'd (list 'e 0 1) (list 'q 0 1)) (list 'd (list 'e 0 1) (list 'q 0 2))]
                                          [_ d]))
                                      (cadr e))
                                e))
                          ths)))))

;; ---- the registry against RpInit.v (its own parse of the Rocq data, independent of rocq2jdg.rkt)
(define RPINIT "C:/ClaudeOutput/pompetzki/forcing-src/general/RpInit.v")
(define (rocq-tokens s)
  (define no-comments
    (let loop ([i 0] [depth 0] [acc '()])
      (cond [(>= i (string-length s)) (list->string (reverse acc))]
            [(and (< (add1 i) (string-length s)) (char=? (string-ref s i) #\() (char=? (string-ref s (add1 i)) #\*)) (loop (+ i 2) (add1 depth) acc)]
            [(and (> depth 0) (< (add1 i) (string-length s)) (char=? (string-ref s i) #\*) (char=? (string-ref s (add1 i)) #\))) (loop (+ i 2) (sub1 depth) acc)]
            [(> depth 0) (loop (add1 i) depth acc)]
            [else (loop (add1 i) depth (cons (string-ref s i) acc))])))
  (regexp-match* #px"\\(|\\)|\\[|\\]|;|:=|[A-Za-z_][A-Za-z0-9_']*|[0-9]+|\\.|:" no-comments))
(define (rocq-list toks name)
  (define v (list->vector toks))
  (define start (for/first ([i (in-range (sub1 (vector-length v)))]
                            #:when (and (equal? (vector-ref v i) "Definition") (equal? (vector-ref v (add1 i)) name))) i))
  (define p (let skip ([i start]) (if (equal? (vector-ref v i) ":=") (add1 i) (skip (add1 i)))))
  (define (tok) (begin0 (vector-ref v p) (set! p (add1 p))))
  (define (expect s) (unless (equal? (tok) s) (error 'rocq "expected ~a" s)))
  (define (num) (string->number (tok)))
  (define (nums) (expect "[")
    (if (equal? (vector-ref v p) "]") (begin (tok) '())
        (let loop ([acc (list (num))]) (if (equal? (tok) ";") (loop (cons (num) acc)) (reverse acc)))))
  (define (form)
    (expect "(")
    (define ctor (tok))
    (define r
      (case ctor
        [("dE") (let* ([x (num)] [y (num)]) (list 'e x y))]
        [("dEq") (let* ([x (num)] [y (num)]) (list 'q x y))]
        [("dP") (let* ([pp (num)] [a (nums)]) (list 'p pp a))]
        [("dN") (list 'n (form))] [("dA") (list 'a (form))] [("dX") (list 'x (form))]
        [("dI") (let* ([a (form)] [b (form)]) (list 'i a b))]
        [("dK") (let* ([a (form)] [b (form)]) (list 'k a b))]
        [("dD") (let* ([a (form)] [b (form)]) (list 'd a b))]
        [("dQ") (let* ([a (form)] [b (form)]) (list 'b a b))]
        [else (error 'rocq "constructor ~a" ctor)]))
    (expect ")")
    r)
  (expect "[")
  (let loop ([acc (list (form))]) (if (equal? (tok) ";") (loop (cons (form) acc)) (reverse acc))))
(define (check-registry-text text)
  (define toks (rocq-tokens (file->string RPINIT)))
  (define ax0 (rocq-list toks "AX0"))
  (define def0 (rocq-list toks "DEF0"))
  (define reg0 (append ax0 def0))
  (define-values (rg ths) (read-jdg-text text))
  (cond
    [(not (= (length rg) (length reg0))) (format "FAIL: ~a entries, AX0 ++ DEF0 has ~a" (length rg) (length reg0))]
    [(for/or ([e rg]) (pair? (cadr e))) "FAIL: an entry carries hypotheses"]
    [(for/first ([e rg] [d reg0] [i (in-naturals)] #:unless (equal? (car e) d)) i) => (lambda (i) (format "FAIL: entry ~a differs from RpInit.v" i))]
    [else (format "OK: ~a entries = AX0 (~a) ++ DEF0 (~a) of RpInit.v, entry for entry, none with hypotheses" (length rg) (length ax0) (length def0))]))

;; ---- the judges
(define JUDGE-DIR "C:/ClaudeOutput/pompetzki/judge")
(define PMP "C:/ClaudeOutput/pompetzki/pompetzki.exe")
(define RACKET "C:/Program Files/Racket/racket.exe")
(define (run-cmd dir exe args)
  (parameterize ([current-directory dir])
    (define t0 (current-milliseconds))
    (define-values (sp out in err) (apply subprocess #f #f #f exe args))
    (close-output-port in)
    (define o (port->string out)) (define e (port->string err))
    (subprocess-wait sp)
    (close-input-port out) (close-input-port err)
    (list (subprocess-status sp) (- (current-milliseconds) t0) (string-trim (string-append o e)))))
(define (verdict out) (cond [(regexp-match? #rx"^ACCEPT" out) "ACCEPT"] [(regexp-match? #rx"REJECT" out) "REJECT"]
                            [(regexp-match? #rx"LIMIT" out) "LIMIT"] [else "OTHER"]))
(define (one-line s) (string-join (string-split s) " "))

(define (sha256-hex path) (call-with-input-file path (lambda (in) (bytes->hex-string (sha256-bytes in)))))
(define (write-new path text) (call-with-output-file path #:exists 'error (lambda (o) (write-string text o))) (void))

;; ======================================================================== commands
(define (cmd-emit dir)
  (load-base!)
  (make-directory* (build-path dir "mut"))
  (define manifest '())
  (define (note! . xs) (set! manifest (cons (apply format xs) manifest)) (printf "~a\n" (car manifest)) (flush-output))
  (for ([layer LAYERS])
    (match-define (list base what jobs) layer)
    (match-define (list text ms st keys pflags) (build-file jobs))
    (define file (build-path dir (string-append base ".jdg")))
    (write-new file text)
    (define-values (rg ths) (read-jdg-text text))
    (note! "~a.jdg  ~a" base what)
    (note! "  theorems ~a (prelude ~a, generated ~a), steps ~a (prelude ~a), bytes ~a, build ~a ms, largest tautology test ~a calls"
           (length ths) (hash-ref st 'prelude 0) (hash-ref st 'theorems 0)
           (+ (hash-ref st 'steps 0) (hash-ref st 'prelude-steps 0)) (hash-ref st 'prelude-steps 0)
           (file-size file) ms (hash-ref st 'taut-max 0))
    (note! "  sha256 ~a" (sha256-hex file))
    (note! "  registry: ~a" (check-registry-text text))
    (note! "  copy of the checker: ~a" (check-batch rg ths))
    ;; the listing of the theorems: index, key, statement
    (write-new (build-path dir (string-append base ".index.txt"))
               (string-join (for/list ([k keys] [t ths] [i (in-naturals)])
                              (format "~a ~a ~a" i k (if (and (pair? k) (eq? (car k) 'replay)) "" (show (tof (car t))))))
                            "\n"))
    (for ([m (mutants text (c (twin (last jobs))) pflags)])
      (match-define (list tag mtext) m)
      (define mf (build-path dir "mut" (string-append base "-" tag ".jdg")))
      (write-new mf mtext)
      (define-values (mrg mths) (read-jdg-text mtext))
      (note! "  mutant ~a: copy of the checker ~a" tag (check-batch mrg mths))))
  (write-new (build-path dir "manifest.txt") (string-join (reverse manifest) "\n")))

(define (cmd-judge dir results)
  (define files (append (sort (for/list ([f (directory-list dir #:build? #t)] #:when (regexp-match? #rx"[.]jdg$" (path->string f))) (path->string f)) string<?)
                        (sort (for/list ([f (directory-list (build-path dir "mut") #:build? #t)] #:when (regexp-match? #rx"[.]jdg$" (path->string f))) (path->string f)) string<?)))
  (define o (open-output-file results #:exists 'error))
  (for ([f files])
    (define full (path->string (path->complete-path f)))
    (match-define (list e1 t1 o1) (run-cmd JUDGE-DIR PMP (list "judge-v3.pmp" full)))
    (match-define (list e2 t2 o2) (run-cmd JUDGE-DIR RACKET (list "racket/judge.rkt" full)))
    (define row (format "~a | pmp ~a exit ~a ~a ms | racket ~a exit ~a ~a ms | pmp: ~a | racket: ~a"
                        f (verdict o1) e1 t1 (verdict o2) e2 t2 (one-line o1) (one-line o2)))
    (displayln row o) (flush-output o)
    (printf "~a\n" row) (flush-output))
  (close-output-port o))

(define (cmd-sentence sx out)
  (load-base!)
  (define s (with-input-from-string sx read))
  (reset-batch!)
  (sentence-thm! `(Sent ,s) s)
  (define text (batch-text))
  (write-new out text)
  (define-values (rg ths) (read-jdg-text text))
  (printf "~a: ~a; copy of the checker ~a\n" (if (ev (normalize s) '()) "true, [s] derived" "false, not [s] derived") out (check-batch rg ths)))

(module+ main
  (define args (vector->list (current-command-line-arguments)))
  (match args
    [(list "emit" dir) (cmd-emit dir)]
    [(list "judge" dir results) (cmd-judge dir results)]
    [(list "sentence" sx out) (cmd-sentence sx out)]
    [(list "check-registry" file) (printf "~a\n" (check-registry-text (file->string file)))]
    [_ (printf "usage: racket sigma1.rkt emit DIR | judge DIR RESULTS | sentence SEXP OUT.jdg | check-registry FILE\n")]))
