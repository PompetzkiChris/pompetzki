#lang racket/base
;; lch2.rkt -- lane LCH of the release-day orders 2026-10-09: ZF derivations, in the judge's format JDG1, for Goedel's
;; half of the independence of CH. Layer 01: the alignment of Theorem 29's notCH* with the plain statement of CH used by
;; GoedelCH.v (ch_text): notCH* <-> not CH, with the lemmas LeSub and PowEx.
;;
;; Not trusted. Every file it writes is checked by the two judges (judge-v3.pmp under pompetzki.exe, and
;; racket/judge.rkt). The formula code, the copy of Replay2.v's step semantics, the JDG1 reader and writer, the registry
;; loader, the mutants and the judge runner are copied verbatim from sigma1/sigma1.rkt (lines 23-357, 359-545, 581-594,
;; 1338-1456 of that file, which is not changed); the symbol table SYM is extended; the derivations and commands are new.
;;
;; Usage:
;;   racket lch.rkt emit DIR             write DIR/01-align.jdg, its index and DIR/mut/*.jdg
;;   racket lch.rkt judge DIR RESULTS    run both judges on DIR/*.jdg and DIR/mut/*.jdg, write RESULTS (a new file)
;; Exact integers only.

;; ======================================================================== formulas (Syn.v form)
;; (lch2.rkt: lch.rkt with the require line of sigma1.rkt, line 23, included; lch.rkt left it out.)
(require racket/list racket/string racket/match racket/file racket/port file/sha1)
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
(define SYM (hash 'Sub 5 'Sng 6 'Upr 7 'Opr 8 'App 9 'Fnc 10 'Inj 11 'Tot 12 'Rng 13 'Le 14 'Tr 15 'Ord 16 'Emp 17
                  'Suc 18 'Ind 19 'Om 20 'Nat 72 'M 5000))
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
;; ======================================================================== lane LCH: derivations
;; helpers that compute the rule's formula from the line it uses
(define (alli k l) (match (line l) [(list 'I hyp f) (H k l (Imp hyp (All (ren (absk k) f))))]
                     [x (error 'alli "line ~a is not an implication: ~a" l (show x))]))
(define (exel l k) (match (line l) [(list 'I P Gf) (L l k (Imp (Xf (ren (absk k) P)) Gf))]
                     [x (error 'exel "line ~a is not an implication: ~a" l (show x))]))
(define (exi f t) (E t (Imp (ren (scons t sid) f) (Xf f))))          ; f: the body under the existential
(define (xbody F) (match F [(list 'N (list 'A (list 'N b))) b] [_ (error 'xbody "not an existential: ~a" (show F))]))
(define (abody F) (match F [(list 'A b) b] [_ (error 'abody "not a universal: ~a" (show F))]))

;; the two statements as the kernel's texts parse them (Pure.v notch_text; GoedelCH.v ch_text)
;; notCH*: X w X x X y K K K K Om1 w A u I E u x Sub2 u w A u I E u y Sub2 u w N Le2 x w N Le2 y x
(define NOTCH-DSL
  '(ex w (ex x (ex y (and (pr Om w) (all u (imp (in u x) (pr Sub u w))) (all u (imp (in u y) (pr Sub u w)))
                          (not (pr Le x w)) (not (pr Le y x)))))))
;; CH:      A w A x A p I K K Om1 w A u Q E u p Sub2 u w Sub2 x p D Le2 x w Le2 p x
(define CH-DSL
  '(all w (all x (all p (imp (and (pr Om w) (all u (iff (in u p) (pr Sub u w))) (pr Sub x p))
                             (or (pr Le x w) (pr Le p x)))))))

;; Sub(y,p) -> (Le(p,x) -> Le(y,x))          y = 0, p = 1, x = 2: the same injection, total on the smaller set
(defgen LeSub (key)
  (begin-thm! key 3)
  (define f (fresh!)) (define d (fresh!))
  (define lsub (unfold 'Sub '(0 1)))
  (define ltp (unfold 'Tot (list f 1)))
  (define lty (unfold 'Tot (list f 0)))
  (define e (fresh-sym 'e))
  (define t1 (tt `(imp (and (pr Sub 0 1) (pr Tot ,f 1)) (imp (in ,d 0) (ex ,e (pr App ,f ,d ,e))))
                 lsub ltp (inst (def-body lsub) d) (inst (def-body ltp) d)))
  (define h1 (alli d t1))
  (define t2 (tt `(imp (and (pr Sub 0 1) (pr Tot ,f 1)) (pr Tot ,f 0)) lty h1))
  (define llp (unfold 'Le '(1 2)))
  (define lly (unfold 'Le '(0 2)))
  (define phi1 (xbody (def-body llp)))
  (define phi0 (xbody (def-body lly)))
  (define e1 (exi phi0 f))
  (define t3 (T (list t2 lly e1) (Imp (ren (scons f sid) phi1) (c '(imp (pr Sub 0 1) (pr Le 0 2))))))
  (define l4 (exel t3 f))
  (define g '(imp (pr Sub 0 1) (imp (pr Le 1 2) (pr Le 0 2))))
  (tt g llp l4)
  (end-thm! (c g) (ids 3)))

;; exists p forall u (u in p <-> Sub(u,w))     w = 0: the power set, from Power (entry 3) and a Separation instance
(defgen PowEx (key)
  (begin-thm! key 1)
  (define s1 (S (U 3 '()) '(0)))                       ; exists y forall z ((forall u (u in z -> u in w)) -> z in y)
  (define y0 (fresh!))
  (define Py (ren (scons y0 sid) (xbody (line s1))))
  (define sep (Y (SepF (Pr 5 '(0 2)))))                ; forall z exists y forall x (x in y <-> x in z & Sub(x,w))
  (define s2 (S sep (list y0)))
  (define p0 (fresh!))
  (define Qp (ren (scons p0 sid) (xbody (line s2))))
  (define u0 (fresh!))
  (define u (fresh-sym 'u))
  (define goal (c `(ex p (all ,u (iff (in ,u p) (pr Sub ,u 0))))))
  (define t1 (T (list (inst Qp u0) (inst Py u0) (unfold 'Sub (list u0 0)))
                (Imp (Kf Py Qp) (c `(iff (in ,u0 ,p0) (pr Sub ,u0 0))))))
  (define h1 (alli u0 t1))
  (define e1 (exi (xbody goal) p0))
  (define t2 (T (list h1 e1) (Imp Qp (Imp Py goal))))
  (define m1 (M s2 (exel t2 p0)))
  (M s1 (exel m1 y0))
  (end-thm! goal '(0)))

;; notCH* -> not CH                frame w = 0, x = 1, y = 2, p = 3 (the power set of w), u = 4
(defgen NotchPlain (key)
  (begin-thm! key 3)
  (define CH (c CH-DSL)) (define N0 (c NOTCH-DSL))
  (define p (fresh!)) (define u (fresh!))
  (define B (c '(and (pr Om 0) (all u (imp (in u 1) (pr Sub u 0))) (all u (imp (in u 2) (pr Sub u 0)))
                     (not (pr Le 1 0)) (not (pr Le 2 1)))))
  (define Pw (c `(all u (iff (in u ,p) (pr Sub u 0)))))
  (define pe (U 'PowEx '(0)))
  (define Ax (c '(all u (imp (in u 1) (pr Sub u 0)))))
  (define Ay (c '(all u (imp (in u 2) (pr Sub u 0)))))
  (define ip (inst Pw u))
  (define a1 (alli u (T (list (inst Ax u) ip) (Imp (Kf Ax Pw) (c `(imp (in ,u 1) (in ,u ,p)))))))
  (define a2 (alli u (T (list (inst Ay u) ip) (Imp (Kf Ay Pw) (c `(imp (in ,u 2) (in ,u ,p)))))))
  (define s13 (unfold 'Sub (list 1 p)))
  (define s23 (unfold 'Sub (list 2 p)))
  (define ls (U 'LeSub (list 2 p 1)))
  (define vs (inst* CH (list 0 1 p)))
  (define t (T (append (list a1 a2 s13 s23 ls) vs) (Imp Pw (Imp B (Neg CH)))))
  (define m (M pe (exel t p)))
  (define e2 (exel m 2)) (define e1 (exel e2 1)) (define e0 (exel e1 0))
  (unless (equal? (line e0) (Imp N0 (Neg CH))) (error 'NotchPlain "the last line is not notCH* -> not CH"))
  (end-thm! (Imp N0 (Neg CH)) '()))

;; not CH -> notCH*                frame w = 0, x = 1, p = 2, u = 3
(defgen PlainNotch (key)
  (begin-thm! key 3)
  (define CH (c CH-DSL)) (define N0 (c NOTCH-DSL))
  (define u (fresh!))
  ;; not notCH* -> not B(0,1,2): the three universal instances of not exists = forall not
  (define A1 (xbody N0))                                 ; under w
  (define a0 (V 0 (Imp (All (Neg A1)) (Neg (ren (scons 0 sid) A1)))))
  (define A2 (xbody (ren (scons 0 sid) A1)))
  (define a1 (V 1 (Imp (All (Neg A2)) (Neg (ren (scons 1 sid) A2)))))
  (define A3 (xbody (ren (scons 1 sid) A2)))
  (define a2 (V 2 (Imp (All (Neg A3)) (Neg (ren (scons 2 sid) A3)))))
  (define B012 (ren (scons 2 sid) A3))
  (define Pw (c `(all u (iff (in u 2) (pr Sub u 0)))))
  (define lsub (unfold 'Sub '(1 2)))
  (define ip (inst Pw u))
  (define h1 (alli u (T (list lsub (inst (def-body lsub) u) ip)
                        (Imp (Kf (c '(pr Sub 1 2)) Pw) (c `(imp (in ,u 1) (pr Sub ,u 0)))))))
  (define h2 (alli u (T (list ip) (Imp Pw (c `(imp (in ,u 2) (pr Sub ,u 0)))))))
  (define body (c `(imp (and (pr Om 0) ,`(all v (iff (in v 2) (pr Sub v 0))) (pr Sub 1 2)) (or (pr Le 1 0) (pr Le 2 1)))))
  (define t (T (list a0 a1 a2 h1 h2) (Imp (Neg N0) body)))
  (when (not (equal? B012 (c '(and (pr Om 0) (all u (imp (in u 1) (pr Sub u 0))) (all u (imp (in u 2) (pr Sub u 0)))
                                   (not (pr Le 1 0)) (not (pr Le 2 1))))))
    (error 'PlainNotch "instance mismatch"))
  (define g2 (alli 2 t)) (define g1 (alli 1 g2)) (define g0 (alli 0 g1))
  (unless (equal? (line g0) (Imp (Neg N0) CH)) (error 'PlainNotch "the generalized line is not not notCH* -> CH"))
  (T (list g0) (Imp (Neg CH) N0))
  (end-thm! (Imp (Neg CH) N0) '()))

;; notCH* <-> not CH
(defgen NotchIff (key)
  (begin-thm! key 0)
  (define CH (c CH-DSL)) (define N0 (c NOTCH-DSL))
  (T (list (U 'NotchPlain '()) (U 'PlainNotch '())) (Qf N0 (Neg CH)))
  (end-thm! (Qf N0 (Neg CH)) '()))

;; ======================================================================== commands
(define (build-lch keys)
  (reset-batch!)
  (define t0 (current-milliseconds))
  (for ([k keys]) (ensure! k))
  (define ths (reverse out-thms))
  (list (batch-text) (- (current-milliseconds) t0) (hash-copy stats) (map car ths) (map caddr ths)))

(define LAYERS
  (list (list "01-align" "notCH* <-> not CH (Theorem 29's statement against the plain CH of GoedelCH.v)"
              '(LeSub PowEx NotchPlain PlainNotch NotchIff)
              (lambda () (Qf (c NOTCH-DSL) (c CH-DSL))))))

(define (cmd-emit dir)
  (load-base!)
  (make-directory* (build-path dir "mut"))
  (for ([layer LAYERS])
    (match-define (list base what jobs twin) layer)
    (match-define (list text ms st keys pflags) (build-lch jobs))
    (define file (build-path dir (string-append base ".jdg")))
    (write-new file text)
    (define-values (rg ths) (read-jdg-text text))
    (printf "~a.jdg  ~a\n" base what)
    (printf "  theorems ~a, steps ~a, bytes ~a, build ~a ms, largest tautology test ~a calls\n"
            (length ths) (hash-ref st 'steps 0) (file-size file) ms (hash-ref st 'taut-max 0))
    (printf "  registry: ~a\n" (check-registry-text text))
    (printf "  copy of the checker: ~a\n" (check-batch rg ths))
    (write-new (build-path dir (string-append base ".index.txt"))
               (string-join (for/list ([k keys] [t ths] [i (in-naturals)]) (format "~a ~a ~a" i k (show (tof (car t))))) "\n"))
    (for ([m (mutants text (twin) pflags)])
      (match-define (list tag mtext) m)
      (define mf (build-path dir "mut" (string-append base "-" tag ".jdg")))
      (write-new mf mtext)
      (define-values (mrg mths) (read-jdg-text mtext))
      (printf "  mutant ~a: copy of the checker ~a\n" tag (check-batch mrg mths)))))

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

(module+ main
  (define args (vector->list (current-command-line-arguments)))
  (match args
    [(list "emit" dir) (cmd-emit dir)]
    [(list "judge" dir results) (cmd-judge dir results)]
    [_ (printf "usage: racket lch2.rkt emit DIR | judge DIR RESULTS\n")]))
