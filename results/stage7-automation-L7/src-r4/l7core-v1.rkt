#lang racket/base
;; l7core-v1.rkt -- lane L7 (Stage 7 of PMP-BUILDOUT-2026-10-09): the shared core of the L7 emitters.
;; A copy of sigma1.rkt (C:\ClaudeOutput\pompetzki\sigma1\sigma1.rkt, sha256 7d3ff29c...3337): formulas, JDG1 reading and
;; writing, the copy of Replay2.v's step semantics and check_batch, the registry (the first 677 entries of replay-all.jdg),
;; the prelude import, lemmas on demand, the tactics, the mutants, the registry check against RpInit.v and the judge runner.
;; Changes against the copy: PNAME and SYM name more registered symbols; everything is exported; the L7 additions at the
;; end (replay names, natural-deduction macros, the vacuous box, Hilbert steps, lemma!, emit-file!).
;; Not trusted: every file is checked by judge-v3.pmp under pompetzki.exe and by racket/judge.rkt.
(provide (all-defined-out))
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
(define PNAME (hash 5 "Sub" 6 "Sng" 7 "Upr" 8 "Opr" 9 "App" 10 "Fnc" 11 "Inj" 12 "Tot" 13 "Rng" 15 "Tr" 16 "Ord" 17 "Emp" 18 "Suc" 19 "Ind" 20 "Om" 72 "Nat"))
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
(define SYM (hash 'Sub 5 'Sng 6 'Upr 7 'Opr 8 'App 9 'Fnc 10 'Inj 11 'Tot 12 'Rng 13 'Tr 15 'Ord 16 'Emp 17 'Suc 18 'Ind 19 'Om 20 'Nat 72))
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


;; ======================================================================== L7 additions (2026-10-09)
;; replay theorem names, read from the comments "(* NAME *) Thm" of RpB0.v .. RpB10.v, in order
(define REPLAY-SRC "C:/ClaudeOutput/pompetzki/forcing-src/general")
(define replay-name-vec #f)
(define (replay-names)
  (unless replay-name-vec
    (set! replay-name-vec
          (list->vector
           (apply append (for/list ([b (in-range 11)])
                           (regexp-match* #px"\\(\\* ([^ ]+) \\*\\) Thm" (file->string (format "~a/RpB~a.v" REPLAY-SRC b))
                                          #:match-select cadr))))))
  replay-name-vec)
(define (replay-index name)
  (or (for/first ([n (replay-names)] [i (in-naturals)] #:when (equal? n name)) i)
      (error 'replay-index "no replay theorem ~a" name)))
;; a hypothesis-free replay theorem, copied into the batch with its dependencies; its key is the string name
(define (rp name)
  (cond [(hash-ref names name #f) => values]
        [else (define r (import-replay! (replay-index name))) (hash-set! names name r) r]))
(define (rp-line name args) (S (U (rp name) '()) args))

;; ---- natural-deduction macros on lines (item 3)
;; line l: h -> f, k not free in h            ==> h -> forall f'      (f' = f with k bound)
(define (fa-i k l)
  (match (line l) [(list 'I h f) (H k l (Imp h (All (ren (absk k) f))))]
    [f (G l k)]))
;; line l: p -> g, k not free in g            ==> (exists p') -> g
(define (ex-e k l)
  (match (line l) [(list 'I p g) (L l k (Imp (Xf (ren (absk k) p)) g))]))
;; line l: forall f  ==> f[t];   line l: h -> forall f  ==> h -> f[t]
(define (fa-e l t)
  (match (line l)
    [(list 'A f) (S l (list t))]
    [(list 'I h (list 'A f))
     (define v (V t (Imp (All f) (ren (scons t sid) f))))
     (T (list l v) (Imp h (ren (scons t sid) f)))]))
;; f[t] -> exists f, for an existential core formula ex = Xf f
(define (ex-i t ex)
  (match ex [(list 'N (list 'A (list 'N f))) (E t (Imp (ren (scons t sid) f) ex))]))
;; the vacuous box: B(f) = forall f^ (f shifted up). Y gives f -> B(f), V gives B(f) -> f. To the Shannon test B(f) is one atom.
(define (box f) (All (ren add1 f)))
(define (box-in f) (Y (Imp f (box f))))
(define (box-out f) (V 0 (Imp (box f) f)))

;; Hilbert steps without the tautology test (Y = axiom shapes K, S; M)
(define (ax-k a b) (Y (Imp a (Imp b a))))
(define (ax-s a b c) (Y (Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c)))))
;; from lines l1: a -> b and l2: b -> c, the line a -> c, by K, S and three M (no Shannon expansion)
(define (hsyl l1 l2)
  (match* ((line l1) (line l2))
    [((list 'I a b) (list 'I b2 c))
     (unless (equal? b b2) (error 'hsyl "middle formulas differ"))
     (define k (ax-k (Imp b c) a))
     (define m1 (M l2 k))
     (define s (ax-s a b c))
     (define m2 (M m1 s))
     (M l1 m2)]))

;; ---- a lemma: frame variables 0..n-1 free in its statement; the thunk returns the final line
(define (lemma! key n thunk)
  (begin-thm! key n)
  (define l (thunk))
  (end-thm! (line l) (ids n)))
;; use a lemma (theorem key) with its free variables 0..k-1 renamed to the frame variables args
(define (use key args) (U key args))

;; ---- emitting one file with index, manifest lines and mutants
;; build: a thunk that adds the theorems; twin: a false core statement for the twin-final mutant, or #f
(define (emit-file! dir base what build twin)
  (reset-batch!)
  (make-directory* (build-path dir "mut"))
  (define t0 (current-milliseconds))
  (build)
  (define ms (- (current-milliseconds) t0))
  (define ths0 (reverse out-thms))
  (define keys (map car ths0))
  (define pflags (map caddr ths0))
  (define text (batch-text))
  (define st (hash-copy stats))
  (define file (build-path dir (string-append base ".jdg")))
  (write-new file text)
  (define-values (rg ths) (read-jdg-text text))
  (define notes '())
  (define (note! . xs) (set! notes (cons (apply format xs) notes)) (printf "~a\n" (car notes)) (flush-output))
  (note! "~a.jdg  ~a" base what)
  (note! "  theorems ~a (prelude ~a, generated ~a), steps ~a (prelude ~a), bytes ~a, build ~a ms, largest tautology test ~a calls, all tautology tests ~a calls"
         (length ths) (hash-ref st 'prelude 0) (hash-ref st 'theorems 0)
         (+ (hash-ref st 'steps 0) (hash-ref st 'prelude-steps 0)) (hash-ref st 'prelude-steps 0)
         (file-size file) ms (hash-ref st 'taut-max 0) (hash-ref st 'taut-calls 0))
  (note! "  sha256 ~a" (sha256-hex file))
  (note! "  registry: ~a" (check-registry-text text))
  (note! "  copy of the checker: ~a" (check-batch rg ths))
  (write-new (build-path dir (string-append base ".index.txt"))
             (string-join (for/list ([k keys] [t ths] [i (in-naturals)])
                            (format "~a ~s ~a" i k (if (and (pair? k) (eq? (car k) 'replay)) "" (show (tof (car t))))))
                          "\n"))
  (for ([m (mutants text (or twin (Neg (tof (car (last ths))))) pflags)])
    (match-define (list tag mtext) m)
    (define mf (build-path dir "mut" (string-append base "-" tag ".jdg")))
    (write-new mf mtext)
    (define-values (mrg mths) (read-jdg-text mtext))
    (note! "  mutant ~a: copy of the checker ~a" tag (check-batch mrg mths)))
  (reverse notes))

;; ---- the replay's statements, readable
(define (dump-replay from to)
  (load-base!)
  (for ([i (in-range from to)])
    (match-define (list st sig steps hyps) (vector-ref replay-thms i))
    (printf "~a ~a hyps ~a steps ~a: ~a\n" i (vector-ref (replay-names) i) hyps (length steps) (show (tof st)))))
