#lang racket/base
;; lch10.rkt -- lch9.rkt with one closing parenthesis fewer on the twin statement of layer 05 (lch9.rkt does not read).
;; lch9.rkt -- lch6.rkt (layers 01-04) with layer 05: coherence of two hierarchies (lch-part-L3.rkt.txt with two
;; corrections at assembly: CohBM's backward witness pair and symmetry instance, and one missing closing parenthesis
;; at the end of CohBM's statement). lch6.rkt, lch7.rkt and lch8.rkt are not changed.
;; lch6.rkt -- lane LCH round 2 (orders of 18:5x, 2026-10-09): Goedel's half, the single obligations.
;; (lch6.rkt = lch5.rkt with LTr's instantiated clause read through two implications; lch5.rkt stopped there.)
;;   O0: the class L as one formula over ZB_BASE symbols (lch-part-L.rkt.txt).
;;   Layer 03 (O1): exists x L(x).   Layer 04 (O2): L is transitive, i.e. HT 0 = HT 5 of LAXred2.v for L.
;; Body of lch4.rkt (lines 2-981, layers 01 and 02) unchanged; lch4.rkt and sigma1.rkt are not changed.
;; Usage: racket lch5.rkt emit DIR | judge DIR RESULTS | info
;; Exact integers only.
;; lch4.rkt -- lane LCH of the release-day orders 2026-10-09: ZF derivations, in the judge's format JDG1, for Goedel's
;; (lch4.rkt = lch3.rkt with close-rel-alls emitting no restructuring tautology when no guard is left in front: in
;;  lch3.rkt the last step of such a theorem repeated the previous line, so the drop-step mutant was still a proof.)
;; half of the independence of CH.
;;   Layer 01: the alignment of Theorem 29's notCH* with the plain CH of GoedelCH.v: notCH* <-> not CH (as lch2.rkt).
;;   Layer 02: relativized axioms for a schematic class M (symbol 5000): Ext, Pair, Union, Power, Inf, Found relativized
;;             to M follow from M transitive and M closed under pairs, unions, power covers, with an inductive set in M.
;; Not trusted; both judges check every file. Formula code, checker copy, JDG1 reader/writer, registry loader, mutants
;; and judge runner are copied verbatim from sigma1/sigma1.rkt (see lch2.rkt); lch2.rkt and sigma1.rkt are not changed.
;; Usage:
;;   racket lch4.rkt emit DIR             write DIR/01-align.jdg, DIR/02-relax.jdg, their indexes and DIR/mut/*.jdg
;;   racket lch4.rkt judge DIR RESULTS    run both judges on DIR/*.jdg and DIR/mut/*.jdg, write RESULTS (a new file)
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

;; ======================================================================== lane LCH, layer 02: relativized axioms
;; A class is the schematic predicate symbol 5000 of arity 1 (M), defined nowhere: a theorem about it holds for every
;; class formula by uniform substitution (Prov.prov_psub; Gam's definitions do not mention 5000). relf is Rel2.rel with
;; M = M(v0): every All a becomes All (M -> a). Each theorem is  H -> relf (axiom i)  with H a plain property of M.
(define MS 5000)
(define (Mf x) (Pr MS (list x)))
(define MCL (Mf 0))
(define (relf f)
  (match f
    [(list 'A a) (All (Imp MCL (relf a)))]
    [(list 'N a) (Neg (relf a))]
    [(list 'I a b) (Imp (relf a) (relf b))]
    [_ f]))
(define (conj* fs) (for/fold ([acc (car fs)]) ([g (cdr fs)]) (Kf acc g)))
(define (chain-imp hs g) (foldr Imp g hs))
(define (rhs F) (match F [(list 'I _ q) q]))
(define (kparts F) (match F [(list 'N (list 'I a (list 'N b))) (values a b)] [_ (error 'kparts "not a conjunction: ~a" (show F))]))
(define TRC-DSL '(all x (all y (imp (pr M y) (imp (in x y) (pr M x))))))   ; M is transitive

;; line l: H -> M(v1) -> .. -> M(vn) -> X; result: H -> All (M -> .. All (M -> X')), the relativized universals
(define (close-rel-alls l H vars)
  (let loop ([l l] [vs vars])
    (if (null? vs) l
        (let* ([vk (last vs)] [front (drop-right vs 1)]
               [X (let peel ([F (rhs (line l))] [k (length front)])
                    (if (= k 0) (match F [(list 'I _ q) q]) (peel (rhs F) (sub1 k))))]
               [C (conj* (cons H (map Mf front)))]
               [t (if (null? front) l (T (list l) (Imp C (Imp (Mf vk) X))))]
               [a (alli vk t)]
               [Yf (rhs (line a))])
          (if (null? front) a
              (loop (T (list a) (Imp H (chain-imp (map Mf front) Yf))) front))))))
(define (rexi a t)
  (define v (V t (Imp (All (Imp MCL (Neg a))) (ren (scons t sid) (Imp MCL (Neg a))))))
  (T (list v) (Imp (Kf (Mf t) (ren (scons t sid) a)) (Neg (All (Imp MCL (Neg a)))))))
;; F = All phi: F -> All (M -> phi), u a fresh frame variable
(define (weaken-all F u)
  (define i (inst F u))
  (alli u (T (list i) (Imp F (Imp (Mf u) (rhs (line i)))))))
(define (check-final! who l goal)
  (unless (equal? (line l) goal)
    (eprintf "~a: the last line\n  ~a\nis not\n  ~a\n" who (show (line l)) (show goal))
    (error who "the last line is not the statement")))

;; Ext: M transitive -> Ext^M
(defgen RelExt (key)
  (begin-thm! key 0)
  (define TRC (c TRC-DSL)) (define GOAL (Imp TRC (relf (reg-stmt 0))))
  (define x (fresh!)) (define y (fresh!)) (define z (fresh!))
  (define R (c `(all u (imp (pr M u) (iff (in u ,x) (in u ,y))))))
  (define t1 (T (append (inst* TRC (list z x)) (inst* TRC (list z y)) (list (inst R z)))
                (Imp (conj* (list TRC (Mf x) (Mf y) R)) (c `(iff (in ,z ,x) (in ,z ,y))))))
  (define a1 (alli z t1))
  (define ex (S (U 0 '()) (list x y)))
  (define t2 (T (list a1 ex) (Imp TRC (chain-imp (list (Mf x) (Mf y) R) (Eqv x y)))))
  (define f (close-rel-alls t2 TRC (list x y)))
  (check-final! 'RelExt f GOAL)
  (end-thm! GOAL '()))

;; Pair: M closed under pairs {x,y} -> Pair^M
(defgen RelPair (key)
  (begin-thm! key 0)
  (define H (c '(all x (all y (imp (pr M x) (imp (pr M y) (ex z (and (pr M z) (all u (iff (in u z) (or (eq u x) (eq u y))))))))))))
  (define GOAL (Imp H (relf (reg-stmt 1))))
  (define x (fresh!)) (define y (fresh!)) (define z (fresh!))
  (define hl (inst* H (list x y)))
  (define Uz (c `(all u (iff (in u ,z) (or (eq u ,x) (eq u ,y))))))
  (define Pz (Kf (Mf z) Uz))
  (define a (Kf (Mem (add1 x) 0) (Mem (add1 y) 0)))
  (define Gx (Neg (All (Imp MCL (Neg a)))))
  (define t1 (T (list (inst Uz x) (inst Uz y) (Y (Eqv x x)) (Y (Eqv y y)) (rexi a z)) (Imp Pz Gx)))
  (define e1 (exel t1 z))
  (define t2 (T (append hl (list e1)) (Imp H (chain-imp (list (Mf x) (Mf y)) Gx))))
  (define f (close-rel-alls t2 H (list x y)))
  (check-final! 'RelPair f GOAL)
  (end-thm! GOAL '()))

;; Union: M closed under unions -> Union^M
(defgen RelUnion (key)
  (begin-thm! key 0)
  (define H (c '(all f (imp (pr M f) (ex a (and (pr M a) (all x (iff (in x a) (ex y (and (in y f) (in x y)))))))))))
  (define GOAL (Imp H (relf (reg-stmt 2))))
  (define f (fresh!)) (define a (fresh!)) (define y (fresh!)) (define x (fresh!))
  (define hl (inst H f))
  (define U1 (c `(all x (iff (in x ,a) (ex yy (and (in yy ,f) (in x yy)))))))
  (define ey (exi (xbody (c `(ex yy (and (in yy ,f) (in ,x yy))))) y))
  (define t1 (T (list (inst U1 x) ey) (Imp U1 (Imp (Kf (Mem x y) (Mem y f)) (Mem x a)))))
  (define t2 (T (list t1) (Imp U1 (chain-imp (list (Mf y) (Mf x)) (Imp (Kf (Mem x y) (Mem y f)) (Mem x a))))))
  (define c2 (close-rel-alls t2 U1 (list y x)))
  (define Ip (ren (absk a) (rhs (line c2))))
  (define Gx (Neg (All (Imp MCL (Neg Ip)))))
  (define t3 (T (list c2 (rexi Ip a)) (Imp (Kf (Mf a) U1) Gx)))
  (define e1 (exel t3 a))
  (define t4 (T (list hl e1) (Imp H (Imp (Mf f) Gx))))
  (define fin (close-rel-alls t4 H (list f)))
  (check-final! 'RelUnion fin GOAL)
  (end-thm! GOAL '()))

;; Power: M transitive, and for x in M some y in M holds every subset of x that is in M -> Power^M
(defgen RelPower (key)
  (begin-thm! key 0)
  (define TRC (c TRC-DSL))
  (define PC (c '(all x (imp (pr M x) (ex y (and (pr M y) (all z (imp (pr M z) (imp (all u (imp (in u z) (in u x))) (in z y))))))))))
  (define H (Kf TRC PC))
  (define GOAL (Imp H (relf (reg-stmt 3))))
  (define x (fresh!)) (define y (fresh!)) (define z (fresh!)) (define u (fresh!))
  (define hp (inst PC x))
  (define W1 (c `(all z (imp (pr M z) (imp (all u (imp (in u z) (in u ,x))) (in z ,y))))))
  (define R2 (c `(all u (imp (pr M u) (imp (in u ,z) (in u ,x))))))
  (define t1 (T (append (inst* TRC (list u z)) (list (inst R2 u))) (Imp (conj* (list TRC (Mf z) R2)) (Imp (Mem u z) (Mem u x)))))
  (define a1 (alli u t1))
  (define t2 (T (list a1 (inst W1 z)) (Imp (Kf TRC W1) (chain-imp (list (Mf z)) (Imp R2 (Mem z y))))))
  (define c2 (close-rel-alls t2 (Kf TRC W1) (list z)))
  (define Ip (ren (absk y) (rhs (line c2))))
  (define Gx (Neg (All (Imp MCL (Neg Ip)))))
  (define t3 (T (list c2 (rexi Ip y)) (Imp (Kf (Mf y) W1) (Imp TRC Gx))))
  (define e1 (exel t3 y))
  (define t4 (T (list hp e1) (Imp H (Imp (Mf x) Gx))))
  (define fin (close-rel-alls t4 H (list x)))
  (check-final! 'RelPower fin GOAL)
  (end-thm! GOAL '()))

;; Inf: M transitive and some inductive set (Infinity's body, unrelativized) is in M -> Inf^M
(defgen RelInf (key)
  (begin-thm! key 0)
  (define TRC (c TRC-DSL))
  (define AXI (reg-stmt 4))
  (define IB (xbody AXI))
  (define InfC (Xf (Kf MCL IB)))
  (define H (Kf TRC InfC))
  (define GOAL (Imp H (relf AXI)))
  (define w (fresh!)) (define e (fresh!)) (define y (fresh!)) (define s (fresh!)) (define u (fresh!))
  (define-values (Ee S0) (kparts IB))
  ;; the empty set e in w
  (define Eb (xbody Ee))
  (define Ebe (ren (scons e sid) Eb))
  (define-values (Emp-e e-in-w) (kparts Ebe))
  (define Goal-e (relf Ee))
  (define t1 (T (append (inst* TRC (list e w)) (list (weaken-all Emp-e u) (rexi (relf Eb) e)))
                (Imp (Kf (Kf TRC (Mf w)) Ebe) Goal-e)))
  (define e1 (exel (T (list t1) (Imp Ebe (Imp (Kf TRC (Mf w)) Goal-e))) e))
  ;; every y in w has its successor s in w
  (define iS (inst S0 y))
  (define Sy (rhs (rhs (line iS))))
  (define Sb (xbody Sy))
  (define Sbs (ren (scons s sid) Sb))
  (define-values (Sc s-in-w) (kparts Sbs))
  (define Goal-s (relf Sy))
  (define t2 (T (append (inst* TRC (list s w)) (list (weaken-all Sc u) (rexi (relf Sb) s)))
                (Imp (Kf (Kf TRC (Mf w)) Sbs) Goal-s)))
  (define e2 (exel (T (list t2) (Imp Sbs (Imp (Kf TRC (Mf w)) Goal-s))) s))
  (define t3 (T (list iS e2) (Imp (Kf (Kf TRC (Mf w)) S0) (Imp (Mf y) (Imp (Mem y w) Goal-s)))))
  (define a3 (alli y t3))
  (define SuccM (rhs (line a3)))
  (define t4 (T (list e1 a3) (Imp (Kf (Kf TRC (Mf w)) (Kf Ee S0)) (Kf Goal-e SuccM))))
  (define t5 (T (list t4 (rexi (relf IB) w)) (Imp (Kf (Mf w) (Kf Ee S0)) (Imp TRC (relf AXI)))))
  (define e5 (exel t5 w))
  (define fin (T (list e5) GOAL))
  (check-final! 'RelInf fin GOAL)
  (end-thm! GOAL '()))

;; Found: M transitive -> Found^M
(defgen RelFound (key)
  (begin-thm! key 0)
  (define TRC (c TRC-DSL))
  (define AXF (reg-stmt 5))
  (define GOAL (Imp TRC (relf AXF)))
  (define x (fresh!)) (define y (fresh!)) (define z (fresh!))
  (define fi (S (U 5 '()) (list x)))
  (define Ante (match (line fi) [(list 'I a _) a])) (define Conc (rhs (line fi)))
  (define RAnte (relf Ante))
  (define t1 (T (list (weaken-all (All (Neg (Mem 0 (add1 x)))) y)) (Imp RAnte Ante)))
  (define Cb (xbody Conc))
  (define Cby (ren (scons y sid) Cb))
  (define-values (y-in-x NZ) (kparts Cby))
  (define Zall (match NZ [(list 'N (list 'N q)) q] [_ (error 'RelFound "shape ~a" (show NZ))]))
  (define GOALc (relf Conc))
  (define t2 (T (append (inst* TRC (list y x)) (list (weaken-all Zall z) (rexi (relf Cb) y)))
                (Imp (Kf (Kf TRC (Mf x)) Cby) GOALc)))
  (define e2 (exel (T (list t2) (Imp Cby (Imp (Kf TRC (Mf x)) GOALc))) y))
  (define t3 (T (list fi t1 e2) (Imp TRC (Imp (Mf x) (Imp RAnte GOALc)))))
  (define fin (close-rel-alls t3 TRC (list x)))
  (check-final! 'RelFound fin GOAL)
  (end-thm! GOAL '()))

;; ======================================================================== lane LCH round 2: the constructible universe
;; O0. The class L as one formula over the ZB_BASE symbols (all of them unfold by Pure.pi to the pure language):
;;   Gödel's operations (Jech, Set Theory, 13.7; triples (u,v,w) = ((u,v),w)):
;;     G1 {a,b}   G2 a x b   G3 {t in a : t = (u,v), u in v}   G4 a - b   G5 a n b   G6 U a   G7 dom a
;;     G8 {(u,v) : (v,u) in a}   G9 {(u,v,w) : (u,w,v) in a}   G10 {(u,v,w) : (v,w,u) in a}
;;   Clo(C): C is closed under G1..G10.
;;   D(A) = {X subset of A : X in every C with Clo(C), A subset of C, A in C} = cl(A u {A}) n P(A)   (Jech 13.8: = def(A))
;;   Lev(s): s is a function, total on an ordinal d, every argument of s is in d, and
;;           s(b) = D(U_b) with U_b = the union of s(g) for g in b
;;   L(x):   some Lev(s) has x in one of its values.         VL: forall x L(x).
;; With M_b = s(b) one has M_b = L_(b+1) of the usual hierarchy, so the union is L.
(define (fs b) (fresh-sym b))
(define (BM s b z)                       ; z in U_b
  (let ([g (fs 'g)] [w (fs 'w)]) `(ex ,g (and (in ,g ,b) (ex ,w (and (pr App ,s ,g ,w) (in ,z ,w)))))))
(define (trip t u v w) (let ([p (fs 'p)]) `(ex ,p (and (pr Opr ,p ,u ,v) (pr Opr ,t ,p ,w)))))
(define (Gop i z a b)
  (define t (fs 't)) (define u (fs 'u)) (define v (fs 'v)) (define w (fs 'w)) (define q (fs 'q)) (define y (fs 'y))
  (case i
    [(1) `(pr Upr ,z ,a ,b)]
    [(2) `(all ,t (iff (in ,t ,z) (ex ,u (ex ,v (and (in ,u ,a) (in ,v ,b) (pr Opr ,t ,u ,v))))))]
    [(3) `(all ,t (iff (in ,t ,z) (and (in ,t ,a) (ex ,u (ex ,v (and (pr Opr ,t ,u ,v) (in ,u ,v)))))))]
    [(4) `(all ,t (iff (in ,t ,z) (and (in ,t ,a) (not (in ,t ,b)))))]
    [(5) `(all ,t (iff (in ,t ,z) (and (in ,t ,a) (in ,t ,b))))]
    [(6) `(all ,t (iff (in ,t ,z) (ex ,y (and (in ,y ,a) (in ,t ,y)))))]
    [(7) `(all ,t (iff (in ,t ,z) (ex ,v (ex ,q (and (in ,q ,a) (pr Opr ,q ,t ,v))))))]
    [(8) `(all ,t (iff (in ,t ,z) (ex ,u (ex ,v (and (pr Opr ,t ,u ,v) (ex ,q (and (in ,q ,a) (pr Opr ,q ,v ,u))))))))]
    [(9) `(all ,t (iff (in ,t ,z) (ex ,u (ex ,v (ex ,w (and ,(trip t u v w) (ex ,q (and (in ,q ,a) ,(trip q u w v)))))))))]
    [(10) `(all ,t (iff (in ,t ,z) (ex ,u (ex ,v (ex ,w (and ,(trip t u v w) (ex ,q (and (in ,q ,a) ,(trip q v w u)))))))))]))
(define (bal xs)                          ; balanced conjunction, to keep the formula shallow
  (cond [(null? (cdr xs)) (car xs)]
        [else (let-values ([(l r) (split-at xs (quotient (length xs) 2))]) `(and ,(bal l) ,(bal r)))]))
(define (Clo C)
  (define a (fs 'a)) (define b (fs 'b))
  `(all ,a (all ,b (imp (in ,a ,C) (imp (in ,b ,C)
     ,(bal (for/list ([i (in-range 1 11)]) (let ([z (fs 'z)]) `(ex ,z (and (in ,z ,C) ,(Gop i z a b)))))))))))
(define (Step s b v)
  (define X (fs 'X)) (define z (fs 'z)) (define C (fs 'C)) (define u (fs 'u)) (define z2 (fs 'z)) (define z3 (fs 'z))
  `(all ,X (iff (in ,X ,v)
                (and (all ,z (imp (in ,z ,X) ,(BM s b z)))
                     (all ,C (imp ,(Clo C) (imp (all ,z2 (imp ,(BM s b z2) (in ,z2 ,C)))
                                                (imp (ex ,u (and (in ,u ,C) (all ,z3 (iff (in ,z3 ,u) ,(BM s b z3)))))
                                                     (in ,X ,C)))))))))
(define (Lev s)
  (define d (fs 'd)) (define b (fs 'b)) (define v (fs 'v))
  `(and (pr Fnc ,s) (ex ,d (and (pr Ord ,d) (pr Tot ,s ,d)
                                (all ,b (all ,v (imp (pr App ,s ,b ,v) (and (in ,b ,d) ,(Step s b v)))))))))
(define (Ldsl x)
  (define s (fs 's)) (define b (fs 'b)) (define v (fs 'v))
  `(ex ,s (and ,(Lev s) (ex ,b (ex ,v (and (pr App ,s ,b ,v) (in ,x ,v)))))))
;; the class formula, variable 0 free, and V = L
(define (LF) (c (Ldsl 0)))
(define (VLF) (c (let ([x (fs 'x)]) `(all ,x ,(Ldsl x)))))
(define (fdepth f)
  (match f [(list (or 'E 'Q 'P) _ _) 1] [(list (or 'N 'A) a) (add1 (fdepth a))] [(list 'I a b) (add1 (max (fdepth a) (fdepth b)))]))
;; ======================================================================== lane LCH round 2: O1 (L is not empty), O2 (L transitive)
(define (rp i) (import-replay! i))                    ; a theorem of Theorem 29's replay, copied in with its dependencies
(define (sp i ts) (S (U (rp i) '()) ts))              ; replay theorem i, its universals at ts
(define (sk key ts) (S (U key '()) ts))               ; own theorem by key, its universals at ts
;; replay: 0 EqSym (x=y -> y=x), 1 EqTr, 3 SngEx, 6 OprEx, 7 SngIn, 8 SngMem, 14 Kur1, 15 Kur2, 31 MemApp, 33 EmpUq
(define (close-frame! l vars stmt who)
  (define fin (for/fold ([cur l]) ([v (reverse vars)]) (G cur v)))
  (check-final! who fin stmt)
  (end-thm! stmt '()))

;; exists x Emp(x), from the axiom of infinity (registry entry 4); as sigma1.rkt's EmpEx
(defgen EmpEx (key)
  (begin-thm! key 2)
  (define ax (U 4 '()))
  (define body (match (line ax) [(list 'N (list 'A (list 'N b))) b]))
  (define e1 (match body [(list 'N (list 'I (list 'N (list 'A (list 'N e1b))) _)) e1b]))
  (define ed (unfold 'Emp '(1)))
  (define goal (c (let ([x (fresh-sym 'x)]) `(ex ,x (pr Emp ,x)))))
  (define l2 (E 1 (Imp (Pr 17 '(1)) goal)))
  (define P (ren (scons 1 sid) e1))
  (define l3 (T (list ed l2) (Imp P goal)))
  (define l4 (L l3 1 (Imp (Neg (All (Neg e1))) goal)))
  (define l5 (T (list l4) (Imp body goal)))
  (define l6 (L l5 0 (Imp (line ax) goal)))
  (M ax l6)
  (end-thm! goal '()))

;; NBM: forall s b z (Emp(b) -> not z in U_b(s))
(defgen NBM (key)
  (begin-thm! key 3)
  (define g (fresh!))
  (define BMf (c (BM 0 1 2)))
  (define Gg (ren (scons g sid) (xbody BMf)))
  (define emp (unfold 'Emp '(1)))
  (define t1 (T (list emp (inst (def-body emp) g)) (Imp Gg (Neg (Pr 17 '(1))))))
  (define e1 (exel t1 g))
  (define t2 (T (list e1) (Imp (Pr 17 '(1)) (Neg BMf))))
  (close-frame! t2 '(0 1 2) (c `(all s (all b (all z (imp (pr Emp b) (not ,(BM 's 'b 'z))))))) 'NBM))

;; AppSng: forall e v p s (Opr(p,e,v) -> Sng(s,p) -> forall a b (App(s,a,b) -> a = e & b = v))
(defgen AppSng (key)
  (begin-thm! key 6)
  (define q (fresh!))
  (define la (unfold 'App '(3 4 5)))
  (define Qq (ren (scons q sid) (xbody (def-body la))))
  (define t1 (T (list (sp 8 (list 3 2 q)) (leib `(pr Opr ,HOLE 4 5) q 2) (sp 14 '(2 4 5 0 1)) (sp 15 '(2 4 5 0 1)))
                (Imp Qq (c '(imp (pr Opr 2 0 1) (imp (pr Sng 3 2) (and (eq 4 0) (eq 5 1))))))))
  (define e1 (exel t1 q))
  (define t2 (T (list la e1) (c '(imp (and (pr Opr 2 0 1) (pr Sng 3 2)) (imp (pr App 3 4 5) (and (eq 4 0) (eq 5 1)))))))
  (define a5 (alli 5 t2)) (define a4 (alli 4 a5))
  (define t3 (T (list a4) (c '(imp (pr Opr 2 0 1) (imp (pr Sng 3 2) (all a (all b (imp (pr App 3 a b) (and (eq a 0) (eq b 1))))))))))
  (close-frame! t3 '(0 1 2 3)
                (c '(all e (all v (all p (all s (imp (pr Opr p e v) (imp (pr Sng s p) (all a (all b (imp (pr App s a b) (and (eq a e) (eq b v))))))))))))
                'AppSng))

;; AppS: forall e v p s (Opr(p,e,v) -> Sng(s,p) -> App(s,e,v))
(defgen AppS (key)
  (begin-thm! key 4)
  (define t (T (list (sp 7 '(3 2)) (sp 31 '(3 0 1 2))) (c '(imp (pr Opr 2 0 1) (imp (pr Sng 3 2) (pr App 3 0 1))))))
  (close-frame! t '(0 1 2 3) (c '(all e (all v (all p (all s (imp (pr Opr p e v) (imp (pr Sng s p) (pr App s e v)))))))) 'AppS))

;; FncS: forall e v p s (Opr(p,e,v) -> Sng(s,p) -> Fnc(s))
(defgen FncS (key)
  (begin-thm! key 7)
  (define ls (inst* (abody (abody (rhs (rhs (line (sk 'AppSng '(0 1 2 3))))))) '()))
  (define as (sk 'AppSng '(0 1 2 3)))
  (define AB (rhs (rhs (line as))))                     ; forall a b (App(3,a,b) -> a = 0 & b = 1)
  (define i1 (inst* AB '(4 5))) (define i2 (inst* AB '(4 6)))
  (define fd (unfold 'Fnc '(3)))
  (define t1 (T (append (list as) i1 i2 (list (sp 0 '(6 1)) (sp 1 '(5 1 6))))
                (c '(imp (pr Opr 2 0 1) (imp (pr Sng 3 2) (imp (and (pr App 3 4 5) (pr App 3 4 6)) (eq 5 6)))))))
  (define t2 (T (list t1) (c '(imp (and (pr Opr 2 0 1) (pr Sng 3 2)) (imp (and (pr App 3 4 5) (pr App 3 4 6)) (eq 5 6))))))
  (define a6 (alli 6 t2)) (define a5 (alli 5 a6)) (define a4 (alli 4 a5))
  (define t3 (T (list a4 fd) (c '(imp (pr Opr 2 0 1) (imp (pr Sng 3 2) (pr Fnc 3))))))
  (close-frame! t3 '(0 1 2 3) (c '(all e (all v (all p (all s (imp (pr Opr p e v) (imp (pr Sng s p) (pr Fnc s)))))))) 'FncS))

;; OrdSng: forall e v (Emp(e) -> Sng(v,e) -> Ord(v))
(defgen OrdSng (key)
  (begin-thm! key 2)
  (define emp (unfold 'Emp '(0)))
  (define ie2 (inst (def-body emp) 2))
  (define tr (unfold 'Tr '(1)))
  (define t1 (T (list (sp 8 '(1 0 3)) (leib `(in 2 ,HOLE) 3 0) emp ie2)
                (c '(imp (and (pr Emp 0) (pr Sng 1 0)) (imp (and (in 2 3) (in 3 1)) (in 2 1))))))
  (define a3 (alli 3 t1)) (define a2 (alli 2 a3))
  (define t2 (T (list a2 tr) (c '(imp (and (pr Emp 0) (pr Sng 1 0)) (pr Tr 1)))))
  (define od (unfold 'Ord '(1)))
  (define t3 (T (list (sp 8 '(1 0 2)) (sp 8 '(1 0 3)) (sp 0 '(3 0)) (sp 1 '(2 0 3)))
                (c '(imp (and (pr Emp 0) (pr Sng 1 0)) (imp (and (in 2 1) (in 3 1)) (or (or (in 2 3) (eq 2 3)) (in 3 2)))))))
  (define b3 (alli 3 t3)) (define b2 (alli 2 b3))
  (define t4 (T (list t2 b2 od) (c '(imp (pr Emp 0) (imp (pr Sng 1 0) (pr Ord 1))))))
  (close-frame! t4 '(0 1) (c '(all e (all v (imp (pr Emp e) (imp (pr Sng v e) (pr Ord v)))))) 'OrdSng))

;; TotS: forall e v p s (Sng(v,e) -> Opr(p,e,v) -> Sng(s,p) -> Tot(s,v))
(defgen TotS (key)
  (begin-thm! key 5)
  (define y (fresh-sym 'y))
  (define ex (exi (xbody (c `(ex ,y (pr App 3 4 ,y)))) 1))
  (define t1 (T (list (sk 'AppS '(0 1 2 3)) (sp 8 '(1 0 4)) (sp 0 '(4 0)) (leib `(pr App 3 ,HOLE 1) 0 4) ex)
                (c `(imp (and (pr Sng 1 0) (pr Opr 2 0 1) (pr Sng 3 2)) (imp (in 4 1) (ex ,y (pr App 3 4 ,y)))))))
  (define a4 (alli 4 t1))
  (define td (unfold 'Tot '(3 1)))
  (define t2 (T (list a4 td) (c '(imp (pr Sng 1 0) (imp (pr Opr 2 0 1) (imp (pr Sng 3 2) (pr Tot 3 1)))))))
  (close-frame! t2 '(0 1 2 3) (c '(all e (all v (all p (all s (imp (pr Sng v e) (imp (pr Opr p e v) (imp (pr Sng s p) (pr Tot s v))))))))) 'TotS))

;; StepS: forall e v s (Emp(e) -> Sng(v,e) -> Step(s,e,v)): {e} = D(U_e) when e is empty
(defgen StepS (key)
  (begin-thm! key 3)
  (define X (fresh!)) (define C (fresh!)) (define u (fresh!)) (define z (fresh!))   ; 3 4 5 6
  (define St (c (Step 2 0 1)))
  (define St3 (ren (scons X sid) (abody St)))           ; X in v <-> (Below & Rest)
  (define-values (Xinv BR) (match St3 [(list 'N (list 'I (list 'I a b) _)) (values a b)]))
  (define-values (Below Rest) (kparts BR))
  (define emp (unfold 'Emp '(0)))
  (define nbm (sk 'NBM (list 2 0 z)))                  ; Emp(0) -> not BM(2,0,z)
  (define BMz (match (line nbm) [(list 'I _ (list 'N q)) q]))
  ;; -> : X in v gives X = e; Below is vacuous; Rest: the u of C with no element is e, so X = u in C
  (define sm (sp 8 (list 1 0 X)))
  (define b1 (alli z (T (list emp (leib `(in ,z ,HOLE) X 0) (inst (def-body emp) z))
                        (Imp (Kf (Pr 17 '(0)) (Eqv X 0)) (Imp (Mem z X) BMz)))))
  ;; Rest at C: Clo(C) -> (U_e subset C) -> (exists u in C, u = U_e) -> X in C
  (define RC (ren (scons C sid) (abody Rest)))          ; Clo(C) -> BI -> EU -> X in C
  (define EU (match RC [(list 'I _ (list 'I _ (list 'I eu _))) eu]))
  (define Ub (xbody EU))
  (define U5 (ren (scons u sid) Ub))                     ; u in C & forall z (z in u <-> BM)
  (define-values (u-in-C Uall) (kparts U5))
  (define iu (inst Uall z))
  (define a6 (alli z (T (list iu nbm) (Imp (Kf (Pr 17 '(0)) Uall) (Neg (Mem z u))))))
  (define tU (T (list a6 (unfold 'Emp (list u)) (sp 33 (list 0 u)) (sp 1 (list X 0 u)) (sp 0 (list X u)) (leib `(in ,HOLE ,C) u X))
                (Imp U5 (Imp (Pr 17 '(0)) (Imp (Eqv X 0) (Mem X C))))))
  (define eU (exel tU u))
  (define tR (T (list eU) (Imp (Kf (Pr 17 '(0)) (Eqv X 0)) RC)))
  (define aR (alli C tR))
  (define fwd (T (list sm b1 aR) (Imp (Pr 17 '(0)) (Imp (Pr 6 '(1 0)) (Imp Xinv (Kf Below Rest))))))
  ;; <- : Below makes X empty, so X = e in v
  (define ib (inst Below z))
  (define aN (alli z (T (list ib nbm) (Imp (Kf (Pr 17 '(0)) Below) (Neg (Mem z X))))))
  (define bwd (T (list aN (unfold 'Emp (list X)) (sp 33 (list 0 X)) (sp 7 '(1 0)) (leib `(in ,HOLE 1) 0 X))
                 (Imp (Pr 17 '(0)) (Imp (Pr 6 '(1 0)) (Imp (Kf Below Rest) Xinv)))))
  (define both (T (list fwd bwd) (Imp (Kf (Pr 17 '(0)) (Pr 6 '(1 0))) St3)))
  (define aX (alli X both))
  (define t (T (list aX) (Imp (Pr 17 '(0)) (Imp (Pr 6 '(1 0)) St))))
  (close-frame! t '(0 1 2) (c `(all e (all v (all s (imp (pr Emp e) (imp (pr Sng v e) ,(Step 's 'e 'v))))))) 'StepS))

;; AllS: forall e v p s (Emp(e) -> Sng(v,e) -> Opr(p,e,v) -> Sng(s,p) -> forall b w (App(s,b,w) -> b in v & Step(s,b,w)))
(defgen AllS (key)
  (begin-thm! key 6)
  (define as (sk 'AppSng '(0 1 2 3)))
  (define AB (rhs (rhs (line as))))
  (define ab (inst* AB '(4 5)))
  (define t1 (T (append (list as) ab (list (sp 7 '(1 0)) (sk 'StepS '(0 1 3)) (sp 0 '(4 0)) (sp 0 '(5 1))
                                           (leib `(in ,HOLE 1) 0 4) (leib (Step 3 HOLE 1) 0 4) (leib (Step 3 4 HOLE) 1 5)))
                (c `(imp (and (pr Emp 0) (pr Sng 1 0) (pr Opr 2 0 1) (pr Sng 3 2)) (imp (pr App 3 4 5) (and (in 4 1) ,(Step 3 4 5)))))))
  (define a5 (alli 5 t1)) (define a4 (alli 4 a5))
  (define t2 (T (list a4) (c `(imp (pr Emp 0) (imp (pr Sng 1 0) (imp (pr Opr 2 0 1) (imp (pr Sng 3 2)
                                (all b (all w (imp (pr App 3 b w) (and (in b 1) ,(Step 3 'b 'w))))))))))))
  (close-frame! t2 '(0 1 2 3)
                (c `(all e (all v (all p (all s (imp (pr Emp e) (imp (pr Sng v e) (imp (pr Opr p e v) (imp (pr Sng s p)
                      (all b (all w (imp (pr App s b w) (and (in b v) ,(Step 's 'b 'w))))))))))))))
                'AllS))

;; O1 LEX: exists x L(x), with x = 0, s = {(0, {0})}
(defgen LEX (key)
  (begin-thm! key 4)
  (define Lf (LF)) (define Goal (Xf Lf))
  (define Lsb (xbody Lf))                               ; s = v0, x = v1
  (define Ls3 (ren (scons 3 sid) Lsb))                  ; x = 0, s = 3
  (define-values (Lev3 Rest) (kparts Ls3))
  (define-values (F3 ED) (kparts Lev3))
  (define Db (xbody ED))
  (define D1 (ren (scons 1 sid) Db))
  (define Bb (xbody Rest))
  (define Rb0 (ren (scons 0 sid) Bb))
  (define Bv (xbody Rb0))
  (define facts (list (sk 'OrdSng '(0 1)) (sk 'TotS '(0 1 2 3)) (sk 'FncS '(0 1 2 3)) (sk 'AppS '(0 1 2 3))
                      (sk 'AllS '(0 1 2 3)) (sp 7 '(1 0)) (exi Db 1) (exi Bv 1) (exi Bb 0) (exi Lsb 3) (exi Lf 0)))
  (define t (T facts (Imp (Pr 6 '(3 2)) (Imp (conj* (list (Pr 17 '(0)) (Pr 6 '(1 0)) (Pr 8 '(2 0 1)))) Goal))))
  (define m3 (M (sp 3 '(2)) (exel t 3)))
  (define t2 (T (list m3) (Imp (Pr 8 '(2 0 1)) (Imp (Kf (Pr 17 '(0)) (Pr 6 '(1 0))) Goal))))
  (define m2 (M (sp 6 '(0 1)) (exel t2 2)))
  (define t3 (T (list m2) (Imp (Pr 6 '(1 0)) (Imp (Pr 17 '(0)) Goal))))
  (define m1 (M (sp 3 '(0)) (exel t3 1)))
  (define m0 (M (U 'EmpEx '()) (exel m1 0)))
  (check-final! 'LEX m0 Goal)
  (end-thm! Goal '()))

;; O2 LTr: L is transitive, forall x y (L(y) -> x in y -> L(x)); the statement is HT 0 with L for the symbol 5000
(define (psubM F Mform)
  (match F
    [(list 'P 5000 (list a)) (ren (scons a sid) Mform)]
    [(list 'N a) (Neg (psubM a Mform))] [(list 'I a b) (Imp (psubM a Mform) (psubM b Mform))]
    [(list 'A a) (All (psubM a Mform))] [_ F]))
(defgen LTr (key)
  (begin-thm! key 2)
  (define Lf (LF))
  (define stmt (psubM (c TRC-DSL) Lf))
  (define L1 (ren (scons 1 sid) Lf))
  (define Lsb (xbody Lf)) (define Ls2 (ren (scons 2 sid) Lsb)) (define-values (Lev2 Rest2) (kparts Ls2))
  (define Bb (xbody Rest2)) (define Rb5 (ren (scons 5 sid) Bb))
  (define Hsb (xbody L1)) (define Hs2 (ren (scons 2 sid) Hsb)) (define-values (Lev2b HRest2) (kparts Hs2))
  (unless (equal? Lev2 Lev2b) (error 'LTr "Lev differs"))
  (define HB (xbody HRest2)) (define HRb3 (ren (scons 3 sid) HB)) (define HBv (xbody HRb3)) (define HRv4 (ren (scons 4 sid) HBv))
  (define-values (F2 ED) (kparts Lev2))
  (define D7 (ren (scons 7 sid) (xbody ED)))
  (define-values (OT AllBV) (kparts D7))
  (define iA (inst* AllBV '(3 4)))
  (define-values (b-in-d Step234) (kparts (rhs (rhs (line (last iA))))))
  (define iS (inst Step234 1))
  (define-values (Xin BR) (match (rhs (line iS)) [(list 'N (list 'I (list 'I a b) _)) (values a b)]))
  (define-values (Below13 Rest13) (kparts BR))
  (define iB (inst Below13 0))
  (define BM230 (rhs (rhs (line iB))))
  (define G5 (ren (scons 5 sid) (xbody BM230)))
  (define-values (g-in-b W5) (kparts G5))
  (unless (equal? W5 Rb5) (error 'LTr "the value clause differs"))
  (define tg (T (list (exi Bb 5) (exi Lsb 2)) (Imp G5 (Imp Lev2 Lf))))
  (define eg (exel tg 5))
  (define td (T (append iA (list iS iB eg)) (Imp D7 (Imp (Kf Lev2 HRv4) (Imp (Mem 0 1) Lf)))))
  (define ed (exel td 7))
  (define t5 (T (list ed) (Imp HRv4 (Imp Lev2 (Imp (Mem 0 1) Lf)))))
  (define ev (exel t5 4)) (define eb (exel ev 3))
  (define t6 (T (list eb) (Imp Hs2 (Imp (Mem 0 1) Lf))))
  (define es (exel t6 2))
  (close-frame! es '(0 1) stmt 'LTr))

;; ======================================================================== lane LCH round 2: coherence of hierarchies (toward O3, O4)
;; congr: a line  Hyp -> (F1 <-> F2)  where F1, F2 differ only at instances of Hyp's body; Hyp = forall z (P(z) <-> Q(z)),
;; inst? recognizes an instance pair (P(k), Q(k)) at a frame variable k. Under a quantifier a fresh frame variable is used.
(define (congr Hyp inst? F1 F2)
  (cond
    [(equal? F1 F2) (T '() (Imp Hyp (Qf F1 F2)))]
    [(inst? F1 F2) => (lambda (k) (inst Hyp k))]
    [else
     (match* (F1 F2)
       [((list 'N a1) (list 'N a2)) (T (list (congr Hyp inst? a1 a2)) (Imp Hyp (Qf F1 F2)))]
       [((list 'I a1 b1) (list 'I a2 b2))
        (T (list (congr Hyp inst? a1 a2) (congr Hyp inst? b1 b2)) (Imp Hyp (Qf F1 F2)))]
       [((list 'A a1) (list 'A a2))
        (define k (fresh!))
        (define a1k (ren (scons k sid) a1)) (define a2k (ren (scons k sid) a2))
        (define l (congr Hyp inst? a1k a2k))
        (define h1 (alli k (T (list l (inst F1 k)) (Imp (Kf Hyp F1) a2k))))
        (define h2 (alli k (T (list l (inst F2 k)) (Imp (Kf Hyp F2) a1k))))
        (T (list h1 h2) (Imp Hyp (Qf F1 F2)))]
       [(_ _) (error 'congr "no congruence:\n  ~a\n  ~a" (show F1) (show F2))])]))
(define (bm-inst s t b)                  ; recognizer for BM(s,b,k) / BM(t,b,k)
  (lambda (F1 F2)
    (for/first ([k (in-range 0 64)] #:when (and (equal? F1 (c (BM s b k))) (equal? F2 (c (BM t b k))))) k)))
(define (HypBM s t b) (c (let ([z (fs 'z)]) `(all ,z (iff ,(BM s b z) ,(BM t b z))))))

;; CohStep: forall s t b v w (Step(s,b,v) -> Step(t,b,w) -> forall z (BM(s,b,z) <-> BM(t,b,z)) -> v = w)
(defgen CohStep (key)
  (begin-thm! key 5)
  (define X (fresh!))
  (define Ss (c (Step 0 2 3))) (define St (c (Step 1 2 4))) (define Hy (HypBM 0 1 2))
  (define is (inst Ss X)) (define it (inst St X))
  (define-values (xs Ps) (match (rhs (line is)) [(list 'N (list 'I (list 'I a b) _)) (values a b)]))
  (define-values (xt Pt) (match (rhs (line it)) [(list 'N (list 'I (list 'I a b) _)) (values a b)]))
  (define cg (congr Hy (bm-inst 0 1 2) Ps Pt))
  (define t1 (T (list is it cg) (Imp (conj* (list Ss St Hy)) (Qf (Mem X 3) (Mem X 4)))))
  (define a1 (alli X t1))
  (define ex (S (U 0 '()) '(3 4)))
  (define t2 (T (list a1 ex) (Imp Ss (Imp St (Imp Hy (Eqv 3 4))))))
  (close-frame! t2 '(0 1 2 3 4)
                (c `(all s (all t (all b (all v (all w (imp ,(Step 's 'b 'v) (imp ,(Step 't 'b 'w)
                      (imp ,(let ([z (fs 'z)]) `(all ,z (iff ,(BM 's 'b z) ,(BM 't 'b z)))) (eq v w))))))))))
                'CohStep))

;; the separated set of the first disagreement and its defining formula (x = v0 of g, z = v1, s = v2, t = v3)
(define (Gb s t x) (let ([v (fs 'v)] [w (fs 'w)]) `(ex ,v (ex ,w (and (pr App ,s ,x ,v) (pr App ,t ,x ,w) (not (eq ,v ,w)))))))
(define (BBdsl B d s t) (let ([x (fs 'x)]) `(all ,x (iff (in ,x ,B) (and (in ,x ,d) ,(Gb s t x))))))
(define (Mindsl B y) (let ([z (fs 'z)]) `(not (ex ,z (and (in ,z ,B) (in ,z ,y))))))

;; CohBM: forall s t d e B b (Ord d & Ord e & Tot(s,d) & Tot(t,e) & b in d & b in e & Min(B,b) & BB(B,d,s,t)
;;                            -> forall z (BM(s,b,z) <-> BM(t,b,z)))
(defgen CohBM (key)
  (begin-thm! key 6)
  (define z (fresh!)) (define g (fresh!)) (define w1 (fresh!)) (define w2 (fresh!))   ; 6 7 8 9
  (define H (c `(and (pr Ord 2) (pr Ord 3) (pr Tot 0 2) (pr Tot 1 3) (in 5 2) (in 5 3) ,(Mindsl 4 5) ,(BBdsl 4 2 0 1))))
  (define od2 (unfold 'Ord '(2))) (define od3 (unfold 'Ord '(3)))
  (define tr2 (unfold 'Tr '(2))) (define tr3 (unfold 'Tr '(3)))
  (define i2 (inst* (def-body tr2) (list g 5))) (define i3 (inst* (def-body tr3) (list g 5)))
  (define to2 (unfold 'Tot '(0 2))) (define to3 (unfold 'Tot '(1 3)))
  (define it2 (inst (def-body to2) g)) (define it3 (inst (def-body to3) g))
  (define BBf (c (BBdsl 4 2 0 1)))
  (define ib (inst BBf g))
  (define zz (fs 'z))
  (define mexi (exi (xbody (c `(ex ,zz (and (in ,zz 4) (in ,zz 5))))) g))      ; g in B & g in b -> exists z ...
  (define Gbg (c (Gb 0 1 g)))
  (define gv (xbody Gbg)) (define gv8 (ren (scons w1 sid) gv)) (define gw (xbody gv8))
  (define e-in (exi gw w2)) (define e-out (exi gv w1))                          ; for (v, w) = (w1, w2)
  (define gv9 (ren (scons w2 sid) gv)) (define gw9 (xbody gv9))
  (define f-in (exi gw9 w1)) (define f-out (exi gv w2))                         ; for (v, w) = (w2, w1)
  (define BMs (c (BM 0 5 z))) (define BMt (c (BM 1 5 z)))
  (define (open-bm BMf w) (let* ([G (ren (scons g sid) (xbody BMf))]) (values G (ren (scons w sid) (xbody (match G [(list 'N (list 'I _ (list 'N q))) q]))))))
  (define-values (Gs Ws8) (open-bm BMs w1))                  ; g in b & exists w (App(s,g,w) & z in w);  App(s,g,w1) & z in w1
  (define-values (Gt9 Wt9) (open-bm BMt w2))
  ;; -> : BM(s) at g, w1; the value of t at g is w2
  (define tA (T (append (list od2 od3 tr2 tr3 to2 to3 it2 it3 ib mexi e-in e-out (leib `(in ,z ,HOLE) w1 w2)
                              (exi (xbody (match Gt9 [(list 'N (list 'I _ (list 'N q))) q])) w2) (exi (xbody BMt) g))
                        i2 i3)
                (Imp (Pr 9 (list 1 g w2)) (Imp H (Imp Ws8 (Imp (Mem g 5) BMt))))))
  (define eY (exel tA w2))
  (define tB (T (append (list eY od2 od3 tr2 tr3 to3 it3) i3) (Imp Ws8 (Imp (Mem g 5) (Imp H BMt)))))
  (define eW (exel tB w1))
  (define tC (T (list eW) (Imp Gs (Imp H BMt))))
  (define eG (exel tC g))
  ;; <- : BM(t) at g, w2; the value of s at g is w1
  (define Gs8 (match Gs [(list 'N (list 'I _ (list 'N q))) q]))
  (define tA2 (T (append (list od2 od3 tr2 tr3 to2 to3 it2 it3 ib mexi e-in e-out (sp 0 (list w1 w2)) (leib `(in ,z ,HOLE) w2 w1)
                               (exi (xbody Gs8) w1) (exi (xbody BMs) g))
                         i2 i3)
                 (Imp (Pr 9 (list 0 g w1)) (Imp H (Imp Wt9 (Imp (Mem g 5) BMs))))))
  (define eY2 (exel tA2 w1))
  (define tB2 (T (append (list eY2 od2 od3 tr2 tr3 to2 it2) i2) (Imp Wt9 (Imp (Mem g 5) (Imp H BMs)))))
  (define eW2 (exel tB2 w2))
  (define tC2 (T (list eW2) (Imp Gt9 (Imp H BMs))))
  (define eG2 (exel tC2 g))
  (define t (T (list eG eG2) (Imp H (Qf BMs BMt))))
  (define a (alli z t))
  (define t2 (T (list a) (chain-imp (list (Pr 16 '(2)) (Pr 16 '(3)) (Pr 12 '(0 2)) (Pr 12 '(1 3)) (Mem 5 2) (Mem 5 3)
                                          (c (Mindsl 4 5)) BBf) (HypBM 0 1 5))))
  (close-frame! t2 '(0 1 2 3 4 5)
                (c `(all s (all t (all d (all e (all B (all b
                      (imp (pr Ord d) (imp (pr Ord e) (imp (pr Tot s d) (imp (pr Tot t e) (imp (in b d) (imp (in b e)
                        (imp ,(Mindsl 'B 'b) (imp ,(BBdsl 'B 'd 's 't)
                          ,(let ([z (fs 'z)]) `(all ,z (iff ,(BM 's 'b z) ,(BM 't 'b z)))))))))))))))))))
                'CohBM))

;; Coh: forall s t (Lev(s) -> Lev(t) -> forall b v w (App(s,b,v) -> App(t,b,w) -> v = w))
(defgen Coh (key)
  (begin-thm! key 2)
  (define d 2) (define e 3) (define B 4) (define b 5) (define v 6) (define w 7) (define y 8) (define v2 9) (define w2 10)
  (set-thm-next! (cur) 11)
  (define Lev0 (c (Lev 0))) (define Lev1 (c (Lev 1)))
  (define-values (F0 ED0) (kparts Lev0)) (define-values (F1 ED1) (kparts Lev1))
  (define Ds (ren (scons d sid) (xbody ED0))) (define Dt (ren (scons e sid) (xbody ED1)))
  (define-values (OTs Alls) (kparts Ds)) (define-values (OTt Allt) (kparts Dt))
  (define sep (S (Y (SepF (c (Gb 2 3 0)))) (list d)))
  (define BBf (c (BBdsl B d 0 1)))
  (unless (equal? (ren (scons B sid) (xbody (line sep))) BBf) (error 'Coh "the separation instance differs"))
  (define found (S (U 5 '()) (list B)))
  (define Fy (xbody (rhs (line found))))
  (define Yy (ren (scons y sid) Fy))
  (define-values (y-in-B Miny) (kparts Yy))
  (define CTX (conj* (list Ds Dt BBf)))
  ;; the minimal element y of B gives a contradiction
  (define as (inst* Alls (list y v2))) (define at (inst* Allt (list y w2)))
  (define cbm (sk 'CohBM (list 0 1 d e B y)))
  (define cst (sk 'CohStep (list 0 1 y v2 w2)))
  (define Gy (c (Gb 0 1 y)))
  (define Gyv (ren (scons v2 sid) (xbody Gy))) (define Gyw (ren (scons w2 sid) (xbody Gyv)))
  (define tK (T (append as at (list cbm cst)) (Imp Gyw (Imp CTX (Neg Yy)))))
  (define e10 (exel tK w2)) (define e9 (exel e10 v2))
  (define ib-y (inst BBf y))
  (define tN (T (list e9 ib-y) (Imp CTX (Neg Yy))))
  (define aY (alli y tN))
  ;; any disagreement b would lie in B
  (define as5 (inst* Alls (list b v)))
  (define Gb5 (c (Gb 0 1 b)))
  (define Gbv (xbody Gb5)) (define Gbv6 (ren (scons v sid) Gbv)) (define Gbw (xbody Gbv6))
  (define ex1 (exi Gbw w)) (define ex2 (exi Gbv v))
  (define ib5 (inst BBf b))
  (define exB (exi (xbody (match (line found) [(list 'I a _) a])) b))
  (define tM (T (append as5 (list ex1 ex2 ib5 exB found aY))
                (Imp CTX (Imp (Pr 9 (list 0 b v)) (Imp (Pr 9 (list 1 b w)) (Eqv v w))))))
  (define a7 (alli w tM)) (define a6 (alli v a7)) (define a5 (alli b a6))
  (define Concl (rhs (line a5)))
  (define tB (T (list a5) (Imp BBf (Imp (Kf Ds Dt) Concl))))
  (define mB (M sep (exel tB B)))
  (define tE (T (list mB) (Imp Dt (Imp Ds Concl))))
  (define eE (exel tE e))
  (define tD (T (list eE) (Imp Ds (Imp ED1 Concl))))
  (define eD (exel tD d))
  (define tL (T (list eD) (Imp Lev0 (Imp Lev1 Concl))))
  (close-frame! tL '(0 1)
                (c `(all s (all t (imp ,(Lev 's) (imp ,(Lev 't) (all b (all v (all w (imp (pr App s b v) (imp (pr App t b w) (eq v w)))))))))))
                'Coh))
;; ======================================================================== commands
(define (build-lch keys)
  (reset-batch!)
  (define t0 (current-milliseconds))
  (for ([k keys]) (ensure! k))
  (define ths (reverse out-thms))
  (list (batch-text) (- (current-milliseconds) t0) (hash-copy stats) (map car ths) (map caddr ths)))
(define (registry-mutant text idx f)
  (define-values (rg ths) (read-jdg-text text))
  (structure-text (for/list ([e rg] [i (in-naturals)]) (if (= i idx) (list (f (car e)) (cadr e)) e)) ths))
(define LAYERS
  (list
   (list "05-coh" "two hierarchies agree where both are defined (toward O3, O4)"
         (quote (CohStep CohBM Coh))
         (lambda () (c `(all s (all t (imp ,(Lev (quote s)) (imp ,(Lev (quote t)) (all b (all v (all w (imp (pr App s b v) (imp (pr App t b w) (in v w))))))))))))
         (lambda () (cons 0 (lambda (d) (match d [(list (quote a) (list (quote a) (list (quote i) X (list (quote q) 1 0)))) (list (quote a) (list (quote a) (list (quote i) X (list (quote q) 0 1))))])))))))
(define (cmd-emit dir)
  (load-base!)
  (make-directory* (build-path dir "mut"))
  (for ([layer LAYERS])
    (match-define (list base what jobs twin regmut) layer)
    (match-define (list text ms st keys pflags) (build-lch jobs))
    (define file (build-path dir (string-append base ".jdg")))
    (write-new file text)
    (define-values (rg ths) (read-jdg-text text))
    (printf "~a.jdg  ~a\n" base what)
    (printf "  theorems ~a (prelude ~a), steps ~a (prelude ~a), bytes ~a, build ~a ms, largest tautology test ~a calls\n"
            (length ths) (hash-ref st 'prelude 0) (+ (hash-ref st 'steps 0) (hash-ref st 'prelude-steps 0)) (hash-ref st 'prelude-steps 0)
            (file-size file) ms (hash-ref st 'taut-max 0))
    (printf "  registry: ~a\n" (check-registry-text text))
    (printf "  copy of the checker: ~a\n" (check-batch rg ths))
    (write-new (build-path dir (string-append base ".index.txt"))
               (string-join (for/list ([k keys] [t ths] [i (in-naturals)])
                              (format "~a ~a ~a" i k (if (and (pair? k) (eq? (car k) 'replay)) "" (show (tof (car t)))))) "\n"))
    (define ms2 (append (mutants text (twin) pflags)
                        (if regmut (let ([rm (regmut)]) (list (list "registry-used" (registry-mutant text (car rm) (cdr rm))))) '())))
    (for ([m ms2])
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
    [_ (printf "usage: racket lch10.rkt emit DIR | judge DIR RESULTS\n")]))
