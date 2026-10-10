#lang racket/base
;; zfcore.rkt -- lane L6: lines 23-353 of sigma1/sigma1.rkt (sha256 7d3ff29c..., Stage 2), copied verbatim by sed, plus
;; (provide (all-defined-out)). Formula syntax, the copy of the checker (Replay2.v step semantics), JDG1 reading and writing.
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

