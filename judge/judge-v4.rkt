#lang racket/base
(require "registry-auth-v4.rkt")
;; judge-v4 authenticates every initial registry entry before checking theorems.
;; judge.rkt -- the Racket copy of the judge. check_batch of forcing-src/general/Replay2.v (sound for prov by Replay3.v),
;; written from the Rocq definitions only: Syn.v (form, ren, up, scons, free, form_eqb, Kf Df Qf Xf), Replay.v (absk,
;; findf, addat, topf), ReplayT.v (bf, mkN, mkI, subst, somevar, taut_bf, tobf, tautchk2), Checks.v (skip1, ins2, SepF,
;; CollF, Bot), Ax.v (closedk), Prov.v (sid), Kal.v (pform), Replay2.v (dform, tof, step, axshape, isSep isColl isSepN
;; isCollN, sstep, run, check_thm, check_batch). Exact integers throughout.
;;
;; Input JDG1 (rocq2jdg.rkt): tokens separated by white space, numbers in decimal.
;;   JDG1  R n ENTRY..  T m THM..        ENTRY = FORM LIST        THM = FORM LIST(sig) nsteps STEP.. LIST(hyps)
;;   FORM = e x y | q x y | p P LIST | n F | i F G | a F | k F G | d F G | b F G | x F     (k d b x = Kf Df Qf Xf)
;;   STEP = U r LIST | S l LIST | G l k | M i j | T LIST FORM | E t FORM | L l k FORM | H k l FORM | V t FORM
;;        | Z FORM FORM | Y FORM
;;   LIST = count then the numbers.
;; Output: ACCEPT and the counts, exit 0; or REJECT with the theorem and step index (from 0), exit 1.
;; usage: racket judge.rkt FILE.jdg
;;
;; Implementation choices that do not change the value of check_batch:
;;  - forms are hash-consed (one table per theorem), so form_eqb, a structural equality, is eq?;
;;  - each form carries fvb = 1 + its largest free variable (0 if closed); ren s f = f when every free variable of f is
;;    below the binder depth (ren_free, Ax.v), and free n f = false when n >= fvb f;
;;  - ren, free, closedk, topf, tobf, subst are memoized per call on the nodes of the DAG (pure functions);
;;  - addat keeps a set beside the list (existsb form_eqb = membership) and skips N/I nodes already walked (their atoms
;;    are in the list already, so addat leaves the list unchanged);
;;  - andb is read left to right and stops at the first false (same value).
(require racket/list)

;; ============================================================================================================== forms
;; Syn.v: form = Mem x y | Eqv x y | Pr p (list nat) | Neg a | Imp a b | All a
(struct F (tag x y fvb))   ; opaque: equal? on F is eq?, so interning keys compare children by identity

(define itab (make-parameter #f))   ; the intern table of the theorem being checked

(define (intern tag x y fvb)
  (define key (vector tag x y))
  (define t (itab))
  (or (hash-ref t key #f)
      (let ([f (F tag x y fvb)]) (hash-set! t key f) f)))

(define (Mem x y) (intern 'mem x y (add1 (max x y))))
(define (Eqv x y) (intern 'eqv x y (add1 (max x y))))
(define (Pr p a) (intern 'pr p a (if (null? a) 0 (add1 (apply max a)))))
(define (Neg a) (intern 'neg a #f (F-fvb a)))
(define (Imp a b) (intern 'imp a b (max (F-fvb a) (F-fvb b))))
(define (All a) (intern 'all a #f (max 0 (sub1 (F-fvb a)))))

(define (mem? f) (eq? (F-tag f) 'mem))
(define (eqv? f) (eq? (F-tag f) 'eqv))
(define (neg? f) (eq? (F-tag f) 'neg))
(define (imp? f) (eq? (F-tag f) 'imp))
(define (all? f) (eq? (F-tag f) 'all))
(define (sub f) (F-x f))          ; the argument of Neg / All, the left of Imp
(define (lhs f) (F-x f))
(define (rhs f) (F-y f))

;; the abbreviations (Syn.v)
(define (Kf a b) (Neg (Imp a (Neg b))))
(define (Df a b) (Imp (Neg a) b))
(define (Qf a b) (Kf (Imp a b) (Imp b a)))
(define (Xf a) (Neg (All (Neg a))))

;; form_eqb: structural equality; on interned forms of one table it is identity
(define (form-eqb f g) (eq? f g))

;; ---- ren s f (Syn.v). Under k binders the renaming is up^k s: n -> n if n < k, else k + s (n - k).
(define (ren s f)
  (define memo (make-hasheq))
  (let go ([f f] [k 0])
    (if (<= (F-fvb f) k)
        f
        (let* ([seen (hash-ref memo f '())] [hit (assv k seen)])
          (if hit
              (cdr hit)
              (let* ([v (lambda (n) (if (< n k) n (+ k (s (- n k)))))]
                     [r (case (F-tag f)
                          [(mem) (Mem (v (F-x f)) (v (F-y f)))]
                          [(eqv) (Eqv (v (F-x f)) (v (F-y f)))]
                          [(pr) (Pr (F-x f) (map v (F-y f)))]
                          [(neg) (Neg (go (sub f) k))]
                          [(imp) (Imp (go (lhs f) k) (go (rhs f) k))]
                          [(all) (All (go (sub f) (add1 k)))])])
                (hash-set! memo f (cons (cons k r) seen))
                r))))))

(define (sid n) n)                                                  ; Prov.v
(define ((scons y s) n) (if (= n 0) y (s (sub1 n))))                ; Syn.v
(define ((absk k) j) (if (= j k) 0 (add1 j)))                       ; Replay.v
(define (succ n) (add1 n))                                          ; S
(define (skip1 n) (if (= n 0) 0 (add1 n)))                          ; Checks.v: 0 -> 0, S m -> S (S m)
(define (ins2 n) (if (<= n 1) n (add1 n)))                          ; Checks.v: 0 -> 0, 1 -> 1, S (S m) -> S (S (S m))
(define (unskip n) (if (<= n 1) 0 (sub1 n)))                        ; Replay2.v: 0 -> 0, 1 -> 0, S (S m) -> S m

;; ---- free n f (Syn.v)
(define (free n f)
  (define memo (make-hasheq))
  (let go ([n n] [f f])
    (cond
      [(>= n (F-fvb f)) #f]
      [else
       (define seen (hash-ref memo f '()))
       (define hit (assv n seen))
       (if hit
           (cdr hit)
           (let ([r (case (F-tag f)
                      [(mem eqv) (or (= (F-x f) n) (= (F-y f) n))]
                      [(pr) (and (memv n (F-y f)) #t)]
                      [(neg) (go n (sub f))]
                      [(imp) (or (go n (lhs f)) (go n (rhs f)))]
                      [(all) (go (add1 n) (sub f))])])
             (hash-set! memo f (cons (cons n r) seen))
             r))])))

;; ---- closedk k f (Ax.v)
(define (closedk k f)
  (define memo (make-hasheq))
  (let go ([k k] [f f])
    (define seen (hash-ref memo f '()))
    (define hit (assv k seen))
    (if hit
        (cdr hit)
        (let ([r (case (F-tag f)
                   [(mem eqv) (and (< (F-x f) k) (< (F-y f) k))]
                   [(pr) (andmap (lambda (x) (< x k)) (F-y f))]
                   [(neg) (go k (sub f))]
                   [(imp) (and (go k (lhs f)) (go k (rhs f)))]
                   [(all) (go (add1 k) (sub f))])])
          (hash-set! memo f (cons (cons k r) seen))
          r))))

;; ---- Checks.v
(define (SepF g) (All (Xf (All (Qf (Mem 0 1) (Kf (Mem 0 2) (ren skip1 g)))))))
(define (CollF g)
  (All (Imp (All (Imp (Mem 0 1) (Xf g))) (Xf (All (Imp (Mem 0 2) (Xf (Kf (Mem 0 2) (ren ins2 g)))))))))

;; ===================================================================================================== tautologies
;; Replay.v: addat, findf, topf. pform (Kal.v) = PV i | PN p | PI p q, as vectors.
(define (atom? f) (not (or (neg? f) (imp? f))))

(define (addat-empty f)          ; addat [] f, as a list
  (define seen (make-hasheq))    ; atoms in the list
  (define walked (make-hasheq))  ; N / I nodes done
  (define acc '())
  (let go ([f f])
    (cond
      [(neg? f) (unless (hash-ref walked f #f) (go (sub f)) (hash-set! walked f #t))]
      [(imp? f) (unless (hash-ref walked f #f) (go (lhs f)) (go (rhs f)) (hash-set! walked f #t))]
      [else (unless (hash-ref seen f #f) (hash-set! seen f #t) (set! acc (cons f acc)))]))
  (reverse acc))

(define (findf-table l)          ; findf a l = index of the first b in l with form_eqb a b, else length l
  (define t (make-hasheq))
  (for ([b l] [i (in-naturals)]) (unless (hash-ref t b #f) (hash-set! t b i)))
  (define n (length l))
  (lambda (a) (hash-ref t a n)))

(define (topf l f)
  (define findf (findf-table l))
  (define memo (make-hasheq))
  (let go ([f f])
    (or (hash-ref memo f #f)
        (let ([r (case (F-tag f)
                   [(neg) (vector 'PN (go (sub f)))]
                   [(imp) (vector 'PI (go (lhs f)) (go (rhs f)))]
                   [else (vector 'PV (findf f))])])
          (hash-set! memo f r)
          r))))

;; ReplayT.v: bf = BT | BF | BV n | BN a | BI a b
(struct BV (n))
(struct BN (a))
(struct BI (a b))

(define (mkN a)
  (cond [(eq? a 'BT) 'BF]
        [(eq? a 'BF) 'BT]
        [(BN? a) (BN-a a)]
        [else (BN a)]))

(define (mkI a c)
  (cond [(eq? a 'BF) 'BT]
        [(eq? c 'BT) 'BT]
        [(eq? a 'BT) c]
        [(eq? c 'BF) (mkN a)]
        [else (BI a c)]))

(define (subst v c b)
  (define memo (make-hasheq))
  (let go ([b b])
    (cond
      [(BV? b) (if (= (BV-n b) v) (if c 'BT 'BF) b)]
      [(BN? b) (or (hash-ref memo b #f) (let ([r (mkN (go (BN-a b)))]) (hash-set! memo b r) r))]
      [(BI? b) (or (hash-ref memo b #f) (let ([r (mkI (go (BI-a b)) (go (BI-b b)))]) (hash-set! memo b r) r))]
      [else b])))

(define (somevar b)
  (cond [(BV? b) (BV-n b)]
        [(BN? b) (somevar (BN-a b))]
        [(BI? b) (or (somevar (BI-a b)) (somevar (BI-b b)))]
        [else #f]))

(define (taut-bf k b)
  (cond [(eq? b 'BT) #t]
        [(eq? b 'BF) #f]
        [else
         (define v (somevar b))
         (if (and (> k 0) v)
             (and (taut-bf (sub1 k) (subst v #t b)) (taut-bf (sub1 k) (subst v #f b)))
             #f)]))

(define (tobf p)
  (define memo (make-hasheq))
  (let go ([p p])
    (or (hash-ref memo p #f)
        (let ([r (case (vector-ref p 0)
                   [(PV) (BV (vector-ref p 1))]
                   [(PN) (mkN (go (vector-ref p 1)))]
                   [(PI) (mkI (go (vector-ref p 1)) (go (vector-ref p 2)))])])
          (hash-set! memo p r)
          r))))

(define (tautchk2 f)
  (define l (addat-empty f))
  (taut-bf (length l) (tobf (topf l f))))

;; ========================================================================================================= Replay2.v
;; dform as parsed: #(e x y) #(q x y) #(p P list) #(n F) #(i F G) #(a F) #(k F G) #(d F G) #(b F G) #(x F)
(define (tof d)
  (case (vector-ref d 0)
    [(e) (Mem (vector-ref d 1) (vector-ref d 2))]
    [(q) (Eqv (vector-ref d 1) (vector-ref d 2))]
    [(p) (Pr (vector-ref d 1) (vector-ref d 2))]
    [(n) (Neg (tof (vector-ref d 1)))]
    [(i) (Imp (tof (vector-ref d 1)) (tof (vector-ref d 2)))]
    [(a) (All (tof (vector-ref d 1)))]
    [(k) (Kf (tof (vector-ref d 1)) (tof (vector-ref d 2)))]
    [(d) (Df (tof (vector-ref d 1)) (tof (vector-ref d 2)))]
    [(b) (Qf (tof (vector-ref d 1)) (tof (vector-ref d 2)))]
    [(x) (Xf (tof (vector-ref d 1)))]))

;; ---- axiom shapes
(define (isSep g)
  ;; All (Neg (All (Neg (All (Neg (Imp (Imp _ (Neg (Imp _ (Neg F)))) _))))))
  (define F*
    (and (all? g)
         (let ([g1 (sub g)]) (and (neg? g1)
         (let ([g2 (sub g1)]) (and (all? g2)
         (let ([g3 (sub g2)]) (and (neg? g3)
         (let ([g4 (sub g3)]) (and (all? g4)
         (let ([g5 (sub g4)]) (and (neg? g5)
         (let ([g6 (sub g5)]) (and (imp? g6)
         (let ([g7 (lhs g6)]) (and (imp? g7)
         (let ([g8 (rhs g7)]) (and (neg? g8)
         (let ([g9 (sub g8)]) (and (imp? g9)
         (let ([g10 (rhs g9)]) (and (neg? g10) (sub g10)))))))))))))))))))))))
  (and F* (not (free 1 F*)) (form-eqb g (SepF (ren unskip F*)))))

(define (isColl g)
  ;; All (Imp (All (Imp _ (Neg (All (Neg F))))) _)
  (define F*
    (and (all? g)
         (let ([g1 (sub g)]) (and (imp? g1)
         (let ([g2 (lhs g1)]) (and (all? g2)
         (let ([g3 (sub g2)]) (and (imp? g3)
         (let ([g4 (rhs g3)]) (and (neg? g4)
         (let ([g5 (sub g4)]) (and (all? g5)
         (let ([g6 (sub g5)]) (and (neg? g6) (sub g6)))))))))))))))
  (and F* (form-eqb g (CollF F*))))

(define (isSepN g) (or (isSep g) (and (all? g) (isSepN (sub g)))))
(define (isCollN g) (or (isColl g) (and (all? g) (isCollN (sub g)))))

(define (axshape g)
  (or
   ;; Imp a (Imp b a')                                          (k)
   (and (imp? g) (imp? (rhs g)) (form-eqb (lhs g) (rhs (rhs g))))
   ;; Imp (Imp a (Imp b c)) (Imp (Imp a' b') (Imp a'' c'))      (s)
   (and (imp? g) (imp? (lhs g)) (imp? (rhs (lhs g))) (imp? (rhs g)) (imp? (lhs (rhs g))) (imp? (rhs (rhs g)))
        (let ([a (lhs (lhs g))] [b (lhs (rhs (lhs g)))] [c (rhs (rhs (lhs g)))]
              [a1 (lhs (lhs (rhs g)))] [b1 (rhs (lhs (rhs g)))] [a2 (lhs (rhs (rhs g)))] [c1 (rhs (rhs (rhs g)))])
          (and (form-eqb a a1) (form-eqb a a2) (form-eqb b b1) (form-eqb c c1))))
   ;; Imp (Imp (Neg a) (Neg b)) (Imp b' a')                     (c)
   (and (imp? g) (imp? (lhs g)) (neg? (lhs (lhs g))) (neg? (rhs (lhs g))) (imp? (rhs g))
        (form-eqb (sub (lhs (lhs g))) (rhs (rhs g))) (form-eqb (sub (rhs (lhs g))) (lhs (rhs g))))
   ;; Imp (All (Imp a b)) (Imp (All a') (All b'))               (dist)
   (and (imp? g) (all? (lhs g)) (imp? (sub (lhs g))) (imp? (rhs g)) (all? (lhs (rhs g))) (all? (rhs (rhs g)))
        (form-eqb (lhs (sub (lhs g))) (sub (lhs (rhs g)))) (form-eqb (rhs (sub (lhs g))) (sub (rhs (rhs g)))))
   ;; Imp a (All b), b = ren S a                                (vac)
   (and (imp? g) (all? (rhs g)) (form-eqb (sub (rhs g)) (ren succ (lhs g))))
   ;; Eqv x x                                                   (refl)
   (and (eqv? g) (= (F-x g) (F-y g)))
   (isSepN g)
   (isCollN g)))

;; ---- one step. Returns (cons form hyps) or #f. lines: vector, nl: its length; reg-form: index -> form or #f.
(define (line lines nl l) (and (< l nl) (vector-ref lines l)))

(define (specn f ts)
  (cond [(null? ts) f]
        [(all? f) (specn (ren (scons (car ts) sid) (sub f)) (cdr ts))]
        [else #f]))

(define (sstep reg-entry reg-form lines nl st)
  (define (ok G) (cons G '()))
  (case (vector-ref st 0)
    [(U) (define r (vector-ref st 1))
         (define e (reg-entry r))
         (and e
              (let* ([sig (list->vector (vector-ref st 2))]
                     [sigf (lambda (i) (if (< i (vector-length sig)) (vector-ref sig i) 0))])
                (cons (ren sigf (reg-form r)) (cdr e))))]
    [(S) (define F* (line lines nl (vector-ref st 1)))
         (and F* (let ([G (specn F* (vector-ref st 2))]) (and G (ok G))))]
    [(G) (define F* (line lines nl (vector-ref st 1)))
         (and F* (ok (All (ren (absk (vector-ref st 2)) F*))))]
    [(M) (define a (line lines nl (vector-ref st 1)))
         (define ab (line lines nl (vector-ref st 2)))
         (and a ab (imp? ab) (form-eqb a (lhs ab)) (ok (rhs ab)))]
    [(T) (define G (tof (vector-ref st 2)))
         (define ps (for/list ([l (vector-ref st 1)]) (line lines nl l)))
         (and (andmap values ps)
              (tautchk2 (foldr Imp G ps))
              (ok G))]
    [(E) (define t (vector-ref st 1))
         (define G (tof (vector-ref st 2)))
         ;; Imp F (Neg (All (Neg f)))
         (and (imp? G) (neg? (rhs G)) (all? (sub (rhs G))) (neg? (sub (sub (rhs G))))
              (let ([F* (lhs G)] [f (sub (sub (sub (rhs G))))])
                (and (form-eqb F* (ren (scons t sid) f)) (ok G))))]
    [(L) (define l (vector-ref st 1))
         (define k (vector-ref st 2))
         (define G (tof (vector-ref st 3)))
         (define Ln (line lines nl l))
         ;; G = Imp (Neg (All (Neg P'))) G2, line l = Imp P G3
         (and (imp? G) (neg? (lhs G)) (all? (sub (lhs G))) (neg? (sub (sub (lhs G))))
              Ln (imp? Ln)
              (let ([P1 (sub (sub (sub (lhs G))))] [G2 (rhs G)] [P (lhs Ln)] [G3 (rhs Ln)])
                (and (form-eqb G2 G3) (form-eqb P1 (ren (absk k) P)) (not (free k G2)) (ok G))))]
    [(H) (define k (vector-ref st 1))
         (define l (vector-ref st 2))
         (define G (tof (vector-ref st 3)))
         (define Ln (line lines nl l))
         ;; G = Imp H (All f'), line l = Imp H2 f
         (and (imp? G) (all? (rhs G)) Ln (imp? Ln)
              (let ([H* (lhs G)] [f1 (sub (rhs G))] [H2 (lhs Ln)] [f (rhs Ln)])
                (and (form-eqb H* H2) (form-eqb f1 (ren (absk k) f)) (not (free k H*)) (ok G))))]
    [(V) (define t (vector-ref st 1))
         (define G (tof (vector-ref st 2)))
         ;; Imp (All f) G2
         (and (imp? G) (all? (lhs G))
              (form-eqb (rhs G) (ren (scons t sid) (sub (lhs G))))
              (ok G))]
    [(Z) (define A (tof (vector-ref st 1)))
         (define G (tof (vector-ref st 2)))
         ;; Imp (Eqv s t) (Imp X Y)
         (and (imp? G) (eqv? (lhs G)) (imp? (rhs G))
              (let ([s (F-x (lhs G))] [t (F-y (lhs G))] [X (lhs (rhs G))] [Y (rhs (rhs G))])
                (and (form-eqb X (ren (scons s sid) A)) (form-eqb Y (ren (scons t sid) A)) (ok G))))]
    [(Y) (define G (tof (vector-ref st 1)))
         (and (axshape G) (ok G))]))

;; check_thm. reg: vector of entries #(dform hyps), nreg of them in use. Returns #t or (cons step-index reason).
(define (nodupb l) (or (null? l) (and (not (memv (car l) (cdr l))) (nodupb (cdr l)))))

(define (check-thm reg nreg t)
  (parameterize ([itab (make-hash)])
    (define stmt (vector-ref t 0))
    (define sig (vector-ref t 1))
    (define steps (vector-ref t 2))
    (define hyps (vector-ref t 3))
    (define (reg-entry r) (and (< r nreg) (vector-ref reg r)))
    (define rcache (make-hasheqv))
    (define (reg-form r) (or (hash-ref rcache r #f)
                             (let ([f (tof (car (vector-ref reg r)))]) (hash-set! rcache r f) f)))
    (define n (vector-length steps))
    (define lines (make-vector n #f))
    (let loop ([i 0] [hs '()])
      (if (< i n)
          (let ([res (sstep reg-entry reg-form lines i (vector-ref steps i))])
            (if res
                (begin (vector-set! lines i (car res)) (loop (add1 i) (append hs (cdr res))))
                (cons i (format "step ~a" (vector-ref (vector-ref steps i) 0)))))
          ;; final: last line = ren (sigf sig) (tof stmt), sig without repeats, stmt closed below length sig,
          ;; hs within the claimed hyps, at least one line
          (let* ([S (tof stmt)]
                 [sv (list->vector sig)]
                 [sigf (lambda (j) (if (< j (vector-length sv)) (vector-ref sv j) 0))])
            (cond
              [(= n 0) (cons n "final: no lines")]
              [(not (form-eqb (vector-ref lines (sub1 n)) (ren sigf S))) (cons n "final: last line is not the statement")]
              [(not (nodupb sig)) (cons n "final: sig repeats a variable")]
              [(not (closedk (length sig) S)) (cons n "final: statement not closed below length sig")]
              [(not (andmap (lambda (h) (memv h hyps)) hs)) (cons n "final: a hypothesis used is not claimed")]
              [else #t]))))))

;; ============================================================================================================ input
(define src #"")
(define pos 0)
(define (perr msg) (raise (list 'parse msg pos)))

(define (ws? b) (or (= b 32) (= b 10) (= b 13) (= b 9)))
(define (skip-ws!) (let loop () (when (and (< pos (bytes-length src)) (ws? (bytes-ref src pos))) (set! pos (add1 pos)) (loop))))
(define (token!)
  (skip-ws!)
  (when (>= pos (bytes-length src)) (perr "unexpected end of input"))
  (define start pos)
  (let loop () (when (and (< pos (bytes-length src)) (not (ws? (bytes-ref src pos)))) (set! pos (add1 pos)) (loop)))
  (subbytes src start pos))
(define (num!)
  (define t (token!))
  (unless (for/and ([b t]) (<= 48 b 57)) (perr (format "expected a number, got ~a" t)))
  (for/fold ([v 0]) ([b t]) (+ (* v 10) (- b 48))))
(define (tag!)
  (define t (token!))
  (unless (= (bytes-length t) 1) (perr (format "expected a tag, got ~a" t)))
  (integer->char (bytes-ref t 0)))
(define (list!) (define c (num!)) (for/list ([_ (in-range c)]) (num!)))

(define (form!)
  (define c (tag!))
  (case c
    [(#\e) (let* ([x (num!)] [y (num!)]) (vector 'e x y))]
    [(#\q) (let* ([x (num!)] [y (num!)]) (vector 'q x y))]
    [(#\p) (let* ([p (num!)] [a (list!)]) (vector 'p p a))]
    [(#\n) (vector 'n (form!))]
    [(#\a) (vector 'a (form!))]
    [(#\x) (vector 'x (form!))]
    [(#\i) (let* ([a (form!)] [b (form!)]) (vector 'i a b))]
    [(#\k) (let* ([a (form!)] [b (form!)]) (vector 'k a b))]
    [(#\d) (let* ([a (form!)] [b (form!)]) (vector 'd a b))]
    [(#\b) (let* ([a (form!)] [b (form!)]) (vector 'b a b))]
    [else (perr (format "form: unexpected tag ~a" c))]))

(define (step!)
  (define c (tag!))
  (case c
    [(#\U) (let* ([r (num!)] [l (list!)]) (vector 'U r l))]
    [(#\S) (let* ([l (num!)] [ts (list!)]) (vector 'S l ts))]
    [(#\G) (let* ([l (num!)] [k (num!)]) (vector 'G l k))]
    [(#\M) (let* ([i (num!)] [j (num!)]) (vector 'M i j))]
    [(#\T) (let* ([ls (list!)] [g (form!)]) (vector 'T ls g))]
    [(#\E) (let* ([t (num!)] [g (form!)]) (vector 'E t g))]
    [(#\L) (let* ([l (num!)] [k (num!)] [g (form!)]) (vector 'L l k g))]
    [(#\H) (let* ([k (num!)] [l (num!)] [g (form!)]) (vector 'H k l g))]
    [(#\V) (let* ([t (num!)] [g (form!)]) (vector 'V t g))]
    [(#\Z) (let* ([a (form!)] [g (form!)]) (vector 'Z a g))]
    [(#\Y) (vector 'Y (form!))]
    [else (perr (format "step: unexpected tag ~a" c))]))

(define (thm!)
  (let* ([st (form!)] [sig (list!)] [n (num!)]
         [steps (for/vector #:length n ([_ (in-range n)]) (step!))]
         [hyps (list!)])
    (vector st sig steps hyps)))

(define (expect! s) (define t (token!)) (unless (equal? t s) (perr (format "expected ~a, got ~a" s t))))

;; ============================================================================================================= main
(define (judge path)
  (set! src (call-with-input-file path (lambda (in) (let ([b (read-bytes (file-size path) in)]) (if (eof-object? b) #"" b)))))
  (set! pos 0)
  (with-handlers ([(lambda (e) (and (pair? e) (eq? (car e) 'registry)))
                   (lambda (e) (printf "REJECT initial registry ~a: ~a\n" (cadr e) (caddr e)) 1)]
                  [(lambda (e) (and (pair? e) (eq? (car e) 'parse)))
                   (lambda (e) (printf "REJECT parse error at byte ~a: ~a\n" (caddr e) (cadr e)) 1)])
    (expect! #"JDG1")
    (expect! #"R")
    (define n0 (num!))
    (when (> n0 canonical-registry-length) (raise (list 'registry 'count "more than 706 entries")))
    (define entries (for/list ([i (in-range n0)])
      (define entry (let* ([d (form!)] [h (list!)]) (cons d h)))
      (unless (equal? entry (canonical-registry-entry i))
        (raise (list 'registry i "entry differs from canonical REG0")))
      entry))
    (expect! #"T")
    (define m (num!))
    (define reg (make-vector (+ n0 m) #f))
    (for ([e entries] [i (in-naturals)]) (vector-set! reg i e))
    (let loop ([j 0] [nreg n0] [nsteps 0])
      (cond
        [(< j m)
         (define t (thm!))
         (define r (check-thm reg nreg t))
         (cond
           [(eq? r #t)
            (vector-set! reg nreg (cons (vector-ref t 0) (vector-ref t 3)))   ; ent t = (t_stmt t, t_hyps t)
            (loop (add1 j) (add1 nreg) (+ nsteps (vector-length (vector-ref t 2))))]
           [else
            (printf "REJECT theorem ~a step ~a (~a)\n" j (car r) (cdr r))
            1])]
        [else
         (skip-ws!)
         (cond
           [(< pos (bytes-length src)) (perr "trailing input after the last theorem")]
           [else
            (printf "ACCEPT registry ~a theorems ~a steps ~a final-registry ~a\n" n0 m nsteps nreg)
            0])]))))

(module+ main
  (define args (current-command-line-arguments))
  (unless (= (vector-length args) 1)
    (eprintf "usage: racket judge.rkt FILE.jdg\n")
    (exit 2))
  (exit (judge (vector-ref args 0))))
