#lang racket/base
;; mm3.rkt -- lane L5 (Stage 5 of PMP-BUILDOUT-2026-10-09): a Metamath database reader and proof verifier.
;;
;; Reads a .mm file (set.mm or an exported file), keeps the frames ($c $v $f $e $d $a $p, ${ $}), decodes compressed
;; proofs, verifies proofs by the Metamath rules on token strings (substitution, $e matching, $d conditions), and
;; parses statements into trees with the database's own syntax axioms (packrat, all parses; set.mm's grammar is
;; unambiguous, so exactly one full parse is expected).
;;
;; Not trusted for the Book: it only supplies candidates to the pmp judge. Exact integers only.
;;
;; Usage:  racket mm.rkt verify FILE.mm [N]     verify the first N $p (all when N is omitted)
(require racket/list racket/string racket/file)
(provide (all-defined-out))

;; ============================================================================================ records
(struct fhyp (label type var) #:transparent)
(struct ehyp (label type toks) #:transparent)                 ; toks: vector of strings, typecode excluded
;; kind 'a or 'p; hyps: mandatory hypothesis labels in order; dvs: mandatory $d pairs (x . y), x string<? y
;; frame-f: every active $f label (dummy variables); frame-dv: hash of every active $d pair
;; proof: list of raw proof tokens or #f; idx: position among all assertions; pidx: position among $p (or #f)
(struct assr (label kind type toks hyps dvs frame-f frame-dv proof idx pidx) #:transparent)

(struct mmdb (consts vartype labels order syntax) #:transparent)
;; consts: hash string -> #t; vartype: hash var -> typecode (from $f); labels: hash label -> record
;; order: vector of assertion labels in file order; syntax: hash typecode -> list of syntax assr (non-|- $a)

;; ============================================================================================ tokens
(define (ws? b) (or (= b 32) (= b 10) (= b 13) (= b 9) (= b 12)))

;; read-db: path, limit = number of $p after which reading stops (#f: whole file)
(define (read-db path [limit #f] #:provable [provable "|-"])
  (define src (file->bytes path))
  (define n (bytes-length src))
  (define pos 0)
  (define (raw-token!)
    (let skip () (when (and (< pos n) (ws? (bytes-ref src pos))) (set! pos (add1 pos)) (skip)))
    (if (>= pos n)
        #f
        (let ([start pos])
          (let loop () (when (and (< pos n) (not (ws? (bytes-ref src pos)))) (set! pos (add1 pos)) (loop)))
          (bytes->string/latin-1 (subbytes src start pos)))))
  (define (token!)
    (let loop ()
      (define t (raw-token!))
      (cond
        [(equal? t "$(")
         (let c () (define u (raw-token!))
           (cond [(not u) (error 'mm "unterminated comment")]
                 [(equal? u "$)") (void)]
                 [else (c)]))
         (loop)]
        [else t])))
  (define (read-until! end)
    (let loop ([acc '()])
      (define t (token!))
      (cond [(not t) (error 'mm "unexpected end of file, expected ~a" end)]
            [(equal? t end) (reverse acc)]
            [else (loop (cons t acc))])))

  (define consts (make-hash))
  (define vartype (make-hash))
  (define labels (make-hash))
  (define order '())
  (define syntax (make-hash))
  ;; scopes: list of frames, innermost first; a frame is (vector hyps-rev dvs-rev vars)
  (define scopes (list (vector '() '() '())))
  (define (active-hyps) (append* (map (lambda (s) (reverse (vector-ref s 0))) (reverse scopes))))
  (define (active-dvs) (append* (map (lambda (s) (vector-ref s 1)) scopes)))
  (define fvar (make-hash))      ; var -> fhyp label (active)
  (define nass 0)
  (define np 0)

  (define (add-hyp! lab) (vector-set! (car scopes) 0 (cons lab (vector-ref (car scopes) 0))))
  (define (norm-pair a b) (if (string<? a b) (cons a b) (cons b a)))

  (define (make-assertion! lab kind toks proof)
    (define type (car toks))
    (define body (list->vector (cdr toks)))
    (define hyps (active-hyps))
    ;; mandatory variables: those of the statement and of every active $e
    (define mv (make-hash))
    (define (note-vars! v) (for ([t v]) (when (hash-ref fvar t #f) (hash-set! mv t #t))))
    (note-vars! body)
    (for ([h hyps]) (define r (hash-ref labels h)) (when (ehyp? r) (note-vars! (ehyp-toks r))))
    (define mand
      (filter (lambda (h) (define r (hash-ref labels h))
                (or (ehyp? r) (and (fhyp? r) (hash-ref mv (fhyp-var r) #f))))
              hyps))
    (define all-dv (active-dvs))
    (define dvs (remove-duplicates
                 (filter (lambda (p) (and (hash-ref mv (car p) #f) (hash-ref mv (cdr p) #f))) all-dv)))
    (define frame-dv (make-hash))
    (for ([p all-dv]) (hash-set! frame-dv p #t))
    (define frame-f (filter (lambda (h) (fhyp? (hash-ref labels h))) hyps))
    (define a (assr lab kind type body mand dvs frame-f frame-dv proof nass (and (eq? kind 'p) np)))
    (set! nass (add1 nass))
    (when (eq? kind 'p) (set! np (add1 np)))
    (hash-set! labels lab a)
    (set! order (cons lab order))
    (unless (equal? type provable)
      (hash-update! syntax type (lambda (l) (cons a l)) '())))

  (let loop ()
    (define t (token!))
    (cond
      [(not t) (void)]
      [(and limit (>= np limit)) (void)]
      [(equal? t "${") (set! scopes (cons (vector '() '() '()) scopes)) (loop)]
      [(equal? t "$}")
       ;; variable types stay global (set.mm types each variable once)
       (for ([h (vector-ref (car scopes) 0)])
         (define r (hash-ref labels h))
         (when (fhyp? r) (hash-remove! fvar (fhyp-var r))))
       (set! scopes (cdr scopes))
       (loop)]
      [(equal? t "$c") (for ([c (read-until! "$.")]) (hash-set! consts c #t)) (loop)]
      [(equal? t "$v") (vector-set! (car scopes) 2 (append (read-until! "$.") (vector-ref (car scopes) 2))) (loop)]
      [(equal? t "$d")
       (define vs (read-until! "$."))
       (define ps (for*/list ([a vs] [b vs] #:when (string<? a b)) (cons a b)))
       (vector-set! (car scopes) 1 (append ps (vector-ref (car scopes) 1)))
       (loop)]
      [(equal? t "$[") (read-until! "$]") (loop)]
      [else
       (define lab t)
       (define kw (token!))
       (cond
         [(equal? kw "$f")
          (define toks (read-until! "$."))
          (define r (fhyp lab (car toks) (cadr toks)))
          (hash-set! labels lab r)
          (hash-set! vartype (cadr toks) (car toks))
          (hash-set! fvar (cadr toks) lab)
          (add-hyp! lab)]
         [(equal? kw "$e")
          (define toks (read-until! "$."))
          (hash-set! labels lab (ehyp lab (car toks) (list->vector (cdr toks))))
          (add-hyp! lab)]
         [(equal? kw "$a") (make-assertion! lab 'a (read-until! "$.") #f)]
         [(equal? kw "$p")
          (define toks (read-until! "$="))
          (define proof (read-until! "$."))
          (make-assertion! lab 'p toks proof)]
         [else (error 'mm "unknown keyword ~a after ~a" kw lab)])
       (loop)]))
  (mmdb consts vartype labels (list->vector (reverse order))
        (for/hash ([(k v) syntax]) (values k (reverse v)))))

(define (lookup db lab) (hash-ref (mmdb-labels db) lab (lambda () (error 'mm "no label ~a" lab))))

;; ============================================================================================ proofs
;; decode-proof: the proof of a $p as a list of items: (vector 'L label) | (vector 'R k) (k-th saved step) | 'Z
(define (decode-proof db a)
  (define p (assr-proof a))
  (cond
    [(and (pair? p) (equal? (car p) "("))
     (define-values (plabs rest)
       (let loop ([l (cdr p)] [acc '()])
         (if (equal? (car l) ")") (values (reverse acc) (cdr l)) (loop (cdr l) (cons (car l) acc)))))
     (define m (length (assr-hyps a)))
     (define pv (list->vector plabs))
     (define hv (list->vector (assr-hyps a)))
     (define str (apply string-append rest))
     (let loop ([i 0] [acc 0] [out '()])
       (if (>= i (string-length str))
           (begin (unless (= acc 0) (error 'mm "~a: compressed proof ends inside a number" (assr-label a)))
                  (reverse out))
           (let ([c (char->integer (string-ref str i))])
             (cond
               [(<= 85 c 89) (loop (add1 i) (+ (* acc 5) (- c 84)) out)]          ; U..Y
               [(<= 65 c 84)                                                     ; A..T ends a number
                (define num (+ (* acc 20) (- c 64)))
                (define item
                  (cond [(<= num m) (vector 'L (vector-ref hv (- num 1)))]
                        [(<= num (+ m (vector-length pv))) (vector 'L (vector-ref pv (- num m 1)))]
                        [else (vector 'R (- num m (vector-length pv) 1))]))
                (loop (add1 i) 0 (cons item out))]
               [(= c 90) (unless (= acc 0) (error 'mm "Z inside a number")) (loop (add1 i) 0 (cons 'Z out))]
               [(= c 63) (error 'mm "~a: incomplete proof (?)" (assr-label a))]
               [else (error 'mm "~a: bad character ~a in compressed proof" (assr-label a) (integer->char c))]))))]
    [else
     (for/list ([t p])
       (when (equal? t "?") (error 'mm "~a: incomplete proof (?)" (assr-label a)))
       (vector 'L t))]))

;; ---- substitution on token vectors
(define (subst-toks toks sub)
  (list->vector (append* (for/list ([t toks]) (let ([r (hash-ref sub t #f)]) (if r (vector->list r) (list t)))))))

(define (vars-of db toks) (for/list ([t toks] #:when (hash-ref (mmdb-vartype db) t #f)) t))

;; verify-assr: #t or raises with a message. Token-string semantics of the Metamath specification.
(define (verify-assr db a)
  (define lab (assr-label a))
  (define (fail fmt . args) (error 'verify (string-append lab ": " (apply format fmt args))))
  (define frame-labels (make-hash))
  (for ([h (assr-hyps a)]) (hash-set! frame-labels h #t))
  (for ([h (assr-frame-f a)]) (hash-set! frame-labels h #t))
  (define saved (make-vector 0))
  (define nsaved 0)
  (define (save! e)
    (when (= nsaved (vector-length saved))
      (let ([nv (make-vector (max 16 (* 2 nsaved)) #f)]) (vector-copy! nv 0 saved) (set! saved nv)))
    (vector-set! saved nsaved e) (set! nsaved (add1 nsaved)))
  ;; stack entries: (cons type toks-vector)
  (define stack '())
  (for ([it (decode-proof db a)])
    (cond
      [(eq? it 'Z) (when (null? stack) (fail "Z on empty stack")) (save! (car stack))]
      [(eq? (vector-ref it 0) 'R)
       (define k (vector-ref it 1))
       (unless (< k nsaved) (fail "reference to unsaved step ~a" k))
       (set! stack (cons (vector-ref saved k) stack))]
      [else
       (define l (vector-ref it 1))
       (define r (hash-ref (mmdb-labels db) l (lambda () (fail "unknown label ~a" l))))
       (cond
         [(fhyp? r) (unless (hash-ref frame-labels l #f) (fail "hypothesis ~a not in frame" l))
                    (set! stack (cons (cons (fhyp-type r) (vector (fhyp-var r))) stack))]
         [(ehyp? r) (unless (hash-ref frame-labels l #f) (fail "hypothesis ~a not in frame" l))
                    (set! stack (cons (cons (ehyp-type r) (ehyp-toks r)) stack))]
         [else
          (unless (< (assr-idx r) (assr-idx a)) (fail "~a used before it is stated" l))
          (define hs (assr-hyps r))
          (define k (length hs))
          (when (< (length stack) k) (fail "stack underflow at ~a" l))
          (define args (reverse (take stack k)))
          (set! stack (drop stack k))
          (define sub (make-hash))
          (for ([h hs] [e args])
            (define hr (lookup db h))
            (when (fhyp? hr)
              (unless (equal? (car e) (fhyp-type hr)) (fail "~a: type ~a, expected ~a" l (car e) (fhyp-type hr)))
              (hash-set! sub (fhyp-var hr) (cdr e))))
          (for ([h hs] [e args])
            (define hr (lookup db h))
            (when (ehyp? hr)
              (unless (and (equal? (car e) (ehyp-type hr)) (equal? (cdr e) (subst-toks (ehyp-toks hr) sub)))
                (fail "~a: hypothesis ~a does not match" l h))))
          ;; $d: for each mandatory pair of r, the substituted expressions share no variable, and every pair of
          ;; their variables is a $d pair of a's frame
          (for ([p (assr-dvs r)])
            (define e1 (hash-ref sub (car p) #f))
            (define e2 (hash-ref sub (cdr p) #f))
            (when (and e1 e2)
              (for* ([x (vars-of db e1)] [y (vars-of db e2)])
                (when (equal? x y) (fail "~a: $d ~a ~a violated (common variable ~a)" l (car p) (cdr p) x))
                (unless (hash-ref (assr-frame-dv a) (if (string<? x y) (cons x y) (cons y x)) #f)
                  (fail "~a: $d ~a ~a needs $d ~a ~a" l (car p) (cdr p) x y)))))
          (set! stack (cons (cons (assr-type r) (subst-toks (assr-toks r) sub)) stack))])]))
  (unless (= (length stack) 1) (fail "stack has ~a entries at the end" (length stack)))
  (unless (and (equal? (car (car stack)) (assr-type a)) (equal? (cdr (car stack)) (assr-toks a)))
    (fail "the proof proves something else"))
  #t)

;; ============================================================================================ grammar
;; Trees: a variable is its name (string); an application of a syntax axiom is (cons label children), the children in
;; the order of the axiom's mandatory $f hypotheses (the order the proof's syntax steps supply them).

(define pattern-cache (make-hasheq))
(define (pattern db a)        ; vector of (cons 'c token) | (cons 'v (cons var type))
  (or (hash-ref pattern-cache a #f)
      (let ([p (for/vector ([t (assr-toks a)])
                 (define ty (hash-ref (mmdb-vartype db) t #f))
                 (if (and ty (not (hash-ref (mmdb-consts db) t #f))) (cons 'v (cons t ty)) (cons 'c t)))])
        (hash-set! pattern-cache a p) p)))

(define (parse db type toks)  ; toks: vector of strings -> tree, or raises
  (define n (vector-length toks))
  (define memo (make-hash))
  (define vt (mmdb-vartype db))
  (define (P ty pos)
    (define key (cons ty pos))
    (define m (hash-ref memo key #f))
    (cond
      [m m]
      [else
       (hash-set! memo key '())
       (define res
         (append
          (if (and (< pos n) (equal? (hash-ref vt (vector-ref toks pos) #f) ty)
                   (not (hash-ref (mmdb-consts db) (vector-ref toks pos) #f)))
              (list (cons (vector-ref toks pos) (add1 pos)))
              '())
          (append* (for/list ([a (hash-ref (mmdb-syntax db) ty '())]) (M a pos)))))
       (hash-set! memo key res)
       res]))
  (define (M a pos)
    (define pat (pattern db a))
    (define k (vector-length pat))
    (let loop ([i 0] [pos pos] [binds '()])
      (cond
        [(= i k)
         (list (cons (cons (assr-label a)
                           (for/list ([h (assr-hyps a)]) (cdr (assoc (fhyp-var (lookup db h)) binds))))
                     pos))]
        [(eq? (car (vector-ref pat i)) 'c)
         (if (and (< pos n) (equal? (vector-ref toks pos) (cdr (vector-ref pat i))))
             (loop (add1 i) (add1 pos) binds)
             '())]
        [else
         (define v (cadr (vector-ref pat i)))
         (define ty (cddr (vector-ref pat i)))
         (append* (for/list ([r (P ty pos)]) (loop (add1 i) (cdr r) (cons (cons v (car r)) binds))))])))
  (define full (remove-duplicates (filter (lambda (r) (= (cdr r) n)) (P type 0))))
  (cond
    [(null? full) (error 'parse "no parse of ~a ~a" type (string-join (vector->list toks) " "))]
    [(pair? (cdr full)) (error 'parse "~a parses of ~a ~a: ~s" (length full) type (string-join (vector->list toks) " ") full)]
    [else (car (car full))]))

;; the typecode a |- statement is parsed as
(define (stmt-type db) (if (hash-ref (mmdb-syntax db) "wff" #f) "wff" (error 'mm "no wff syntax")))

;; tree substitution
(define (subst-tree t sub)
  (cond [(string? t) (hash-ref sub t t)]
        [else (cons (car t) (for/list ([c (cdr t)]) (subst-tree c sub)))]))

;; tree -> token list (for display and for the export's string checks)
(define (tree->toks db t)
  (cond
    [(string? t) (list t)]
    [else
     (define a (lookup db (car t)))
     (define binds (for/list ([h (assr-hyps a)] [c (cdr t)]) (cons (fhyp-var (lookup db h)) c)))
     (append* (for/list ([p (pattern db a)])
                (if (eq? (car p) 'c) (list (cdr p)) (tree->toks db (cdr (assoc (cadr p) binds))))))]))

;; ============================================================================================ main
(module+ main
  (define args (current-command-line-arguments))
  (cond
    [(and (>= (vector-length args) 2) (equal? (vector-ref args 0) "verify"))
     (define path (vector-ref args 1))
     (define lim (and (>= (vector-length args) 3) (string->number (vector-ref args 2))))
     (define t0 (current-milliseconds))
     (define db (read-db path lim))
     (define t1 (current-milliseconds))
     (define ok 0) (define bad 0) (define na 0)
     (for ([lab (mmdb-order db)])
       (define a (lookup db lab))
       (cond
         [(eq? (assr-kind a) 'a) (set! na (add1 na))]
         [else
          (with-handlers ([exn:fail? (lambda (e) (set! bad (add1 bad)) (printf "FAIL ~a\n" (exn-message e)))])
            (verify-assr db a) (set! ok (add1 ok)))]))
     (define t2 (current-milliseconds))
     (printf "~a: $a ~a, $p verified ~a, failed ~a; read ~a ms, verify ~a ms\n"
             path na ok bad (- t1 t0) (- t2 t1))
     (exit (if (= bad 0) 0 1))]
    [else (eprintf "usage: racket mm.rkt verify FILE.mm [N]\n") (exit 2)]))
