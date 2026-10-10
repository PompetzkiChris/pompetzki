#lang racket/base
;; certs-v2.rkt (certs-v1.rkt passing the twin to mutants as a core formula; core-v1 compresses it itself) -- lane L2D: emitters for three certificate formats, over cert-v1.rkt (binary numerals, kernel).
;; Not trusted. Each emitter checks its certificate with exact integer arithmetic, then derives the certificate
;; theorem (cert-v1.rkt's closed form  forall w p g o (Ctx -> E_1 & ... & E_M)); both judges check the files.
;;
;; Certificate files are S-expressions:
;;   (smith (A rows) (U rows) (V rows) (D rows))      U A V = D, D diagonal, d_i | d_i+1, U and V unimodular.
;;       Entries: A V = W (W computed here), U W = D, U U' = I, V V' = I (U', V' the integer inverses, computed
;;       here), d_i+1 = d_i * k_i.
;;   (rank (A rows) (r n) (I rows-of-minor) (J cols-of-minor) (K kernel-basis-columns-as-rows) (I2 rows-of-K-minor))
;;       rank A = r over Q, certified by: M = A[I,J] with M adj(M) = det(M) I and det(M) /= 0; A K = 0;
;;       K2 = K[I2, :] (n-r square) with K2 adj(K2) = det(K2) I and det(K2) /= 0 (K has rank n - r).
;;   (pratt p a ((q e) ...) sub-certificates...)      Pratt certificate; the arithmetic checks:
;;       p - 1 = prod q^e (a chain of products), 1 + (p - 1) = p;  a^(p-1) mod p = 1 and, for each q,
;;       a^((p-1)/q) mod p = r with 1 + r' = r, r' /= 0, r + (p - r) = p, p - r /= 0 (so 1 < r < p), by square-and-
;;       multiply with explicit quotients:  x*x = s, Q*p = t, t + x' = s, x' + (p - x') = p, p - x' /= 0 ...
;;       Recursively for each q > 2. What the theorem states is these checks; "p is prime" follows by Lucas'
;;       theorem, which is not derived here.
;; Usage: racket certs-v2.rkt emit CERT.sexp OUT.jdg
(require racket/list racket/match racket/string racket/file racket/path racket/port
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/cert-v1.rkt"))
(provide (all-defined-out))

;; ------------------------------------------------------------------ exact matrices
(define (rows m) (length m))
(define (cols m) (length (car m)))
(define (mref m i j) (list-ref (list-ref m i) j))
(define (mat* a b) (for/list ([i (rows a)]) (for/list ([j (cols b)]) (for/sum ([k (cols a)]) (* (mref a i k) (mref b k j))))))
(define (ident n) (for/list ([i n]) (for/list ([j n]) (if (= i j) 1 0))))
(define (minor m i j) (for/list ([r m] [a (in-naturals)] #:unless (= a i)) (for/list ([x r] [b (in-naturals)] #:unless (= b j)) x)))
(define (det m) (if (= (rows m) 1) (mref m 0 0) (for/sum ([j (cols m)]) (* (if (even? j) 1 -1) (mref m 0 j) (det (minor m 0 j))))))
(define (adj m) (if (= (rows m) 1) '((1)) (for/list ([i (rows m)]) (for/list ([j (rows m)]) (* (if (even? (+ i j)) 1 -1) (det (minor m j i)))))))
(define (scal c m) (for/list ([r m]) (for/list ([x r]) (* c x))))
(define (submat m is js) (for/list ([i is]) (for/list ([j js]) (mref m i j))))
(define (transpose m) (apply map list m))

;; entries of X*Y = Z: (Lin terms c), trivial ones (no terms, c = 0) left out
(define (sgn x) (if (< x 0) -1 1))
(define (mat-entries X Y Z)
  (for*/list ([i (rows X)] [j (cols Y)]
              #:unless (and (= (mref Z i j) 0) (for/and ([k (cols X)]) (or (= 0 (mref X i k)) (= 0 (mref Y k j))))))
    `(Lin ,(for/list ([k (cols X)] #:unless (or (= 0 (mref X i k)) (= 0 (mref Y k j))))
             (list (* (sgn (mref X i k)) (sgn (mref Y k j))) (abs (mref X i k)) (abs (mref Y k j))))
          ,(mref Z i j))))

;; ------------------------------------------------------------------ Smith
(define (smith-specs A U V D)
  (unless (equal? (mat* (mat* U A) V) D) (error 'smith "U A V /= D"))
  (define m (rows A)) (define n (cols A))
  (for* ([i m] [j n]) (unless (or (= i j) (= 0 (mref D i j))) (error 'smith "D not diagonal")))
  (define ds (for/list ([i (min m n)]) (mref D i i)))
  (for ([d ds]) (when (< d 0) (error 'smith "negative diagonal entry")))
  (for ([a ds] [b (cdr ds)]) (unless (if (= a 0) (= b 0) (= 0 (modulo b a))) (error 'smith "~a does not divide ~a" a b)))
  (define (unimod-inv M) (let ([d (det M)]) (unless (= (abs d) 1) (error 'smith "not unimodular")) (scal d (adj M))))
  (define Ui (unimod-inv U)) (define Vi (unimod-inv V))
  (unless (equal? (mat* U Ui) (ident m)) (error 'smith "U inverse"))
  (unless (equal? (mat* V Vi) (ident n)) (error 'smith "V inverse"))
  (define W (mat* A V))
  (values W Ui Vi
          (append (mat-entries A V W) (mat-entries U W D) (mat-entries U Ui (ident m)) (mat-entries V Vi (ident n))
                  (for/list ([a ds] [b (cdr ds)] #:when (and (> a 0) (> b 0))) `(Lin ((1 ,a ,(quotient b a))) ,b)))))

;; ------------------------------------------------------------------ rank
(define (rank-specs A r I J K I2)
  (define n (cols A))
  (define M (submat A I J))
  (define d (det M))
  (when (= d 0) (error 'rank "the minor is singular"))
  (define N (adj M))
  (unless (equal? (mat* M N) (scal d (ident r))) (error 'rank "M adj(M)"))
  (define Kc (transpose K))                                   ; n x (n-r), columns are the kernel vectors
  (unless (= (length K) (- n r)) (error 'rank "need n - r kernel vectors"))
  (unless (for/and ([row (mat* A Kc)]) (andmap zero? row)) (error 'rank "A K /= 0"))
  (define-values (K2 N2 d2 kspecs)
    (cond
      [(= r n) (values '() '() 1 '())]
      [else
       (define K2 (submat Kc I2 (range (- n r))))
       (define d2 (det K2))
       (when (= d2 0) (error 'rank "the kernel minor is singular"))
       (define N2 (adj K2))
       (values K2 N2 d2 (append (mat-entries A Kc (for/list ([i (rows A)]) (for/list ([j (- n r)]) 0)))
                                (mat-entries K2 N2 (scal d2 (ident (- n r))))
                                (list `(CNZ ,(abs d2)))))]))
  (values M N d K2 N2 d2 (append (mat-entries M N (scal d (ident r))) (list `(CNZ ,(abs d))) kspecs)))

;; ------------------------------------------------------------------ Pratt
(define (pratt-specs cert)
  (match-define (list 'pratt p a fac subs ...) cert)
  (define specs '())
  (define (add! s) (set! specs (cons s specs)))
  (define pm1 (sub1 p))
  (unless (= pm1 (for/product ([qe fac]) (expt (car qe) (cadr qe)))) (error 'pratt "p - 1 /= prod q^e"))
  ;; the product chain
  (define factors (append* (for/list ([qe fac]) (make-list (cadr qe) (car qe)))))
  (for/fold ([acc (car factors)]) ([f (cdr factors)]) (add! `(CMul ,acc ,f)) (* acc f))
  (add! `(CAdd 1 ,pm1))
  ;; modular exponentiation of a to e: square and multiply from the top bit; returns the residue
  (define (modexp e)
    (define bits (let loop ([e e] [acc '()]) (if (= e 0) acc (loop (quotient e 2) (cons (remainder e 2) acc)))))
    (define (reduce s)                       ; s -> s mod p with the checks Q*p = t, t + r = s, r + (p - r) = p, p - r /= 0
      (define Q (quotient s p)) (define r (remainder s p))
      (when (> Q 0) (add! `(CMul ,Q ,p)))
      (when (and (> Q 0) (> r 0)) (add! `(CAdd ,(* Q p) ,r)))
      (add! `(CAdd ,r ,(- p r)))
      (add! `(CNZ ,(- p r)))
      r)
    (define x0 (reduce a))
    (for/fold ([x x0]) ([b (cdr bits)])
      (when (= x 0) (error 'pratt "residue 0"))
      (add! `(CMul ,x ,x))
      (define y (reduce (* x x)))
      (if (= b 1)
          (begin (when (= y 0) (error 'pratt "residue 0")) (add! `(CMul ,y ,a)) (reduce (* y a)))
          y)))
  (unless (= 1 (modexp pm1)) (error 'pratt "a^(p-1) mod p /= 1"))
  (for ([qe fac])
    (define r (modexp (quotient pm1 (car qe))))
    (unless (> r 1) (error 'pratt "a^((p-1)/~a) mod p = ~a" (car qe) r))
    (add! `(CAdd 1 ,(sub1 r)))
    (add! `(CNZ ,(sub1 r))))
  ;; sub-certificates for the prime factors q > 2
  (define subq (for/list ([s subs]) (cadr s)))
  (for ([qe fac] #:when (> (car qe) 2)) (unless (memv (car qe) subq) (error 'pratt "no certificate for ~a" (car qe))))
  (for ([s subs]) (for ([x (pratt-specs s)]) (add! x)))
  (remove-duplicates (reverse specs)))

;; ------------------------------------------------------------------ files
(define (spec-text s)
  (match s
    [(list 'Lin terms c) (string-append (string-join (for/list ([t terms]) (format "~a~a*~a" (if (> (car t) 0) "+" "-") (cadr t) (caddr t))) " ") (format " = ~a" c))]
    [(list 'CMul a b) (format "~a*~a = ~a" a b (* a b))]
    [(list 'CAdd a b) (format "~a+~a = ~a" a b (+ a b))]
    [(list 'CNZ n) (format "~a /= 0" n)]))

(define (emit-cert cert-path out)
  (load-base!)
  (reset-batch!)
  (define cert (call-with-input-file cert-path read))
  (define-values (kind specs notes)
    (match cert
      [(list 'smith (list 'A A) (list 'U U) (list 'V V) (list 'D D))
       (define-values (W Ui Vi specs) (smith-specs A U V D))
       (values 'Smith specs (list (format "W = A V = ~a" W) (format "U^-1 = ~a" Ui) (format "V^-1 = ~a" Vi)))]
      [(list 'rank (list 'A A) (list 'r r) (list 'I I) (list 'J J) (list 'K K) (list 'I2 I2))
       (define-values (M N d K2 N2 d2 specs) (rank-specs A r I J K I2))
       (values 'Rank specs (list (format "minor M = ~a, adj(M) = ~a, det = ~a" M N d) (format "kernel minor ~a, adj ~a, det ~a" K2 N2 d2)))]
      [(list 'pratt p _ ...)
       (values 'Pratt (pratt-specs cert) (list (format "p = ~a" p)))]))
  (define key `(Cert ,kind ,(path->string (file-name-from-path cert-path))))
  (define t0 (current-milliseconds))
  (cert-thm! key specs)
  (define ms (- (current-milliseconds) t0))
  (define text (batch-text))
  (write-new out text)
  (define-values (rg ths) (read-jdg-text text))
  (define base (regexp-replace #rx"[.]jdg$" out ""))
  (define mdir (string-append base "-mut"))
  (make-directory* mdir)
  (define pflags (map caddr (reverse out-thms)))
  (define keys (map car (reverse out-thms)))
  ;; twin: the certificate theorem with its first entry negated (false, since the entry is a theorem)
  (define stmt (tof (car (last ths))))
  (define twin
    (let loop ([f stmt] [k 4])
      (if (> k 0) (match f [(list 'A b) (All (loop b (sub1 k)))])
          (match f [(list 'I ctx body)
                    (Imp ctx (let neg-first ([b body]) (match b [(list 'N (list 'I x (list 'N y))) #:when (pair? x) (Kf (neg-first x) y)] [_ (Neg b)])))]))))
  ;; targeted: in the certificate theorem, the first U step uses the registry entry of the second entry lemma
  (define tv (list->vector ths))
  (define last-i (sub1 (vector-length tv)))
  (match-define (list lst lsig lsteps lhyps) (vector-ref tv last-i))
  (define us (for/list ([s lsteps] [i (in-naturals)] #:when (eq? (car s) 'U)) (cons i (cadr s))))
  (define targeted
    (if (and (>= (length us) 2) (not (= (cdr (car us)) (cdr (cadr us)))))
        (list (list "cert-use-swap"
                    (structure-text rg (for/list ([x tv] [j (in-naturals)])
                                         (if (= j last-i)
                                             (list lst lsig (for/list ([s lsteps] [i (in-naturals)]) (if (= i (car (car us))) (list 'U (cdr (cadr us)) (caddr s)) s)) lhyps)
                                             x)))))
        '()))
  (define muts (append targeted (mutants text twin pflags)))
  (define lines
    (append
     (list (format "~a  from ~a (~a certificate), ~a entries" out cert-path kind (length specs)))
     (map (lambda (s) (string-append "  note: " s)) notes)
     (for/list ([s specs] [i (in-naturals 1)]) (format "  E~a: ~a" i (spec-text s)))
     (list (format "  theorems ~a (prelude ~a, generated ~a), steps ~a (prelude ~a), bytes ~a, build ~a ms"
                   (length ths) (hash-ref stats 'prelude 0) (hash-ref stats 'theorems 0)
                   (+ (hash-ref stats 'steps 0) (hash-ref stats 'prelude-steps 0)) (hash-ref stats 'prelude-steps 0)
                   (file-size out) ms)
           (format "  largest tautology test ~a calls" (hash-ref stats 'taut-max 0))
           (format "  sha256 ~a" (sha256-hex out))
           (format "  registry: ~a" (check-registry-text text))
           (format "  copy of the checker: ~a" (check-batch rg ths)))))
  (for-each displayln lines)
  (define mlines
    (for/list ([mu muts])
      (match-define (list tag mtext) mu)
      (define mf (build-path mdir (string-append (path->string (file-name-from-path base)) "-" tag ".jdg")))
      (write-new mf mtext)
      (define-values (mrg mths) (read-jdg-text mtext))
      (format "  mutant ~a: copy of the checker ~a" tag (check-batch mrg mths))))
  (for-each displayln mlines)
  (write-new (string-append base ".index.txt")
             (string-join (for/list ([k keys] [t ths] [i (in-naturals)])
                            (format "~a ~s" i k)) "\n"))
  (write-new (string-append base ".manifest.txt") (string-join (append lines mlines) "\n")))

(module+ main
  (define args (vector->list (current-command-line-arguments)))
  (match args
    [(list "emit" cert out) (emit-cert cert out)]
    [_ (printf "usage: racket certs-v2.rkt emit CERT.sexp OUT.jdg\n")]))
