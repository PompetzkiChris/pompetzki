#lang racket/base
;; L8G release example. Reads the matrices l8g_workload already wrote under out2,
;; checks them in exact integers, writes L2D certificate sexps, and asks
;; certs-v3.rkt to emit JDG1. `judge` runs both judges from the judge directory.
;; This program does not load l8g.dll and does not allocate device memory.
;;
;;   racket example.rkt emit
;;   racket example.rkt judge
;;   racket example.rkt hashes
;;   racket example.rkt all

(require racket/list racket/string racket/file racket/path racket/port racket/match file/sha1)

(define lane "C:/ClaudeOutput/pompetzki/lanes/L8G")
(define dumps (build-path lane "out2"))
(define rel (build-path lane "release"))
(define sexp-dir (build-path rel "sexps"))
(define jdg-dir (build-path rel "jdg"))
(define corrupt-dir (build-path rel "corrupt"))
(define emitter "C:/ClaudeOutput/pompetzki/lanes/L2D/certs-v3.rkt")
(define judge-dir "C:/ClaudeOutput/pompetzki/judge")
(define pmp "C:/ClaudeOutput/pompetzki/pompetzki.exe")
(define racket-exe "C:/Program Files/Racket/racket.exe")

(define (read-matrix path)
  (for/list ([line (in-list (file->lines path))] #:unless (string=? (string-trim line) ""))
    (map string->number (string-split line))))

(define (read-scalar path)
  (string->number (string-trim (file->string path))))

(define (minor-of m i j)
  (for/list ([row m] [a (in-naturals)] #:unless (= a i))
    (for/list ([x row] [b (in-naturals)] #:unless (= b j)) x)))

(define (det m)
  (cond
    [(= (length m) 1) (caar m)]
    [else
     (for/fold ([s 0] [sign 1] #:result s) ([j (in-range (length (car m)))])
       (values (+ s (* sign (list-ref (car m) j) (det (minor-of m 0 j)))) (- sign)))]))

(define (mat* a b)
  (define nb (length (car b)))
  (for/list ([row a])
    (for/list ([j (in-range nb)])
      (for/fold ([s 0]) ([k (in-range (length row))])
        (+ s (* (list-ref row k) (list-ref (list-ref b k) j)))))))

(define (transpose m)
  (apply map list m))

(define (mat-text rows)
  (string-append "(" (string-join (for/list ([r rows])
                                    (string-append "(" (string-join (map number->string r) " ") ")"))
                                  " ")
                 ")"))

(define (idx-text xs)
  (string-append "(" (string-join (map number->string xs) " ") ")"))

(define (write-exact path text)
  (call-with-output-file path #:exists 'error (lambda (o) (write-string text o)))
  (void))

(define (must what ok)
  (unless ok (error 'example "~a" what))
  (printf "check ~a\n" what)
  (flush-output))

(define (run-emit cert out log)
  (define-values (sp o i e) (subprocess #f #f #f racket-exe emitter "emit" cert out))
  (close-output-port i)
  (define so (port->string o))
  (define se (port->string e))
  (subprocess-wait sp)
  (close-input-port o)
  (close-input-port e)
  (define code (subprocess-status sp))
  (call-with-output-file log #:exists 'error
    (lambda (p)
      (fprintf p "exit ~a\n" code)
      (display so p)
      (display se p)))
  (cons code (string-append so se)))

(define (emit-good)
  (make-directory* sexp-dir)
  (make-directory* jdg-dir)
  (define A (read-matrix (build-path dumps "pmp_A.txt")))
  (define K (read-matrix (build-path dumps "pmp_K.txt")))
  (define Minor (read-matrix (build-path dumps "pmp_minor.txt")))
  (define r (read-scalar (build-path dumps "pmp_gpu_rank.txt")))
  (define m (length A))
  (define n (length (car A)))
  (define k (length (car K)))
  (must "rn6x8 shape 6x8 rank 4 nullity 4" (and (= m 6) (= n 8) (= r 4) (= k 4) (= (length K) 8)))
  (define I (build-list r values))
  (define lead (for/list ([row (take A r)]) (take row r)))
  (must "rn6x8 leading block equals pmp_minor.txt" (equal? lead Minor))
  (define d (det Minor))
  (must "rn6x8 leading minor determinant is nonzero" (not (= d 0)))
  (define Z (mat* A K))
  (must "rn6x8 A K = 0" (for/and ([row Z]) (andmap (lambda (x) (= x 0)) row)))
  (must "rn6x8 bottom of K is I" 
        (for/and ([a (in-range k)])
          (for/and ([b (in-range k)])
            (= (list-ref (list-ref K (+ r a)) b) (if (= a b) 1 0)))))
  (define I2 (build-list k (lambda (i) (+ r i))))
  (define Krows (transpose K))
  (define rank-path (path->string (build-path sexp-dir "rn6x8.sexp")))
  (write-exact rank-path
               (string-append "(rank\n (A " (mat-text A) ")\n (r " (number->string r)
                              ")\n (I " (idx-text I) ")\n (J " (idx-text I) ")\n (K " (mat-text Krows)
                              ")\n (I2 " (idx-text I2) "))\n"))
  (printf "wrote ~a minor-det ~a\n" rank-path d)

  (define T (read-matrix (build-path dumps "pmpT_A.txt")))
  (define tr (read-scalar (build-path dumps "pmpT_gpu_rank.txt")))
  (must "tri5 is 5x5 of rank 5" (and (= (length T) 5) (= (length (car T)) 5) (= tr 5)))
  (must "tri5 determinant is 1" (= (det T) 1))
  (define tri-path (path->string (build-path sexp-dir "tri5.sexp")))
  (write-exact tri-path
               (string-append "(rank\n (A " (mat-text T) ")\n (r 5)\n (I (0 1 2 3 4))\n (J (0 1 2 3 4))\n (K ())\n (I2 ()))\n"))
  (printf "wrote ~a\n" tri-path)

  (define S (read-matrix (build-path dumps "pmp_smith_S.txt")))
  (define U (read-matrix (build-path dumps "pmp_smith_U.txt")))
  (define V (read-matrix (build-path dumps "pmp_smith_V.txt")))
  (define D (read-matrix (build-path dumps "pmp_smith_D.txt")))
  (must "smith3 shapes are 3x3" (and (= (length S) 3) (= (length U) 3) (= (length V) 3) (= (length D) 3)))
  (must "smith3 U S V = D" (equal? (mat* (mat* U S) V) D))
  (define du (det U))
  (define dv (det V))
  (must "smith3 det U is +1 or -1" (= (* du du) 1))
  (must "smith3 det V is +1 or -1" (= (* dv dv) 1))
  (define ds (for/list ([i (in-range 3)]) (list-ref (list-ref D i) i)))
  (must "smith3 D is diagonal and nonnegative"
        (and (for/and ([i (in-range 3)] [row D])
               (for/and ([j (in-range 3)] [x row])
                 (or (= i j) (= x 0))))
             (andmap (lambda (x) (>= x 0)) ds)))
  (must "smith3 each diagonal entry divides the next"
        (for/and ([a ds] [b (cdr ds)])
          (or (and (= a 0) (= b 0)) (and (> a 0) (= (remainder b a) 0)))))
  (define smith-path (path->string (build-path sexp-dir "smith3.sexp")))
  (write-exact smith-path
               (string-append "(smith\n (A " (mat-text S) ")\n (U " (mat-text U) ")\n (V " (mat-text V)
                              ")\n (D " (mat-text D) "))\n"))
  (printf "wrote ~a detU ~a detV ~a\n" smith-path du dv)

  (define jobs
    (list (list rank-path (path->string (build-path jdg-dir "rn6x8.jdg")) (path->string (build-path rel "emit-rn6x8.txt")))
          (list tri-path (path->string (build-path jdg-dir "tri5.jdg")) (path->string (build-path rel "emit-tri5.txt")))
          (list smith-path (path->string (build-path jdg-dir "smith3.jdg")) (path->string (build-path rel "emit-smith3.txt")))))
  (for ([job jobs])
    (define got (run-emit (car job) (cadr job) (caddr job)))
    (unless (= (car got) 0) (error 'example "emit failed ~a exit ~a" (car job) (car got)))
    (printf "emit exit 0 ~a\n" (cadr job)))
  (void))

(define (corrupt-one)
  (make-directory* corrupt-dir)
  (define src (file->string (build-path sexp-dir "smith3.sexp")))
  (define bad (regexp-replace #rx"\\(A \\(\\(2 " src "(A ((3 "))
  (unless (and bad (not (string=? bad src))) (error 'example "corruption did not change A"))
  (define bad-path (path->string (build-path corrupt-dir "smith3-bad.sexp")))
  (write-exact bad-path bad)
  (define out (path->string (build-path corrupt-dir "smith3-bad.jdg")))
  (define log (path->string (build-path corrupt-dir "smith3-bad-emit.txt")))
  (define got (run-emit bad-path out log))
  (unless (not (= (car got) 0)) (error 'example "corrupt smith was accepted"))
  (unless (not (file-exists? out)) (error 'example "corrupt smith wrote a jdg"))
  (printf "corrupt smith3 rejected exit ~a\n" (car got))
  (define A (read-matrix (build-path dumps "pmp_A.txt")))
  (define K (read-matrix (build-path dumps "pmp_K.txt")))
  (define r 4)
  (define I (build-list r values))
  (define I2 (build-list 4 (lambda (i) (+ r i))))
  (define Krows (transpose K))
  (define broken (cons (map (lambda (x) (+ x 1)) (car Krows)) (cdr Krows)))
  (define rank-bad (path->string (build-path corrupt-dir "rn6x8-bad.sexp")))
  (write-exact rank-bad
               (string-append "(rank\n (A " (mat-text A) ")\n (r 4)\n (I " (idx-text I) ")\n (J " (idx-text I)
                              ")\n (K " (mat-text broken) ")\n (I2 " (idx-text I2) "))\n"))
  (define rout (path->string (build-path corrupt-dir "rn6x8-bad.jdg")))
  (define rlog (path->string (build-path corrupt-dir "rn6x8-bad-emit.txt")))
  (define rgot (run-emit rank-bad rout rlog))
  (unless (not (= (car rgot) 0)) (error 'example "corrupt rank was accepted"))
  (unless (not (file-exists? rout)) (error 'example "corrupt rank wrote a jdg"))
  (printf "corrupt rn6x8 rejected exit ~a\n" (car rgot))
  (void))

(define (one-line s) (string-join (string-split s) " "))
(define (verdict s)
  (cond [(regexp-match? #rx"^ACCEPT" (string-trim s)) "ACCEPT"]
        [(regexp-match? #rx"REJECT" s) "REJECT"]
        [(regexp-match? #rx"LIMIT" s) "LIMIT"]
        [else "OTHER"]))

(define (run-judge exe args)
  (parameterize ([current-directory judge-dir])
    (define t0 (current-milliseconds))
    (define-values (sp o i e) (apply subprocess #f #f #f exe args))
    (close-output-port i)
    (define so (port->string o))
    (define se (port->string e))
    (subprocess-wait sp)
    (close-input-port o)
    (close-input-port e)
    (list (subprocess-status sp) (- (current-milliseconds) t0) (string-trim (string-append so se)))))

(define (jdg-files)
  (define found '())
  (define (walk dir)
    (for ([p (in-list (directory-list dir #:build? #t))])
      (cond [(directory-exists? p) (walk p)]
            [(regexp-match? #rx"[.]jdg$" (path->string p)) (set! found (cons (path->string p) found))])))
  (walk jdg-dir)
  (sort found (lambda (a b)
                (define am (regexp-match? #rx"-mut" a))
                (define bm (regexp-match? #rx"-mut" b))
                (cond [(and am (not bm)) #f]
                      [(and bm (not am)) #t]
                      [else (string<? a b)]))))

(define (judge-all)
  (define files (jdg-files))
  (define outp (open-output-file (build-path rel "judge-run.txt") #:exists 'error))
  (define lock (make-semaphore 1))
  (define ix 0)
  (define ilock (make-semaphore 1))
  (define (next)
    (call-with-semaphore ilock
      (lambda ()
        (if (>= ix (length files)) #f (begin0 (list-ref files ix) (set! ix (add1 ix)))))))
  (define (work)
    (let loop ()
      (define f (next))
      (when f
        (define full (path->string (simple-form-path f)))
        (match-define (list e1 t1 o1) (run-judge pmp (list "judge-v3.pmp" full)))
        (match-define (list e2 t2 o2) (run-judge racket-exe (list "racket/judge.rkt" full)))
        (define row (format "~a | pmp ~a exit ~a ~a ms | racket ~a exit ~a ~a ms | pmp: ~a | racket: ~a"
                            full (verdict o1) e1 t1 (verdict o2) e2 t2 (one-line o1) (one-line o2)))
        (call-with-semaphore lock
          (lambda ()
            (displayln row outp) (flush-output outp)
            (displayln row) (flush-output)))
        (loop))))
  (define ths (for/list ([_ (in-range 2)]) (thread work)))
  (for-each thread-wait ths)
  (close-output-port outp)
  (printf "judged ~a files\n" (length files))
  (void))

(define dep-files
  (list
   "C:/ClaudeOutput/pompetzki/lanes/L8G/src/l8g.cu"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/l8g.dll"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/example.pmp"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/release/example.rkt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/summary.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmp_A.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmp_K.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmp_minor.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmp_gpu_rank.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmpT_A.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmpT_gpu_rank.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmp_smith_S.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmp_smith_U.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmp_smith_V.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L8G/out2/pmp_smith_D.txt"
   "C:/ClaudeOutput/pompetzki/lanes/L2D/certs-v3.rkt"
   "C:/ClaudeOutput/pompetzki/lanes/L2D/cert-v1.rkt"
   "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt"
   "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt"
   "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel-v6.rkt"
   "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel2-v2.rkt"
   "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel3-v4.rkt"
   "C:/ClaudeOutput/pompetzki/lanes/L2D/bin-v6.rkt"
   "C:/ClaudeOutput/pompetzki/forcing-src/general/RpInit.v"
   "C:/ClaudeOutput/pompetzki/pompetzki.exe"
   "C:/ClaudeOutput/pompetzki/judge/judge-v3.pmp"
   "C:/ClaudeOutput/pompetzki/judge/racket/judge.rkt"))

(define (sha-file path)
  (bytes->hex-string (call-with-input-file path sha256-bytes)))

(define (write-hashes)
  (define paths (append dep-files
                        (sort (for/list ([p (in-directory rel)] #:when (or (regexp-match? #rx"[.]sexp$" (path->string p))
                                                                          (regexp-match? #rx"[.]jdg$" (path->string p))
                                                                          (regexp-match? #rx"[.]txt$" (path->string p))))
                                 (path->string p))
                              string<?)))
  (define lines
    (for/list ([p paths] #:when (file-exists? p))
      (format "~a  ~a" (sha-file p) (path->string (simple-form-path p)))))
  (write-exact (build-path rel "HASHES.txt") (string-join lines "\n"))
  (printf "hashes ~a\n" (length lines))
  (void))

(define (main)
  (match (vector->list (current-command-line-arguments))
    [(list "emit") (emit-good) (corrupt-one)]
    [(list "judge") (judge-all)]
    [(list "hashes") (write-hashes)]
    [(list "all") (emit-good) (corrupt-one) (judge-all) (write-hashes)]
    [_ (printf "usage: racket example.rkt emit|judge|hashes|all\n")]))

(main)
