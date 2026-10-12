#lang racket/base
(require json racket/cmdline racket/file racket/list racket/path racket/port racket/string racket/system
         "book-post-v4.rkt")
(provide verified-post!)

(define header "path\tpmp\tracket\treceipt\tsha256\tpmp_exit\tpmp_start\tpmp_end\tpmp_ms\tpmp_out\trkt_exit\trkt_start\trkt_end\trkt_ms\trkt_out")
(define (hex b) (apply string-append (for/list ([x b]) (define s (number->string x 16)) (if (= (string-length s) 1) (string-append "0" s) s))))
(define (digest p) (call-with-input-file p (lambda (in) (hex (sha256-bytes in)))))
(define (clean s) (string-trim (regexp-replace* #px"[\t\r\n]+" s " / ")))
(define (classify text code)
  ;; grok-fixed: an output naming both verdicts is UNKNOWN
  (define a (regexp-match? #px"\\bACCEPT\\b" text)) (define r (regexp-match? #px"\\bREJECT\\b" text))
  (cond [(and (equal? code 0) a (not r)) "ACCEPT"]
        [(and (equal? code 1) r (not a)) "REJECT"]
        [else "UNKNOWN"]))
(define (run-judge exe args limit logbase)
  ;; grok-fixed: exact integer clock; judge in its own process group so a timeout kills descendants too;
  ;; output readers are bounded so an inherited pipe cannot hold the run past the deadline.
  (define start (current-milliseconds))
  (define-values (sp out in err)
    (parameterize ([subprocess-group-enabled (not (eq? (system-type) 'windows))]) (apply subprocess #f #f #f exe args)))
  (close-output-port in)
  (define ob (open-output-bytes)) (define eb (open-output-bytes))
  (define ot (thread (lambda () (copy-port out ob))))
  (define et (thread (lambda () (copy-port err eb))))
  (define done (sync/timeout limit sp))
  (unless done (subprocess-kill sp #t))
  (subprocess-wait sp)
  (define drained? (and (sync/timeout 5 (thread-dead-evt ot)) (sync/timeout 5 (thread-dead-evt et)) #t))
  (unless drained? (kill-thread ot) (kill-thread et))
  (close-input-port out) (close-input-port err)
  (define code (cond [(not done) 124] [(not drained?) 125] [else (subprocess-status sp)]))
  (define stdout (get-output-bytes ob)) (define stderr (get-output-bytes eb))
  (call-with-output-file (string-append logbase ".stdout.txt") #:exists 'error (lambda (o) (write-bytes stdout o)))
  (call-with-output-file (string-append logbase ".stderr.txt") #:exists 'error (lambda (o) (write-bytes stderr o)))
  (define text (bytes->string/utf-8 (bytes-append stdout stderr) #\?))
  (list (classify text code) code start (current-milliseconds) (clean text)))

(define (verified-post! bundle outdir date inputs limit #:interpreted? [interpreted? #f])
  (define home (simplify-path (path->complete-path bundle)))
  (define target (simplify-path (path->complete-path outdir)))
  (when (or (file-exists? target) (directory-exists? target) (link-exists? target))
    (error 'book-post "output already exists: ~a" target))
  (define pmp (build-path home "pompetzki.exe"))
  (define version
    (or (for/first ([v '("v6" "v5" "v4")]
                    #:when (file-exists? (build-path home "judge" (string-append "judge-" v ".pmp")))) v)
        (error 'book-post "required versioned pmp judge source is missing")))
  (define pj (build-path home "judge" (string-append "judge-" version ".pmp")))
  (define native-pmp (build-path home "judge" (string-append "judge-" version "-windows.exe")))
  (define pmp-exe (if (and (not interpreted?) (file-exists? native-pmp)) native-pmp pmp))
  (define rktexe (build-path home "judge-rkt.exe"))
  (define rktsource (build-path home "judge" (string-append "judge-" version ".rkt")))
  (define racket (or (let ([p (find-executable-path "racket")]) (and p (simplify-path (path->complete-path p)))) (string->path "C:/Program Files/Racket/racket.exe")))
  (for ([p (list pmp pj)]) (unless (file-exists? p) (error 'book-post "required judge file: ~a" p)))
  (unless (or (file-exists? rktexe) (and (file-exists? racket) (file-exists? rktsource)))
    (error 'book-post "Racket cross-check executable or source is required"))
  (define files
    (sort (remove-duplicates
           (append-map (lambda (p)
             (define absolute (simplify-path (path->complete-path p)))
             (cond [(file-exists? absolute) (list absolute)]
                   [(directory-exists? absolute) (for/list ([f (in-directory absolute)] #:when (regexp-match? #rx"[.]jdg$" (path->string f))) f)]
                   [else (error 'book-post "input path does not exist: ~a" absolute)])) inputs))
          string<? #:key path->string))
  (when (null? files) (error 'book-post "no JDG input files"))
  (let-values ([(parent n _) (split-path target)]) (when (path? parent) (make-directory* parent)))
  (make-directory target) ; grok-fixed: atomic create; fails if the target appeared after the check
  (define logs (build-path target "judge-runs")) (make-directory logs)
  (define snapshots (build-path target "judge-inputs")) (make-directory snapshots)
  (define snapshot-files '())
  (define artifact-files
    (append (list pmp-exe pj (build-path home "judge" "registry-auth-v4.rkt"))
            (if (file-exists? rktexe) (list rktexe) (list racket rktsource))))
  (define artifacts
    (for/list ([p artifact-files] #:when (file-exists? p))
      (hasheq 'path (path->string p) 'sha256 (digest p))))
  (define (artifacts-unchanged?)
    (for/and ([a artifacts])
      (and (file-exists? (hash-ref a 'path))
           (equal? (hash-ref a 'sha256) (digest (hash-ref a 'path))))))
  (define runs '())
  (define (run-data exe args result base)
    (hasheq 'command (cons (path->string exe) args) 'verdict (car result) 'exit_code (cadr result)
            'start_epoch_ms (list-ref result 2)
            'end_epoch_ms (list-ref result 3)
            'stdout (string-append base ".stdout.txt") 'stdout_sha256 (digest (string-append base ".stdout.txt"))
            'stderr (string-append base ".stderr.txt") 'stderr_sha256 (digest (string-append base ".stderr.txt"))))
  (define receipt (build-path target "RECEIPTS.tsv"))
  (call-with-output-file receipt #:exists 'error
    (lambda (o)
      (displayln header o)
      (for ([file files] [i (in-naturals 1)])
        (define snapshot (build-path snapshots (format "~a-~a" i (path->string (file-name-from-path file)))))
        (call-with-output-file snapshot #:exists 'error (lambda (out) (write-bytes (file->bytes file) out)))
        (set! snapshot-files (cons snapshot snapshot-files))
        (define before (digest snapshot))
        (define pmp-args (if (equal? pmp-exe native-pmp) (list (path->string snapshot))
                             (list (path->string pj) (path->string snapshot))))
        (define rkt-exe (if (file-exists? rktexe) rktexe racket))
        (define rkt-args (if (file-exists? rktexe) (list (path->string snapshot)) (list (path->string rktsource) (path->string snapshot))))
        (define pmp-base (path->string (build-path logs (format "~a-pmp" i))))
        (define rkt-base (path->string (build-path logs (format "~a-racket" i))))
        (define stable-before? (artifacts-unchanged?))
        (define pr (run-judge pmp-exe pmp-args limit pmp-base))
        (define rr (run-judge rkt-exe rkt-args limit rkt-base))
        (define after (digest snapshot))
        (define unchanged? (and (equal? before after) stable-before? (artifacts-unchanged?)))
        (set! runs (cons (hasheq 'original (path->string file) 'snapshot (path->string snapshot)
                                'input_sha256_before before 'input_sha256_after after 'unchanged unchanged?
                                'pmp (run-data pmp-exe pmp-args pr pmp-base)
                                'racket (run-data rkt-exe rkt-args rr rkt-base)) runs))
        (define (columns r)
          (list (number->string (cadr r)) (number->string (list-ref r 2))
                (number->string (list-ref r 3))
                (number->string (- (list-ref r 3) (list-ref r 2))) (list-ref r 4)))
        (define cols (append (list (path->string snapshot) (if unchanged? (car pr) "CHANGED") (if unchanged? (car rr) "CHANGED")
                                  (path->string logs) before) (columns pr) (columns rr)))
        (displayln (string-join cols "\t") o)
        (flush-output o)
        (printf "~a pmp ~a racket ~a unchanged ~a\n" file (car pr) (car rr) unchanged?))))
  (call-with-output-file (build-path target "run-metadata.json") #:exists 'error
    (lambda (o) (write-json (hasheq 'schema "verified-book-run-v1" 'time_unit "milliseconds since Unix epoch"
                                 'posting_date date 'timeout_seconds limit 'artifacts artifacts 'runs (reverse runs)) o)))
  (post-receipts! (path->string receipt) (path->string target) date (map path->string (reverse snapshot-files))))

(module+ main
  (define bundle #f) (define timeout 300) (define interpreted? #f)
  (define rest
    (command-line #:program "verified-book-post"
      #:once-each
      [("--bundle") path "Installed mathematics bundle" (set! bundle path)]
      [("--interpreted") "Run the pmp source through the interpreter" (set! interpreted? #t)]
      [("--timeout") seconds "Seconds per judge" (define n (string->number seconds)) (unless (and (exact-positive-integer? n) (<= n 3600)) (error 'book-post "timeout must be an integer from 1 to 3600")) (set! timeout n)]
      #:args args args))
  (unless (and bundle (>= (length rest) 3))
    (eprintf "usage: verified-book-post --bundle DIR OUTDIR DATE INPUT ...\n") (exit 2))
  (with-handlers ([exn:fail? (lambda (e) (eprintf "~a\n" (exn-message e)) (exit 3))])
    (exit (verified-post! bundle (car rest) (cadr rest) (cddr rest) timeout #:interpreted? interpreted?))))
