#lang racket
;; Command-line interface for the exact matrix engine.
;;
;;   racket engine.rkt --op det --a matrix.txt
;;   racket engine.rkt --op solve --a A.txt --b b.txt
;;   racket engine.rkt --op mul --a A.txt --b B.txt --out result.txt
;;   racket engine.rkt --batch jobs.json
;;   racket engine.rkt --self-check
;;
;; --out refuses a path that already exists.
;; A job file is a JSON array of objects with id, op, a, and optional b.
;; The human answer is printed first. A line ---MACHINE--- follows, then one JSON object.
;; Batch mode prints one JSON array and no human text. Each item has its own exit
;; status; a malformed item does not suppress the other results. A valid batch
;; envelope exits 0 after processing every item, even if individual items fail.
;; Exit 0 means the operation returned a mathematical result, including an inconsistent
;; system or a square matrix with no inverse. Exit 1 means the input was rejected or
;; the output path was refused. Exit 2 means the command line was not understood.

(require json "exact.rkt")

(provide main-argv)

(define usage
  (string-join
   '("usage:"
     "  racket engine.rkt --op OP --a FILE [--b FILE] [--out FILE]"
     "  racket engine.rkt --batch JOBS.json [--out FILE]"
     "  racket engine.rkt --self-check"
     "operations: rref, rank, kernel, image, solve, det, inv, transpose, add, mul"
     "matrix file: rows: R / cols: C followed by entries, or [a, b; c, d], or empty R C, or zero R C"
     "entries are integers or fractions such as -3/4. Decimal points are rejected.")
   "\n"))

(define (read-text path)
  (unless (file-exists? path)
    (error 'engine "Cannot read ~a because that file is not there." path))
  (file->string path))

(define (flag-map argv)
  (define known '("--op" "--a" "--b" "--out" "--batch"))
  (let loop ([xs argv] [h (hash)])
    (cond
      [(null? xs) h]
      [(and (regexp-match? #rx"^--" (car xs)) (pair? (cdr xs)))
       (unless (member (car xs) known) (error 'engine "Unknown command flag: ~a" (car xs)))
       (when (hash-has-key? h (car xs)) (error 'engine "Repeated command flag: ~a" (car xs)))
       (loop (cddr xs) (hash-set h (car xs) (cadr xs)))]
      [else (error 'engine "The command line was not understood near ~a.\n~a" (car xs) usage)])))

(define (emit oc)
  (displayln (outcome-text oc))
  (displayln "---MACHINE---")
  (write-json (outcome-machine oc))
  (newline))

(define (write-out path text)
  (with-handlers ([exn:fail? (lambda (e) (eprintf "~a\n" (exn-message e)) (exit 1))])
    (write-new-file path text)))

(define (run-op op a-path b-path out-path)
  (define a-text (read-text a-path))
  (define b-text (if b-path (read-text b-path) ""))
  (define oc (perform op a-text b-text))
  (define rendered
    (with-output-to-string (lambda () (emit oc))))
  (when out-path (write-out out-path rendered))
  (display rendered)
  (exit (outcome-exit-code oc)))

(define (job->result job)
  (define id (if (hash? job) (hash-ref job 'id 'null) 'null))
  (define op (and (hash? job) (hash-ref job 'op #f)))
  (with-handlers ([exn:fail?
                   (lambda (e)
                     (define reason (exn-message e))
                     (hash 'id id 'exit 1
                           'text (string-append "Rejected. " reason)
                           'machine (hash 'status "rejected"
                                          'op (if (string? op) op 'null)
                                          'reason reason)))])
    (unless (hash? job) (error 'batch "Each batch item must be a JSON object."))
    (unless (string? op) (error 'batch "Each batch item requires a text op field."))
    (define a (hash-ref job 'a #f))
    (unless (string? a) (error 'batch "Each batch item requires a text a field."))
    (define b (hash-ref job 'b ""))
    (unless (string? b) (error 'batch "The optional b field must contain matrix text."))
    (define oc (perform op a b))
    (hash 'id id
          'exit (outcome-exit-code oc)
          'text (outcome-text oc)
          'machine (outcome-machine oc))))

(define (run-batch path out-path)
  (define jobs
    (call-with-input-file path
      (lambda (in)
        (define value (read-json in))
        (unless (eof-object? (read-json in))
          (error 'engine "The batch file must contain exactly one JSON array."))
        value)))
  (unless (list? jobs)
    (error 'engine "The batch file must be a JSON array."))
  (define results (map job->result jobs))
  (define rendered (with-output-to-string (lambda () (write-json results) (newline))))
  (when out-path (write-out out-path rendered))
  (display rendered)
  (exit 0))

(define (main-argv argv)
  (with-handlers ([exn:fail? (lambda (e) (eprintf "~a\n" (exn-message e)) (exit 1))])
    (cond
      [(null? argv)
       (display usage)
       (exit 2)]
      [(equal? (car argv) "--self-check")
       (unless (= (length argv) 1) (eprintf "--self-check takes no other arguments\n") (exit 2))
       (if (self-check)
           (begin (displayln "SELF-CHECK passed") (exit 0))
           (begin (displayln "SELF-CHECK failed") (exit 1)))]
      [else
       (define flags (with-handlers ([exn:fail? (lambda (e) (eprintf "~a\n" (exn-message e)) (exit 2))]) (flag-map argv)))
       (when (and (hash-has-key? flags "--batch") (ormap (lambda (key) (hash-has-key? flags key)) '("--op" "--a" "--b")))
         (eprintf "--batch cannot be combined with --op, --a, or --b\n") (exit 2))
       (define out-path (hash-ref flags "--out" #f))
       (cond
         [(hash-ref flags "--batch" #f)
          => (lambda (p) (run-batch p out-path))]
         [(hash-ref flags "--op" #f)
          => (lambda (op)
               (define a (hash-ref flags "--a" #f))
               (unless a
                 (eprintf "An --a matrix file is required.\n~a" usage)
                 (exit 2))
               (run-op op a (hash-ref flags "--b" #f) out-path))]
         [else
          (display usage)
          (exit 2)])])))

(module+ main
  (main-argv (vector->list (current-command-line-arguments))))
