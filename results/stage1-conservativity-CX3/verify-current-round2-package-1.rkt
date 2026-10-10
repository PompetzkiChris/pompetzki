#lang racket/base
(require racket/file racket/list racket/string racket/port racket/path racket/system json openssl/sha1)
(define args (current-command-line-arguments))
(unless (= (vector-length args) 3) (error 'usage "integration-json package-directory receipt-sequence"))
(define integration-path (vector-ref args 0))
(define package (vector-ref args 1))
(define seq (vector-ref args 2))
(unless (regexp-match? #px"^[0-9]+$" seq) (error 'sequence "expected an integer"))
(define lane "C:/ClaudeOutput/pompetzki/lanes/CX3")
(define clock
  (string-trim (with-output-to-string
    (lambda () (unless (system* "C:/Program Files/Git/usr/bin/date.exe" "+%Y-%m-%dT%H:%M:%S%:z")
                 (error 'date "date.exe failed"))))))
(define (sha p) (call-with-input-file p (lambda (i) (bytes->hex-string (sha256-bytes i))) #:mode 'binary))
(define integration (call-with-input-file integration-path read-json))
(define manifest-path (build-path package "MANIFEST.sha256"))
(define outer (make-hash))
(when (file-exists? manifest-path)
  (for ([s (in-list (file->lines manifest-path))])
    (define m (regexp-match #px"^([a-fA-F0-9]{64})  (.+)$" s))
    (when m (hash-set! outer (string-replace (string-trim (caddr m)) "\\" "/") (string-downcase (cadr m))))))
(define rows
  (for/list ([r (in-list (hash-ref integration 'files))]
             #:unless (eq? (hash-ref r 'package_relative) 'null))
    (define relative (hash-ref r 'package_relative))
    (define dest (build-path package relative))
    (define actual (and (file-exists? dest) (sha dest)))
    (define expected (hash-ref r 'sha256))
    (hasheq 'relative relative 'source (hash-ref r 'path) 'expected_sha256 expected
            'present (and actual #t) 'actual_sha256 (or actual 'null)
            'source_matches (and actual (equal? actual expected))
            'outer_manifest_matches (equal? expected (hash-ref outer relative #f)))))
(define matching (count (lambda (r) (hash-ref r 'source_matches)) rows))
(define outer-ok (count (lambda (r) (and (hash-ref r 'source_matches) (hash-ref r 'outer_manifest_matches))) rows))
(define artifact
  (hasheq 'clock_date_exe clock 'package package 'integration integration-path
          'integration_sha256 (sha integration-path) 'required_copies (length rows)
          'source_matching_copies matching 'source_and_outer_manifest_matching_copies outer-ok
          'outer_manifest_path (path->string manifest-path)
          'outer_manifest_sha256 (if (file-exists? manifest-path) (sha manifest-path) 'null)
          'all_required_copies_match (= matching (length rows))
          'all_required_copies_in_outer_manifest (= outer-ok (length rows))
          'rows rows))
(define out (build-path lane (string-append "CURRENT-ROUND2-PACKAGE-VERIFY-" seq ".json")))
(call-with-output-file out #:exists 'error (lambda (o) (write-json artifact o) (newline o)))
(define receipt (build-path lane (string-append "CURRENT-ROUND2-PACKAGE-VERIFY-" seq ".sha256")))
(call-with-output-file receipt #:exists 'error
  (lambda (o)
    (fprintf o "# date.exe ~a\n~a  ~a\n~a  ~a\n" clock (sha out) out (sha integration-path) integration-path)))
(printf "~a: ~a/~a copies match source; ~a/~a also match outer manifest. ~a\n"
        clock matching (length rows) outer-ok (length rows) out)
