#lang racket/base
;; chainverify.rkt -- book-master (Abschluss 1.0). Verifies the hash chain of every ledger in inventory.tsv.
;;   racket chainverify.rkt inventory.tsv OUT.tsv
;; Per ledger: the sha256 of the file now must equal the inventory's (the file did not change since it was listed),
;; then Q122's verify-ledger (queue\Q122\ledger-verify.rkt, required unchanged from its folder) checks the chain, the
;; record grammar, the F/B ranges, the step totals and the E counts. One row per ledger: PASS with its counts and
;; chain head, or FAIL with verify-ledger's message. OUT.tsv is created new. Reads only.
(require racket/list racket/string racket/file
         (file "C:/ClaudeOutput/pompetzki/release-1.0/handin/queue/Q122/ledger-verify.rkt"))

(define (hex bs) (apply string-append (for/list ([b bs]) (string-append (if (< b 16) "0" "") (number->string b 16)))))
(define (sha256-file f) (call-with-input-file f (lambda (in) (hex (sha256-bytes in)))))
(define (clean s) (regexp-replace* #rx"[\t\r\n]" s " "))

(module+ main
  (define args (current-command-line-arguments))
  (unless (= (vector-length args) 2) (eprintf "usage: racket chainverify.rkt inventory.tsv OUT.tsv\n") (exit 2))
  (define out (vector-ref args 1))
  (when (file-exists? out) (eprintf "REFUSED: ~a exists\n" out) (exit 1))
  (define rows (for/list ([ln (file->lines (vector-ref args 0))] #:unless (regexp-match? #rx"^(#|order\t)" ln))
                 (string-split ln "\t" #:trim? #f)))
  (define npass 0) (define nfail 0)
  (call-with-output-file out #:exists 'error
    (lambda (o)
      (fprintf o "order\tpair\tkind\tpath\tsha256\tresult\trecords\tF\tB\tN\thead\tmessage\n")
      (for ([r rows])
        (define order (list-ref r 0)) (define pair (list-ref r 1))
        (for ([kind '("BOOK" "NEGATIVE")] [pi '(2 6)])
          (define path (list-ref r pi))
          (define want (list-ref r (add1 pi)))
          (unless (equal? path "-")
            (define now (sha256-file path))
            (define t0 (current-milliseconds))
            (define line
              (cond
                [(not (equal? now want))
                 (list "FAIL" "-" "-" "-" "-" "-" (format "sha256 now ~a, inventory ~a" now want))]
                [else
                 (with-handlers ([exn:fail? (lambda (e) (list "FAIL" "-" "-" "-" "-" "-" (clean (exn-message e))))])
                   (define res (verify-ledger path))
                   (list "PASS" (number->string (ledger-result-records res)) (number->string (ledger-result-files res))
                         (number->string (ledger-result-postings res)) (number->string (ledger-result-negatives res))
                         (ledger-result-head res)
                         (format "segment ~a, ~a ms" (ledger-result-segment res) (- (current-milliseconds) t0))))]))
            (if (equal? (car line) "PASS") (set! npass (add1 npass)) (set! nfail (add1 nfail)))
            (fprintf o "~a\n" (string-join (append (list order pair kind path now) line) "\t"))
            (flush-output o)
            (printf "~a ~a ~a ~a\n" order kind (car line) pair))))))
  (printf "ledgers PASS ~a FAIL ~a\n" npass nfail))
