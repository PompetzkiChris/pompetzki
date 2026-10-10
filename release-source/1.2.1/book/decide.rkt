#lang racket/base
;; decide.rkt -- book-master (Abschluss 1.0). Decides, per ledger, MERGE or HOLD (SPEC.md section 2).
;;   racket decide.rkt inventory.tsv chainverify.tsv OUT.tsv SPOTCHECK.tsv ...
;; A ledger is MERGE when its chain check PASSed (chainverify.tsv, which also compared its sha256 with the inventory)
;; and, if it holds records, its spot-check has at least 2 PASS picks and no FAIL pick (over all SPOTCHECK files
;; given). EMPTY: chain PASS, no F/B (BOOK) or no N (NEGATIVE) record, nothing to merge. HOLD otherwise, with the reason.
;; The shipped Book (pair SHIPPED) is decided the same way from its B and N picks (its chain: bookverify.rkt, RUN-02).
;; OUT.tsv: order, pair, kind, ledger, sha256, records, chain, spot, decision, reason. Created new.
(require racket/list racket/string racket/file)

(define (split-tab s) (string-split s "\t" #:trim? #f))
(define (rows f) (for/list ([ln (file->lines f)] #:unless (regexp-match? #rx"^#" ln)) (split-tab ln)))

(module+ main
  (define args (vector->list (current-command-line-arguments)))
  (unless (>= (length args) 4) (eprintf "usage: racket decide.rkt inventory.tsv chainverify.tsv OUT.tsv SPOTCHECK.tsv ...\n") (exit 2))
  (define out (list-ref args 2))
  (when (file-exists? out) (eprintf "REFUSED: ~a exists\n" out) (exit 1))
  (define inv (cdr (rows (list-ref args 0))))
  (define cv (make-hash)) ; ledger path -> row
  (for ([r (cdr (rows (list-ref args 1)))]) (hash-set! cv (list-ref r 3) r))
  ;; spot picks: (pair . kind) -> list of (pick result record reason)
  (define spot (make-hash))
  (for* ([f (list-tail args 3)] [r (cdr (rows f))])
    (hash-update! spot (cons (list-ref r 0) (list-ref r 1))
                  (lambda (l) (cons (list (list-ref r 3) (list-ref r 7) (list-ref r 4) (list-ref r 10)) l)) '()))
  (define (spot-verdict pair kind nrec)
    (define picks (hash-ref spot (cons pair kind) '()))
    (define real (filter (lambda (p) (not (equal? (car p) "0"))) picks))
    (define pass (filter (lambda (p) (equal? (cadr p) "PASS")) real))
    (define fail (filter (lambda (p) (equal? (cadr p) "FAIL")) real))
    (cond
      [(= nrec 0) (values "none" "EMPTY" "no record to merge")]
      [(pair? fail) (values (format "FAIL ~a" (string-join (map caddr fail) ","))
                            "HOLD" (format "spot-check FAIL: ~a" (string-join (map cadddr fail) " | ")))]
      [(>= (length pass) 2) (values (format "PASS ~a" (string-join (map caddr (reverse pass)) ",")) "MERGE" "-")]
      [(null? picks) (values "not run" "HOLD" "no spot-check result")]
      [else (values (format "PASS ~a of 2" (length pass)) "HOLD"
                    (let ([none (filter (lambda (p) (equal? (car p) "0")) picks)])
                      (if (pair? none) (string-append "spot-check not possible: " (cadddr (car none))) "fewer than 2 picks PASS")))]))
  (define o (open-output-file out #:exists 'error))
  (fprintf o "order\tpair\tkind\tledger\tsha256\trecords\tchain\tspot\tdecision\treason\n")
  (define tally (make-hash))
  (define (emit order pair kind ledger sha nrec chain)
    (define-values (sv dec why)
      (if (equal? chain "PASS") (spot-verdict pair (if (equal? kind "BOOK") "B" "N") nrec) (values "-" "HOLD" "chain check FAIL")))
    (hash-update! tally dec add1 0)
    (fprintf o "~a\n" (string-join (list order pair kind ledger sha (number->string nrec) chain sv dec why) "\t")))
  ;; shipped Book: B and N decided separately, as two "ledgers" of one source
  (emit "0" "SHIPPED" "BOOK" "C:\\ClaudeOutput\\pompetzki\\release-1.0\\handin\\queue\\Q23-book\\book" "-" 9843 "PASS")
  (emit "0" "SHIPPED" "NEGATIVE" "C:\\ClaudeOutput\\pompetzki\\release-1.0\\handin\\queue\\Q23-book\\book" "-" 347 "PASS")
  (for ([r inv])
    (define order (list-ref r 0)) (define pair (list-ref r 1))
    (for ([kind '("BOOK" "NEGATIVE")] [pi '(2 6)])
      (define path (list-ref r pi))
      (unless (equal? path "-")
        (define c (hash-ref cv path #f))
        (define chain (if c (list-ref c 5) "MISSING"))
        (define nrec (if (and c (equal? chain "PASS"))
                         (if (equal? kind "BOOK") (string->number (list-ref c 8)) (string->number (list-ref c 9)))
                         0))
        (emit order pair kind path (list-ref r (add1 pi)) nrec chain))))
  (close-output-port o)
  (printf "MERGE ~a HOLD ~a EMPTY ~a\n" (hash-ref tally "MERGE" 0) (hash-ref tally "HOLD" 0) (hash-ref tally "EMPTY" 0))
  (printf "wrote ~a\n" out))
