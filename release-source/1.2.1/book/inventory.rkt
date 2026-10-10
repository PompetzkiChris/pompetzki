#lang racket/base
;; inventory.rkt -- book-master (Abschluss 1.0). Lists every Book ledger pair under a hand-in root, once.
;;   racket inventory.rkt HANDIN-ROOT OUT.tsv "DATE"
;; A pair is a folder holding BOOK-1.0.ledger and/or NEGATIVE-1.0.ledger (book-post.rkt's two outputs).
;; One row per folder: pair id (folder relative to HANDIN-ROOT), and for each of the two ledgers its path, sha256,
;; byte count and modification time (local, from the file system), "-" when that ledger is absent.
;; Rows are sorted by the BOOK ledger's modification time, then by pair id (the merge order).
;; Copies: "copy-of" names the earliest pair (in that order) whose two ledger sha256 values are the same.
;; OUT.tsv is created new; an existing name stops the tool. DATE is the text of `date` (clock times come from date).
(require racket/list racket/string racket/file racket/date)

(define (hex bs) (apply string-append (for/list ([b bs]) (string-append (if (< b 16) "0" "") (number->string b 16)))))
(define (sha256-file f) (call-with-input-file f (lambda (in) (hex (sha256-bytes in)))))
(define (two n) (if (< n 10) (format "0~a" n) (number->string n)))
(define (mtime-text p)
  (define d (seconds->date (file-or-directory-modify-seconds p) #t))
  (format "~a-~a-~a ~a:~a:~a" (date-year d) (two (date-month d)) (two (date-day d))
          (two (date-hour d)) (two (date-minute d)) (two (date-second d))))

(module+ main
  (define args (current-command-line-arguments))
  (unless (= (vector-length args) 3) (eprintf "usage: racket inventory.rkt HANDIN-ROOT OUT.tsv DATE\n") (exit 2))
  (define root (path->complete-path (vector-ref args 0)))
  (define out (vector-ref args 1))
  (define date-text (vector-ref args 2))
  (when (file-exists? out) (eprintf "REFUSED: ~a exists; nothing is overwritten\n" out) (exit 1))
  (define dirs (make-hash))
  (for ([p (in-directory root)])
    (define name (let-values ([(d n _) (split-path p)]) (path->string n)))
    (when (and (member name '("BOOK-1.0.ledger" "NEGATIVE-1.0.ledger")) (file-exists? p))
      (define-values (d n _) (split-path p))
      (hash-update! dirs (path->string (simplify-path d)) (lambda (l) (cons name l)) '())))
  (define rootstr (path->string (simplify-path root)))
  (define (rel d) (let ([s (if (string-prefix? d rootstr) (substring d (string-length rootstr)) d)])
                    (string-trim (string-trim s "\\" #:right? #f) "\\" #:left? #f)))
  (define (info d name)
    (define p (build-path d name))
    (if (file-exists? p)
        (list (path->string p) (sha256-file p) (number->string (file-size p)) (mtime-text p)
              (file-or-directory-modify-seconds p))
        (list "-" "-" "-" "-" 0)))
  (define rows
    (for/list ([d (hash-keys dirs)])
      (define b (info d "BOOK-1.0.ledger"))
      (define n (info d "NEGATIVE-1.0.ledger"))
      (list (rel d) b n)))
  (define sorted
    (sort rows (lambda (x y)
                 (define tx (list-ref (cadr x) 4)) (define ty (list-ref (cadr y) 4))
                 (if (= tx ty) (string<? (car x) (car y)) (< tx ty)))))
  (define seen (make-hash))
  (call-with-output-file out #:exists 'error
    (lambda (o)
      (fprintf o "# inventory.rkt, root ~a, taken ~a\n" rootstr date-text)
      (fprintf o "order\tpair\tbook\tbook_sha256\tbook_bytes\tbook_mtime\tneg\tneg_sha256\tneg_bytes\tneg_mtime\tcopy_of\n")
      (for ([r sorted] [i (in-naturals 1)])
        (define b (cadr r)) (define n (caddr r))
        (define key (cons (cadr b) (cadr n)))
        (define copy (hash-ref seen key #f))
        (unless copy (hash-set! seen key (car r)))
        (fprintf o "~a\n" (string-join (append (list (number->string i) (car r)) (take b 4) (take n 4) (list (or copy "-"))) "\t")))))
  (printf "pairs ~a (BOOK ledgers ~a, NEGATIVE ledgers ~a), distinct by sha256 pair ~a\n"
          (length sorted)
          (for/sum ([r sorted]) (if (equal? (car (cadr r)) "-") 0 1))
          (for/sum ([r sorted]) (if (equal? (car (caddr r)) "-") 0 1))
          (hash-count seen))
  (printf "wrote ~a\n" out))
