#lang racket/base

(require racket/list racket/match racket/runtime-path)
(provide cases strx-evaluate canonical-line run-oracle)

(define-runtime-path cases-path "strx-cases.rktd")
(define cases (call-with-input-file cases-path read))

(define (pad s width pad-bytes left?)
  (define need (- width (bytes-length s)))
  (cond
    [(or (<= need 0) (zero? (bytes-length pad-bytes))) s]
    [else
     (define added (make-bytes need))
     (for ([i (in-range need)])
       (bytes-set! added i (bytes-ref pad-bytes (remainder i (bytes-length pad-bytes)))))
     (if left? (bytes-append added s) (bytes-append s added))]))

(define (find-literal s needle start)
  (define last-start (- (bytes-length s) (bytes-length needle)))
  (let loop ([i start])
    (cond
      [(> i last-start) #f]
      [(bytes=? needle (subbytes s i (+ i (bytes-length needle)))) i]
      [else (loop (add1 i))])))

(define (split-literal s separator)
  (cond
    [(zero? (bytes-length separator)) (list s)]
    [else
     (let loop ([start 0] [fields '()])
       (define found (find-literal s separator start))
       (if found
           (loop (+ found (bytes-length separator)) (cons (subbytes s start found) fields))
           (reverse (cons (subbytes s start) fields))))]))

(define (join-literal fields separator)
  (apply bytes-append (add-between fields separator)))

(define (replace-literal s from to)
  (cond
    [(zero? (bytes-length from)) s]
    [else
     (define out (open-output-bytes))
     (let loop ([start 0])
       (define found (find-literal s from start))
       (cond
         [found
          (write-bytes s out start found)
          (write-bytes to out)
          (loop (+ found (bytes-length from)))]
         [else (write-bytes s out start)]))
     (get-output-bytes out)]))

(define (ascii-space? b)
  (or (= b 32) (<= 9 b 13)))

(define (trim-ascii s)
  (define size (bytes-length s))
  (define left
    (let loop ([i 0])
      (if (and (< i size) (ascii-space? (bytes-ref s i))) (loop (add1 i)) i)))
  (define right
    (let loop ([i size])
      (if (and (> i left) (ascii-space? (bytes-ref s (sub1 i)))) (loop (sub1 i)) i)))
  (subbytes s left right))

(define (strx-evaluate op args)
  (match (cons op args)
    [(list 'pad-left s width pad-bytes) (pad s width pad-bytes #t)]
    [(list 'pad-right s width pad-bytes) (pad s width pad-bytes #f)]
    [(list 'split s separator) (split-literal s separator)]
    [(list 'join fields separator) (join-literal fields separator)]
    [(list 'replace s from to) (replace-literal s from to)]
    [(list 'trim s) (trim-ascii s)]
    [_ (error 'strx-evaluate "invalid operation or arguments: ~e" (cons op args))]))

(define hex-digits #"0123456789abcdef")
(define (bytes-hex s)
  (define result (make-bytes (* 2 (bytes-length s))))
  (for ([b (in-bytes s)] [i (in-naturals)])
    (bytes-set! result (* 2 i) (bytes-ref hex-digits (quotient b 16)))
    (bytes-set! result (add1 (* 2 i)) (bytes-ref hex-digits (remainder b 16))))
  result)

(define (canonical-line id op result)
  (define fields (if (eq? op 'split) result (list result)))
  (define out (open-output-bytes))
  (fprintf out "~a|~a|~a|" id op (length fields))
  (for ([field (in-list fields)] [i (in-naturals)])
    (when (> i 0) (write-byte 59 out))
    (fprintf out "~a:" (bytes-length field))
    (write-bytes (bytes-hex field) out))
  (write-byte 10 out)
  (get-output-bytes out))

(define (run-oracle output-path)
  (unless (= (length cases) 50) (error 'strx-oracle "expected exactly 50 cases"))
  (unless (equal? (map car cases) (range 1 51)) (error 'strx-oracle "case IDs must be 1 through 50"))
  (define lines
    (for/list ([case (in-list cases)])
      (match-define (list id op args expected) case)
      (define actual (strx-evaluate op args))
      (unless (equal? actual expected)
        (error 'strx-oracle "REJECT case ~a: expected ~e, computed ~e" id expected actual))
      (canonical-line id op actual)))
  (call-with-output-file output-path
    (lambda (out)
      (for ([line (in-list lines)]) (write-bytes line out))
      (write-bytes #"ACCEPT 50\n" out))
    #:exists 'error)
  (displayln "ACCEPT 50"))

(module+ main
  (define args (current-command-line-arguments))
  (unless (= (vector-length args) 1)
    (error 'strx-oracle "usage: racket strx-oracle.rkt OUTPUT"))
  (run-oracle (vector-ref args 0)))
