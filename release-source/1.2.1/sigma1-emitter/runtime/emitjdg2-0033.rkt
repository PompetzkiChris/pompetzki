#lang racket/base
;; emitjdg2-0033.rkt (emitjdg-0033.rkt failed: extracted names clash with racket/list; now prefixed x:) - lane L2R, 2026-10-10. Runs the extracted emitter (emit2_0033-mod.rkt, Scheme extraction of
;; CEmitFinal_0033.emit) on a sentence and prints the batch as JDG1 text for pmp judge-v3.pmp and the Racket checker.
;; The registry section is copied from REG.txt (the 677 REGP lines of prelude-0033.jdg); the extracted REGP is
;; printed by the same printer and compared with it.  Not trusted: the judges check the output.
(require racket/list racket/string racket/match racket/file)
(provide (all-defined-out))
;; extracted numbers: nat (O)/(S n); positive (XI p)/(XO p)/(XH); N (N0)/(Npos p)
(define (nat v) (let loop ([v v] [k 0]) (match v [(list 'O) k] [(list 'S w) (loop w (add1 k))])))
(define (pos v) (match v [(list 'XH) 1] [(list 'XO p) (* 2 (pos p))] [(list 'XI p) (add1 (* 2 (pos p)))]))
(define (nN v) (match v [(list 'N0) 0] [(list 'Npos p) (pos p)]))
(define (lst v) (match v [(list 'Nil) '()] [(list 'Cons a r) (cons a (lst r))]))
(define (nl v) (let ([l (map nN (lst v))]) (cons (length l) l)))
(define (df v)
  (match v
    [(list 'DE x y) (list "e" (nN x) (nN y))]
    [(list 'DEq x y) (list "q" (nN x) (nN y))]
    [(list 'DP p a) (list* "p" (nN p) (nl a))]
    [(list 'DN a) (cons "n" (df a))]
    [(list 'DA a) (cons "a" (df a))]
    [(list 'DX a) (cons "x" (df a))]
    [(list 'DI a b) (append (list "i") (df a) (df b))]
    [(list 'DK a b) (append (list "k") (df a) (df b))]
    [(list 'DD a b) (append (list "d") (df a) (df b))]
    [(list 'DQ a b) (append (list "b") (df a) (df b))]))
(define (st v)
  (match v
    [(list 'SUse r s) (list* "U" (nN r) (nl s))]
    [(list 'SSpec l s) (list* "S" (nN l) (nl s))]
    [(list 'SGen a b) (list "G" (nN a) (nN b))]
    [(list 'SMp a b) (list "M" (nN a) (nN b))]
    [(list 'STaut ls g) (append (list "T") (nl ls) (df g))]
    [(list 'SExi a g) (list* "E" (nN a) (df g))]
    [(list 'SInst a g) (list* "V" (nN a) (df g))]
    [(list 'SExel a b g) (list* "L" (nN a) (nN b) (df g))]
    [(list 'SAlli a b g) (list* "H" (nN a) (nN b) (df g))]
    [(list 'SLeib a g) (append (list "Z") (df a) (df g))]
    [(list 'SAx g) (cons "Y" (df g))]))
(define (tokline l) (string-join (map (lambda (x) (if (string? x) x (number->string x))) l) " "))
(define (thm-line v)
  (match v
    [(list 'Thm f sig sts h)
     (let ([ss (lst sts)])
       (tokline (append (df f) (nl sig) (list (length ss)) (append-map st ss) (nl h))))]))
(define (entry-line v) (match v [(list 'Pair d h) (tokline (append (df d) (nl h)))]))
(define (write-jdg out reg-lines ths)
  (call-with-output-file out #:exists 'error
    (lambda (o)
      (fprintf o "JDG1\nR ~a\n" (length reg-lines))
      (for ([l reg-lines]) (displayln l o))
      (fprintf o "T ~a\n" (length ths))
      (for ([t ths]) (displayln (thm-line t) o)))))
