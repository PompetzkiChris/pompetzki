#lang racket/base
;; rocq2jdg.rkt -- converts the replay data of Theorem 29 (forcing-src/general/RpInit.v and RpB0.v .. RpB10.v, written by
;; mkreplay.pl in Rocq syntax) into the judge's input format JDG1. Not trusted: the judge checks whatever it is given.
;;
;; JDG1 (tokens separated by white space, numbers in decimal):
;;   JDG1
;;   R n   then n registry entries, each: FORM LIST            (LIST = count then the numbers)
;;   T n   then n theorems, each:   FORM LIST(sig) n STEP.. LIST(hyps)
;;   FORM: e x y (Mem) | q x y (Eqv) | p P LIST (Pr) | n F | i F G | a F | k F G | d F G | b F G (Qf) | x F (Xf)
;;   STEP: U r LIST (use) | S l LIST (spec) | G l k (gen) | M i j (mp) | T LIST FORM (taut) | E t FORM (exi)
;;         L l k FORM (exel) | H k l FORM (alli) | V t FORM (inst) | Z FORM FORM (leib) | Y FORM (ax)
;; usage: racket rocq2jdg.rkt GENERAL-DIR OUT.jdg [LAST-BATCH]
(require racket/string racket/list racket/file racket/port)

(define (strip-comments s)
  (let loop ([i 0] [depth 0] [acc '()])
    (cond [(>= i (string-length s)) (list->string (reverse acc))]
          [(and (< (add1 i) (string-length s)) (char=? (string-ref s i) #\() (char=? (string-ref s (add1 i)) #\*))
           (loop (+ i 2) (add1 depth) acc)]
          [(and (> depth 0) (< (add1 i) (string-length s)) (char=? (string-ref s i) #\*) (char=? (string-ref s (add1 i)) #\)))
           (loop (+ i 2) (sub1 depth) acc)]
          [(> depth 0) (loop (add1 i) depth acc)]
          [else (loop (add1 i) depth (cons (string-ref s i) acc))])))

(define (tokenize s)
  (regexp-match* #px"\\(|\\)|\\[|\\]|;|:=|[A-Za-z_][A-Za-z0-9_']*|[0-9]+|\\.|:" s))

;; the body of "Definition NAME : TYPE := [ ... ]."
(define (definition-body toks name)
  (let loop ([t toks])
    (cond [(null? t) (error 'rocq2jdg "no definition ~a" name)]
          [(and (equal? (car t) "Definition") (pair? (cdr t)) (equal? (cadr t) name))
           (let skip ([u (cddr t)]) (if (equal? (car u) ":=") (cdr u) (skip (cdr u))))]
          [else (loop (cdr t))])))

;; a parser over a token list held in a box
(define toks (box '()))
(define (peek-tok) (car (unbox toks)))
(define (next!) (let ([t (car (unbox toks))]) (set-box! toks (cdr (unbox toks))) t))
(define (expect! s) (let ([t (next!)]) (unless (equal? t s) (error 'rocq2jdg "expected ~a, got ~a" s t))))
(define (num!) (let ([t (next!)]) (or (string->number t) (error 'rocq2jdg "expected a number, got ~a" t))))

(define (parse-list item)
  (expect! "[")
  (if (equal? (peek-tok) "]")
      (begin (next!) '())
      (let loop ([acc (list (item))])
        (let ([t (next!)])
          (cond [(equal? t ";") (loop (cons (item) acc))]
                [(equal? t "]") (reverse acc)]
                [else (error 'rocq2jdg "list: unexpected ~a" t)])))))

(define (parenthesized parse)
  (if (equal? (peek-tok) "(") (begin (next!) (let ([v (parse)]) (expect! ")") v)) (parse)))

(define (parse-form)
  (parenthesized
   (lambda ()
     (define c (next!))
     (case c
       [("dE") (list 'e (num!) (num!))]
       [("dEq") (list 'q (num!) (num!))]
       [("dP") (let ([p (num!)]) (list 'p p (parse-list num!)))]
       [("dN") (list 'n (parse-form))]
       [("dA") (list 'a (parse-form))]
       [("dX") (list 'x (parse-form))]
       [("dI") (let ([a (parse-form)]) (list 'i a (parse-form)))]
       [("dK") (let ([a (parse-form)]) (list 'k a (parse-form)))]
       [("dD") (let ([a (parse-form)]) (list 'd a (parse-form)))]
       [("dQ") (let ([a (parse-form)]) (list 'b a (parse-form)))]
       [else (error 'rocq2jdg "form: unexpected ~a" c)]))))

(define (parse-step)
  (parenthesized
   (lambda ()
     (define c (next!))
     (case c
       [("SUse") (let ([r (num!)]) (list 'U r (parse-list num!)))]
       [("SSpec") (let ([l (num!)]) (list 'S l (parse-list num!)))]
       [("SGen") (let ([l (num!)]) (list 'G l (num!)))]
       [("SMp") (let ([i (num!)]) (list 'M i (num!)))]
       [("STaut") (let ([ls (parse-list num!)]) (list 'T ls (parse-form)))]
       [("SExi") (let ([t (num!)]) (list 'E t (parse-form)))]
       [("SExel") (let* ([l (num!)] [k (num!)]) (list 'L l k (parse-form)))]
       [("SAlli") (let* ([k (num!)] [l (num!)]) (list 'H k l (parse-form)))]
       [("SInst") (let ([t (num!)]) (list 'V t (parse-form)))]
       [("SLeib") (let ([a (parse-form)]) (list 'Z a (parse-form)))]
       [("SAx") (list 'Y (parse-form))]
       [else (error 'rocq2jdg "step: unexpected ~a" c)]))))

(define (parse-thm)
  (parenthesized
   (lambda ()
     (expect! "Thm")
     (let* ([st (parse-form)] [sig (parse-list num!)] [steps (parse-list parse-step)] [hyps (parse-list num!)])
       (list st sig steps hyps)))))

(define (parse-def-list toks0 name item)
  (set-box! toks (definition-body toks0 name))
  (parse-list item))

;; ---- output
(define out (open-output-string))
(define (w . xs) (for ([x xs]) (write-string (if (number? x) (number->string x) (if (symbol? x) (symbol->string x) x)) out) (write-string " " out)))
(define (wlist l) (w (length l)) (for ([x l]) (w x)))
(define (wform f)
  (case (car f)
    [(e q) (w (car f) (cadr f) (caddr f))]
    [(p) (w 'p (cadr f)) (wlist (caddr f))]
    [(n a x) (w (car f)) (wform (cadr f))]
    [(i k d b) (w (car f)) (wform (cadr f)) (wform (caddr f))]))
(define (wstep s)
  (case (car s)
    [(U S) (w (car s) (cadr s)) (wlist (caddr s))]
    [(G M) (w (car s) (cadr s) (caddr s))]
    [(T) (w 'T) (wlist (cadr s)) (wform (caddr s))]
    [(E V) (w (car s) (cadr s)) (wform (caddr s))]
    [(L H) (w (car s) (cadr s) (caddr s)) (wform (cadddr s))]
    [(Z) (w 'Z) (wform (cadr s)) (wform (caddr s))]
    [(Y) (w 'Y) (wform (cadr s))]))

(module+ main
  (define args (current-command-line-arguments))
  (define dir (vector-ref args 0))
  (define outp (vector-ref args 1))
  (define last-batch (if (> (vector-length args) 2) (string->number (vector-ref args 2)) 10))
  (define (load-toks f) (tokenize (strip-comments (file->string (build-path dir f)))))
  (define init (load-toks "RpInit.v"))
  (define ax0 (parse-def-list init "AX0" parse-form))
  (define def0 (parse-def-list init "DEF0" parse-form))
  (define hypd (parse-def-list init "HYPD" parse-form))
  (define reg (append (map (lambda (d) (list d '())) ax0)
                      (map (lambda (d) (list d '())) def0)
                      (for/list ([d hypd] [i (in-naturals)]) (list d (list i)))))
  (define thms
    (append* (for/list ([b (in-range 0 (add1 last-batch))])
               (parse-def-list (load-toks (format "RpB~a.v" b)) (format "B~a" b) parse-thm))))
  (write-string "JDG1\n" out)
  (w 'R (length reg)) (write-string "\n" out)
  (for ([e reg]) (wform (car e)) (wlist (cadr e)) (write-string "\n" out))
  (w 'T (length thms)) (write-string "\n" out)
  (for ([t thms])
    (wform (car t)) (wlist (cadr t)) (w (length (caddr t)))
    (for ([s (caddr t)]) (wstep s))
    (wlist (cadddr t)) (write-string "\n" out))
  (call-with-output-file outp #:exists 'error (lambda (o) (write-string (get-output-string out) o)))
  (printf "registry ~a (axioms ~a, definitions ~a, hypotheses ~a), theorems ~a, steps ~a\n"
          (length reg) (length ax0) (length def0) (length hypd) (length thms)
          (for/sum ([t thms]) (length (caddr t)))))
