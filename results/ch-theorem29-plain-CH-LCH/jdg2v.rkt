#lang racket/base
;; jdg2v.rkt -- lane LCH: a JDG1 file to Rocq data for Replay2.v (the theorems after the registry, as list thm).
;; Not trusted: the Rocq side checks the data with check_batch (Replay2.v) by vm_compute and Replay3.check_batch_ok.
;; Usage: racket jdg2v.rkt IN.jdg OUT.v NAME      writes Definition NAME : list thm := [...] (OUT.v must be new)
(require racket/list racket/string racket/match racket/file)

(define (make-reader toks)
  (define p 0)
  (define (nx) (begin0 (vector-ref toks p) (set! p (add1 p))))
  (define (num) (let ([t (nx)]) (or (string->number t) (error 'jdg "number expected, got ~a" t))))
  (define (lst) (for/list ([i (in-range (num))]) (num)))
  (define (dform)
    (define t (nx))
    (case t
      [("e") (let* ([x (num)] [y (num)]) (format "(dE ~a ~a)" x y))]
      [("q") (let* ([x (num)] [y (num)]) (format "(dEq ~a ~a)" x y))]
      [("p") (let* ([pp (num)] [a (lst)]) (format "(dP ~a ~a)" pp (rl a)))]
      [("n") (format "(dN ~a)" (dform))]
      [("a") (format "(dA ~a)" (dform))]
      [("x") (format "(dX ~a)" (dform))]
      [("i") (let* ([a (dform)] [b (dform)]) (format "(dI ~a ~a)" a b))]
      [("k") (let* ([a (dform)] [b (dform)]) (format "(dK ~a ~a)" a b))]
      [("d") (let* ([a (dform)] [b (dform)]) (format "(dD ~a ~a)" a b))]
      [("b") (let* ([a (dform)] [b (dform)]) (format "(dQ ~a ~a)" a b))]
      [else (error 'jdg "form tag expected, got ~a" t)]))
  (define (step)
    (define t (nx))
    (case t
      [("U") (let* ([r (num)] [s (lst)]) (format "SUse ~a ~a" r (rl s)))]
      [("S") (let* ([l (num)] [s (lst)]) (format "SSpec ~a ~a" l (rl s)))]
      [("G") (let* ([a (num)] [b (num)]) (format "SGen ~a ~a" a b))]
      [("M") (let* ([a (num)] [b (num)]) (format "SMp ~a ~a" a b))]
      [("T") (let* ([ls (lst)] [g (dform)]) (format "STaut ~a ~a" (rl ls) g))]
      [("E") (let* ([a (num)] [g (dform)]) (format "SExi ~a ~a" a g))]
      [("V") (let* ([a (num)] [g (dform)]) (format "SInst ~a ~a" a g))]
      [("L") (let* ([a (num)] [b (num)] [g (dform)]) (format "SExel ~a ~a ~a" a b g))]
      [("H") (let* ([a (num)] [b (num)] [g (dform)]) (format "SAlli ~a ~a ~a" a b g))]
      [("Z") (let* ([a (dform)] [g (dform)]) (format "SLeib ~a ~a" a g))]
      [("Y") (format "SAx ~a" (dform))]
      [else (error 'jdg "step tag expected, got ~a" t)]))
  (values nx num lst dform step))

(define (rl l) (string-append "[" (string-join (map number->string l) ";") "]"))

(define (convert in out name)
  (define-values (nx num lst dform step) (make-reader (list->vector (string-split (file->string in)))))
  (unless (equal? (nx) "JDG1") (error 'jdg "header"))
  (unless (equal? (nx) "R") (error 'jdg "R"))
  (define nr (num))
  (for ([i (in-range nr)]) (dform) (lst))
  (unless (equal? (nx) "T") (error 'jdg "T"))
  (define nt (num))
  (define ths
    (for/list ([i (in-range nt)])
      (let* ([f (dform)] [sig (lst)] [n (num)] [sts (for/list ([j n]) (step))] [h (lst)])
        (format "(* ~a *) Thm ~a ~a [~a] ~a" i f (rl sig) (string-join sts ";\n  ") (rl h)))))
  (call-with-output-file out #:exists 'error
    (lambda (o)
      (fprintf o "(* ~a - written by lanes/LCH/jdg2v.rkt from ~a: the ~a theorems after its registry of ~a entries. *)\n"
               (let-values ([(b f d) (split-path out)]) (path->string f)) in nt nr)
      (fprintf o "From Stdlib Require Import List NArith.\nFrom Cohen Require Import Syn Replay2.\nImport ListNotations.\nLocal Open Scope N_scope.\n")
      (fprintf o "Definition ~a : list thm := [\n~a].\n" name (string-join ths ";\n"))))
  (printf "~a: ~a theorems, registry ~a, written ~a\n" in nt nr out))

(module+ main
  (match (vector->list (current-command-line-arguments))
    [(list in out name) (convert in out name)]
    [_ (printf "usage: racket jdg2v.rkt IN.jdg OUT.v NAME\n")]))
