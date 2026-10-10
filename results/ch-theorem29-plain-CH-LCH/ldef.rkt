#lang racket/base
;; ldef.rkt -- lane LCH round 2: the formula L of lch6.rkt (the statement of LEX in a JDG1 file is X L) written as a Rocq
;; dform literal for LDef.v. Not trusted: LRed.v checks by vm_compute that the replayed statement equals X (tof Ld).
;; Usage: racket ldef.rkt LEX.jdg OUT.v      (OUT.v must be new; LEX is the last theorem of the file)
(require racket/list racket/string racket/match racket/file)
(define (rl l) (string-append "[" (string-join (map number->string l) ";") "]"))
(define (make-reader toks)
  (define p 0)
  (define (nx) (begin0 (vector-ref toks p) (set! p (add1 p))))
  (define (num) (string->number (nx)))
  (define (lst) (for/list ([i (in-range (num))]) (num)))
  (define (dform)
    (define t (nx))
    (case t
      [("e") (let* ([x (num)] [y (num)]) (format "(dE ~a ~a)" x y))]
      [("q") (let* ([x (num)] [y (num)]) (format "(dEq ~a ~a)" x y))]
      [("p") (let* ([pp (num)] [a (lst)]) (format "(dP ~a ~a)" pp (rl a)))]
      [("n") (format "(dN ~a)" (dform))] [("a") (format "(dA ~a)" (dform))] [("x") (format "(dX ~a)" (dform))]
      [("i") (let* ([a (dform)] [b (dform)]) (format "(dI ~a ~a)" a b))]
      [("k") (let* ([a (dform)] [b (dform)]) (format "(dK ~a ~a)" a b))]
      [("d") (let* ([a (dform)] [b (dform)]) (format "(dD ~a ~a)" a b))]
      [("b") (let* ([a (dform)] [b (dform)]) (format "(dQ ~a ~a)" a b))]
      [else (error 'jdg "form tag ~a" t)]))
  (define (skip-step)
    (define t (nx))
    (case t
      [("U" "S") (num) (lst)] [("G" "M") (num) (num)] [("T") (lst) (dform)] [("E" "V") (num) (dform)]
      [("L" "H") (num) (num) (dform)] [("Z") (dform) (dform)] [("Y") (dform)]))
  (values nx num lst dform skip-step))
(define (convert in out)
  (define-values (nx num lst dform skip-step) (make-reader (list->vector (string-split (file->string in)))))
  (nx) (nx)
  (define nr (num)) (for ([i nr]) (dform) (lst))
  (nx)
  (define nt (num))
  (define last-stmt
    (for/last ([i nt]) (let* ([f (dform)] [sig (lst)] [n (num)]) (for ([j n]) (skip-step)) (lst) f)))
  (define m (regexp-match #rx"^\\(dX (.*)\\)$" last-stmt))
  (unless m (error 'ldef "the last statement is not an existential"))
  (call-with-output-file out #:exists 'error
    (lambda (o)
      (fprintf o "(* LDef.v - written by lanes/LCH/ldef.rkt from ~a: the class L of lane LCH (O0), as a dform literal.\n" in)
      (fprintf o "   Ld is the body of the last theorem's statement X L. Readable definition: lanes/LCH/L-DEFINITION.md. *)\n")
      (fprintf o "From Stdlib Require Import List NArith.\nFrom Cohen Require Import Syn Replay2.\nImport ListNotations.\nLocal Open Scope N_scope.\n")
      (fprintf o "Definition Ld : dform := ~a.\n" (cadr m))))
  (printf "~a: Ld written to ~a (~a characters)\n" in out (string-length (cadr m))))
(module+ main
  (match (vector->list (current-command-line-arguments))
    [(list in out) (convert in out)]
    [_ (printf "usage: racket ldef.rkt LEX.jdg OUT.v\n")]))
