#lang racket
;; agree.rkt - lane L2R, 2026-10-09. The sentence theorems of sigma1's files 04-bounded, 06-sentences, 07-sigma1 (keys
;; (Sent s) in the .index.txt listings), read from the judged .jdg files with sigma1.rkt's own reader, written as Rocq data
;; to L2RCases.v: the sentence in the de Bruijn syntax of L2RSent.v, its truth value by sigma1's evaluator, and the
;; statement of the theorem (tof of its dform). L2RAgree.v checks that tr gives exactly these statements.
;;   racket agree.rkt OUT.v
(require racket/match racket/string racket/list racket/file)

(define SIGMA1 (string->path "C:/ClaudeOutput/pompetzki/sigma1/sigma1.rkt"))
(define OUTDIR "C:/ClaudeOutput/pompetzki/sigma1/out/")
(define FILES '("04-bounded" "06-sentences" "07-sigma1"))

(define-namespace-anchor anchor)
(define ns0 (namespace-anchor->namespace anchor))
(parameterize ([current-namespace ns0]) (dynamic-require SIGMA1 #f))
(define ns (parameterize ([current-namespace ns0]) (module->namespace SIGMA1)))
(define (sig name) (eval name ns))
(define read-jdg-text (sig 'read-jdg-text))
(define tof (sig 'tof))
(define normalize (sig 'normalize))
(define ev (sig 'ev))

(define (tm->rocq t env)
  (match t
    [(? exact-nonnegative-integer? n) (format "(tnum ~a)" n)]
    [(? symbol? x) (format "(tvar ~a)" (or (index-of env x) (error 'tm "unbound ~a" x)))]
    [(list 'S a) (format "(tS ~a)" (tm->rocq a env))]
    [(list '+ a b) (format "(tadd ~a ~a)" (tm->rocq a env) (tm->rocq b env))]
    [(list '* a b) (format "(tmul ~a ~a)" (tm->rocq a env) (tm->rocq b env))]))

(define (fm->rocq F env)
  (define (two ctor A B) (format "(~a ~a ~a)" ctor (fm->rocq A env) (fm->rocq B env)))
  (define (rel ctor a b) (format "(~a ~a ~a)" ctor (tm->rocq a env) (tm->rocq b env)))
  (define (q ctor x t A) (format "(~a ~a ~a)" ctor (tm->rocq t env) (fm->rocq A (cons x env))))
  (match F
    [(list '= a b) (rel "feq" a b)]
    [(list '< a b) (rel "flt" a b)]
    [(list '<= a b) (rel "fle" a b)]
    [(list 'not A) (format "(fnot ~a)" (fm->rocq A env))]
    [(list 'and A B) (two "fand" A B)]
    [(list 'or A B) (two "fdis" A B)]
    [(list 'imp A B) (two "fimp" A B)]
    [(list 'iff A B) (two "fiff" A B)]
    [(list 'all x t A) (q "fall" x t A)]
    [(list 'ex x t A) (q "fex" x t A)]
    [(list 'alle x t A) (q "falle" x t A)]
    [(list 'exe x t A) (q "fexe" x t A)]
    [(list 'some x A) (format "(fsome ~a)" (fm->rocq A (cons x env)))]))

(define (form->rocq f)
  (match f
    [(list 'E x y) (format "(Mem ~a ~a)" x y)]
    [(list 'Q x y) (format "(Eqv ~a ~a)" x y)]
    [(list 'P p args) (format "(Pr ~a [~a])" p (string-join (map number->string args) "; "))]
    [(list 'N a) (format "(Neg ~a)" (form->rocq a))]
    [(list 'I a b) (format "(Imp ~a ~a)" (form->rocq a) (form->rocq b))]
    [(list 'A a) (format "(All ~a)" (form->rocq a))]))

(define (cases-of base)
  (define lines (file->lines (string-append OUTDIR base ".index.txt")))
  (define-values (rg ths) (read-jdg-text (file->string (string-append OUTDIR base ".jdg"))))
  (define tv (list->vector ths))
  (for/list ([line lines]
             #:when (let* ([in (open-input-string line)] [i (read in)] [k (read in)]) (and (pair? k) (eq? (car k) 'Sent))))
    (define in (open-input-string line))
    (define i (read in))
    (define key (read in))
    (define s (normalize (cadr key)))
    (match-define (list st sg steps hyps) (vector-ref tv i))
    (unless (and (null? sg) (null? hyps)) (error 'cases "theorem ~a of ~a is not closed" i base))
    (list base i (cadr key) (fm->rocq s '()) (if (ev s '()) "true" "false") (form->rocq (tof st)))))

(define (main out)
  (define all (append-map cases-of FILES))
  (define o (open-output-file out #:exists 'error))
  (fprintf o "(* L2RCases.v - written by agree.rkt (lane L2R) from sigma1/out/{04-bounded,06-sentences,07-sigma1}.jdg and\n")
  (fprintf o "   their .index.txt: every theorem with key (Sent s); the sentence s (normalized by sigma1.rkt), its truth value by\n")
  (fprintf o "   sigma1.rkt's evaluator, and the theorem's statement (tof of its dform). ~a cases. *)\n" (length all))
  (fprintf o "From Stdlib Require Import List String.\nFrom Cohen Require Import Syn.\nFrom L2R Require Import L2RSent.\n")
  (fprintf o "Import ListNotations.\nOpen Scope string_scope.\n\n")
  (fprintf o "Definition cases : list (string * fm * bool * form) := [\n")
  (fprintf o "~a]%list.\n"
           (string-join
            (for/list ([c all])
              (match-define (list base i s fr tv f) c)
              (format "  (\"~a ~a ~a\",\n   ~a,\n   ~a,\n   ~a)" base i (string-replace (format "~s" s) "\"" "") fr tv f))
            ";\n"))
  (close-output-port o)
  (printf "~a cases written to ~a\n" (length all) out)
  (for ([b FILES]) (printf "  ~a: ~a\n" b (count (lambda (c) (equal? (car c) b)) all))))

(match (vector->list (current-command-line-arguments))
  [(list out) (main out)]
  [_ (printf "usage: racket agree.rkt OUT.v\n")])
