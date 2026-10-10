#lang racket
;; Hypothetical set-only predicates. This program does not alter a judge registry.
(require racket/list racket/match racket/string "registry-reader-v3.rkt")
(provide (struct-out prototype) prototypes extended-symbol-names extended-symbol-arities
         parse-extended closed-extended? extended->named extended->debruijn
         prototype-validation)
(struct prototype (name arity symbol-id source-label scope parameters body closed-formula) #:transparent)
(define specs
  '(("Rel1" ("f") "df-rel" "F is a represented set; every graph member is a Kuratowski ordered pair."
            "A p I E p f X x X y Opr3 p x y")
    ("Fun1" ("f") "df-fun" "F is a represented set; graphhood and single-valuedness are both retained."
            "K Rel1 f Fnc1 f")
    ("Fn2" ("f" "a") "df-fn" "F and A are represented sets; graphhood and exact domain A are retained."
           "K K Fnc1 f Tot2 f a Dm2 f a")
    ("Map3" ("f" "a" "b") "df-f" "F, A, B are represented sets; exact domain A and range inclusion in B."
            "K Fn2 f a Rng2 f b")
    ("Inject3" ("f" "a" "b") "df-f1" "F, A, B are represented sets; injective mapping with exact domain A."
               "K Map3 f a b Inj1 f")
    ("Onto3" ("f" "a" "b") "df-fo" "F, A, B are represented sets; exact domain A and exact range B."
             "K Map3 f a b Cov3 b f a")
    ("Bijection3" ("f" "a" "b") "df-f1o" "F, A, B are represented sets; injective mapping with exact domain A and exact range B."
                  "K Inject3 f a b Cov3 b f a")
    ("RelPres5" ("h" "r" "s" "a" "b") "df-relp" "H, R, S, A, B are represented sets; arbitrary represented set relations R and S."
                "K Map3 h a b A x A y A u A v I K K K E x a E y a App3 h x u App3 h y v I App3 r x y App3 s u v")
    ("Isom5" ("h" "r" "s" "a" "b") "df-isom" "H, R, S, A, B are represented sets; arbitrary represented set relations R and S."
             "K Bijection3 h a b A x A y A u A v I K K K E x a E y a App3 h x u App3 h y v Q App3 r x y App3 s u v")
    ("DomExact2" ("r" "a") "df-fn;df-er" "R and A are represented sets; exact domain of the ordered-pair part, with graphhood supplied by callers."
                 "A x Q X y App3 r x y E x a")
    ("Er2" ("r" "a") "df-er" "R and A are represented sets; graphhood, exact domain, symmetry, and transitivity."
           "K K K Rel1 r DomExact2 r a A x A y I App3 r y x App3 r x y A x A y A z I K App3 r x y App3 r y z App3 r x z")))
(define first-new-id (vector-length symbol-names))
(unless (= first-new-id 686) (error 'prototype "expected source symbol count 686, received ~a" first-new-id))
(define extended-symbol-names (vector-append symbol-names (list->vector (map first specs))))
(define ids (for/hash ([name (in-vector extended-symbol-names)] [id (in-naturals)]) (values name id)))
(unless (= (hash-count ids) (vector-length extended-symbol-names)) (error 'prototype "symbol collision"))
(define extended-symbol-arities
  (for/fold ([result symbol-arity]) ([spec (in-list specs)])
    (hash-set result (first spec) (length (second spec)))))
(define (parse-extended text [parameters '()])
  (define tokens (list->vector (string-split text)))
  (define cursor 0)
  (define (take)
    (when (>= cursor (vector-length tokens)) (error 'parse-extended "unexpected end in ~a" text))
    (begin0 (vector-ref tokens cursor) (set! cursor (add1 cursor))))
  (define (term env)
    (define v (take)) (define b (index-of env v)) (define p (index-of parameters v))
    (cond [b b] [p (+ (length env) p)] [else (error 'parse-extended "unbound variable ~a in ~a" v text)]))
  (define (form env)
    (define head (take))
    (match head
      ["N" (list 'N (form env))]
      [(or "A" "X") (define v (take)) (list (string->symbol head) (form (cons v env)))]
      [(or "I" "K" "D" "Q") (list (string->symbol head) (form env) (form env))]
      [(or "E" "=") (list (string->symbol head) (term env) (term env))]
      [p (unless (hash-has-key? ids p) (error 'parse-extended "unknown predicate ~a" p))
         (list 'P (hash-ref ids p)
               (for/list ([i (in-range (hash-ref extended-symbol-arities p))]) (term env)))]))
  (define f (form '()))
  (unless (= cursor (vector-length tokens)) (error 'parse-extended "extra tokens in ~a" text)) f)
(define (closed-extended? f [depth 0])
  (define (ok x) (and (exact-nonnegative-integer? x) (< x depth)))
  (match f
    [(list (or 'E '=) x y) (and (ok x) (ok y))]
    [(list 'P p args) (and (exact-nonnegative-integer? p) (< p (vector-length extended-symbol-names))
                           (= (length args) (hash-ref extended-symbol-arities (vector-ref extended-symbol-names p)))
                           (andmap ok args))]
    [(list 'N a) (closed-extended? a depth)]
    [(list (or 'A 'X) a) (closed-extended? a (add1 depth))]
    [(list (or 'I 'K 'D 'Q) a b) (and (closed-extended? a depth) (closed-extended? b depth))]
    [_ #f]))
(define (extended->named f [depth 0])
  (define (term x) (if (< x depth) (format "v~a" (- depth x 1)) (format "f~a" (- x depth))))
  (match f
    [(list (or 'E '=) x y) (format "~a ~a ~a" (first f) (term x) (term y))]
    [(list 'P p args) (string-join (cons (vector-ref extended-symbol-names p) (map term args)) " ")]
    [(list 'N a) (format "N ~a" (extended->named a depth))]
    [(list (or 'A 'X) a) (format "~a v~a ~a" (first f) depth (extended->named a (add1 depth)))]
    [(list (or 'I 'K 'D 'Q) a b) (format "~a ~a ~a" (first f) (extended->named a depth) (extended->named b depth))]))
(define (extended->debruijn f)
  (match f
    [(list 'E x y) (format "(dE ~a ~a)" x y)]
    [(list '= x y) (format "(dEq ~a ~a)" x y)]
    [(list 'P p args) (format "(dP ~a [~a])" p (string-join (map number->string args) ";"))]
    [(list (or 'N 'A 'X) a) (format "(d~a ~a)" (first f) (extended->debruijn a))]
    [(list (or 'I 'K 'D 'Q) a b) (format "(d~a ~a ~a)" (first f) (extended->debruijn a) (extended->debruijn b))]))
(define prototypes
  (for/list ([spec (in-list specs)] [id (in-naturals first-new-id)])
    (match-define (list name params label scope body) spec)
    (define closed-text
      (string-append (apply string-append (for/list ([p (in-list params)]) (format "A ~a " p)))
                     "Q " name " " (string-join params " ") " " body))
    (prototype name (length params) id label scope params body (parse-extended closed-text))))
(define prototype-validation
  (for/list ([p (in-list prototypes)])
    (define f (prototype-closed-formula p))
    (define closed? (closed-extended? f))
    (define named-roundtrip? (equal? f (parse-extended (extended->named f))))
    (define db-roundtrip? (equal? f (parse-dform (extended->debruijn f))))
    (define body (parse-extended (prototype-body p) (prototype-parameters p)))
    (define body-scoped? (closed-extended? body (prototype-arity p)))
    (unless (and closed? named-roundtrip? db-roundtrip? body-scoped?)
      (error 'prototype-validation "validation failed for ~a" (prototype-name p)))
    (list (prototype-name p) closed? named-roundtrip? db-roundtrip? body-scoped?)))
(module+ main
  (call-with-output-file "SET-EXTENSION-PROTOTYPES.tsv" #:exists 'error
    (lambda (out)
      (displayln "new_name\tarity\tsymbol_id\tsource_label\tset_only_scope\tnamed_defining_formula\tdebruijn_closed_formula" out)
      (for ([p (in-list prototypes)])
        (fprintf out "~a\t~a\t~a\t~a\t~a\t~a\t~a\n"
                 (prototype-name p) (prototype-arity p) (prototype-symbol-id p)
                 (prototype-source-label p) (prototype-scope p)
                 (extended->named (prototype-closed-formula p))
                 (extended->debruijn (prototype-closed-formula p))))))
  (printf "set_only_prototypes=~a fresh_ids=~a..~a validated=~a\n"
          (length prototypes) first-new-id (sub1 (vector-length extended-symbol-names))
          (length prototype-validation)))
