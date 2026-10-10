#lang racket/base
;; leanstmt.rkt -- lane L6: reads lean/export-nat.sexp (written by lean/L6Export.lean) and turns each Lean statement into
;; a first-order statement over the natural numbers, or says why it is outside the first slice. Untrusted.
;;
;; Statement syntax produced (the sentence language of sigma1.rkt, plus unbounded quantifiers over omega):
;;   terms    x | n | (S t) | (+ t u) | (* t u)
;;   formulas (= t u) (< t u) (<= t u) (not F) (and F G) (or F G) (imp F G) (iff F G) (nall x F) (some x F)
;; Lean's  a ≥ b  is  b ≤ a  and  a > b  is  b < a  (GE.ge / GT.gt unfold to LE.le / LT.lt);  a ≠ b  is  ¬(a = b).
;; Every instance argument must be the canonical one: instHAdd ℕ instAddNat, instHMul ℕ instMulNat, instLENat,
;; instLTNat, instOfNatNat n. Anything else is refused.
(require racket/list racket/string racket/match racket/file)
(provide read-export lean->stmt stmt->string)

(define (read-export path)
  (with-input-from-file path
    (lambda ()
      (let loop ([acc '()])
        (define x (read))
        (if (eof-object? x) (reverse acc)
            (match x [(list 'thm name mod ty) (loop (cons (list name mod ty) acc))]))))))

(define NAT '(const "Nat"))
(define (app* f . args) (for/fold ([e f]) ([a args]) (list 'app e a)))
;; the head and arguments of an application spine
(define (spine e)
  (let loop ([e e] [args '()])
    (match e [(list 'app f a) (loop f (cons a args))] [_ (values e args)])))

(struct refuse (why))
(define (no why . xs) (raise (refuse (apply format why xs))))

;; ctx: list of entries for bvar 0, 1, ...: (list 'var sym) for a ℕ variable, (list 'hyp) for a proof binder
(define (term e ctx)
  (define-values (h args) (spine e))
  (match* (h args)
    [((list 'bvar i) '())
     (match (list-ref ctx i) [(list 'var x) x] [_ (no "bvar ~a is not a natural number" i)])]
    [('(const "HAdd.hAdd") (list (== NAT) (== NAT) (== NAT) inst a b))
     (unless (equal? inst (app* '(const "instHAdd") NAT '(const "instAddNat"))) (no "+ with instance ~a" inst))
     (list '+ (term a ctx) (term b ctx))]
    [('(const "HMul.hMul") (list (== NAT) (== NAT) (== NAT) inst a b))
     (unless (equal? inst (app* '(const "instHMul") NAT '(const "instMulNat"))) (no "* with instance ~a" inst))
     (list '* (term a ctx) (term b ctx))]
    [('(const "Nat.succ") (list a)) (list 'S (term a ctx))]
    [('(const "OfNat.ofNat") (list (== NAT) (list 'lit n) inst))
     (unless (equal? inst (app* '(const "instOfNatNat") (list 'lit n))) (no "numeral with instance ~a" inst))
     n]
    [(_ _) (no "term ~a" (car (flatten (list h))))]))

(define (prop? e)
  ;; the types this translator reads as propositions
  (define-values (h args) (spine e))
  (member h '((const "Eq") (const "Ne") (const "Not") (const "And") (const "Or") (const "Iff") (const "Exists")
              (const "LE.le") (const "LT.lt") (const "GE.ge") (const "GT.gt"))))

(define counter 0)
(define (fresh base) (set! counter (add1 counter)) (string->symbol (format "~a~a" (sanitize base) counter)))
(define (sanitize s)
  (define t (list->string (for/list ([c s] #:when (or (char-alphabetic? c) (char-numeric? c))) c)))
  (if (or (string=? t "") (not (char-alphabetic? (string-ref t 0)))) "x" (string-downcase (substring t 0 (min 6 (string-length t))))))

(define (form e ctx)
  (define-values (h args) (spine e))
  (match* (h args)
    [('(const "Eq") (list (== NAT) a b)) (list '= (term a ctx) (term b ctx))]
    [('(const "Ne") (list (== NAT) a b)) (list 'not (list '= (term a ctx) (term b ctx)))]
    [('(const "LE.le") (list (== NAT) inst a b))
     (unless (equal? inst '(const "instLENat")) (no "<= with instance ~a" inst))
     (list '<= (term a ctx) (term b ctx))]
    [('(const "LT.lt") (list (== NAT) inst a b))
     (unless (equal? inst '(const "instLTNat")) (no "< with instance ~a" inst))
     (list '< (term a ctx) (term b ctx))]
    [('(const "GE.ge") (list (== NAT) inst a b))
     (unless (equal? inst '(const "instLENat")) (no ">= with instance ~a" inst))
     (list '<= (term b ctx) (term a ctx))]
    [('(const "GT.gt") (list (== NAT) inst a b))
     (unless (equal? inst '(const "instLTNat")) (no "> with instance ~a" inst))
     (list '< (term b ctx) (term a ctx))]
    [('(const "Not") (list a)) (list 'not (form a ctx))]
    [('(const "And") (list a b)) (list 'and (form a ctx) (form b ctx))]
    [('(const "Or") (list a b)) (list 'or (form a ctx) (form b ctx))]
    [('(const "Iff") (list a b)) (list 'iff (form a ctx) (form b ctx))]
    [('(const "Exists") (list (== NAT) (list 'lam nm _ (== NAT) body)))
     (define x (fresh nm))
     (list 'some x (form body (cons (list 'var x) ctx)))]
    [((list 'pi nm bi dom body) '())
     (cond
       [(equal? dom NAT) (define x (fresh nm)) (list 'nall x (form body (cons (list 'var x) ctx)))]
       [(prop? dom)
        ;; an implication; the body must not use the proof binder
        (when (uses-bvar0? body) (no "dependent hypothesis"))
        (list 'imp (form dom ctx) (form body (cons '(hyp) ctx)))]
       [else (no "binder of type ~a" (let-values ([(hh aa) (spine dom)]) hh))])]
    [(_ _) (no "proposition ~a" (if (pair? h) (take h (min 2 (length h))) h))]))

(define (uses-bvar0? e)
  (let walk ([e e] [k 0])
    (match e
      [(list 'bvar i) (= i k)]
      [(list 'app f a) (or (walk f k) (walk a k))]
      [(list (or 'pi 'lam) _ _ d b) (or (walk d k) (walk b (add1 k)))]
      [_ #f])))

;; (values stmt #f) or (values #f reason)
(define (lean->stmt ty)
  (set! counter 0)
  (with-handlers ([refuse? (lambda (r) (values #f (refuse-why r)))])
    (values (form ty '()) #f)))

(define (stmt->string f)
  (define (t x)
    (match x
      [(? symbol?) (symbol->string x)] [(? exact-integer?) (number->string x)]
      [(list 'S a) (format "S(~a)" (t a))]
      [(list '+ a b) (format "(~a + ~a)" (t a) (t b))] [(list '* a b) (format "(~a * ~a)" (t a) (t b))]))
  (match f
    [(list '= a b) (format "~a = ~a" (t a) (t b))]
    [(list '< a b) (format "~a < ~a" (t a) (t b))]
    [(list '<= a b) (format "~a ≤ ~a" (t a) (t b))]
    [(list 'not a) (format "¬(~a)" (stmt->string a))]
    [(list 'and a b) (format "(~a ∧ ~a)" (stmt->string a) (stmt->string b))]
    [(list 'or a b) (format "(~a ∨ ~a)" (stmt->string a) (stmt->string b))]
    [(list 'imp a b) (format "(~a → ~a)" (stmt->string a) (stmt->string b))]
    [(list 'iff a b) (format "(~a ↔ ~a)" (stmt->string a) (stmt->string b))]
    [(list 'nall x a) (format "∀~a:ℕ, ~a" x (stmt->string a))]
    [(list 'some x a) (format "∃~a:ℕ, ~a" x (stmt->string a))]))

(module+ main
  (define ths (read-export "C:/ClaudeOutput/pompetzki/lanes/L6/lean/export-nat.sexp"))
  (define ok 0)
  (for ([t (sort ths string<? #:key car)])
    (match-define (list name mod ty) t)
    (define-values (s why) (lean->stmt ty))
    (if s
        (begin (set! ok (add1 ok)) (printf "OK ~a [~a] ~a\n" name mod (stmt->string s)))
        (printf "NO ~a [~a] ~a\n" name mod why)))
  (printf "translated ~a of ~a\n" ok (length ths)))
