#lang racket
;; Read-only source transcription with exact natural-number de Bruijn indices.
(require racket/list racket/match racket/string racket/file)
(provide (struct-out reg-entry) registry registry-vector symbol-names symbol-arity
         registry-ref formula->prefix formula->named formula->pretty formula->core
         closed-formula? parse-named-formula parse-dform registry-validation
         source-paths)

(struct reg-entry (index kind name arity formula source-body parameters) #:transparent)
(define source-base "C:/ClaudeOutput/pompetzki/forcing-src/general/")
(define source-paths
  (list (string-append source-base "RpInit.v")
        (string-append source-base "Data.v")
        (string-append source-base "Syn.v")
        (string-append source-base "Ax.v")
        (string-append source-base "Replay2.v")
        (string-append source-base "replay/mkreplay.pl")
        "C:/ClaudeOutput/pompetzki/lib/zfc.pmp"))
(define data-text (file->string (second source-paths)))
(define init-text (file->string (first source-paths)))

;; Extract a list assignment while respecting inner argument lists and strings.
(define (assignment-list text name)
  (define start-match
    (regexp-match-positions
     (pregexp (string-append "Definition\\s+" (regexp-quote name) "\\s[^=]*:=\\s*\\[")) text))
  (unless start-match (error 'assignment-list "assignment absent: ~a" name))
  (define start (cdar start-match))
  (let loop ([i start] [depth 1] [quoted? #f])
    (when (>= i (string-length text)) (error 'assignment-list "unterminated ~a" name))
    (define c (string-ref text i))
    (cond
      [(char=? c #\") (loop (add1 i) depth (not quoted?))]
      [quoted? (loop (add1 i) depth #t)]
      [(char=? c #\[) (loop (add1 i) (add1 depth) #f)]
      [(char=? c #\]) (if (= depth 1) (substring text start i)
                             (loop (add1 i) (sub1 depth) #f))]
      [else (loop (add1 i) depth #f)])))

(define (quoted-strings text)
  (regexp-match* #px"\"([^\"]*)\"" text #:match-select cadr))
(define symbol-names (list->vector (quoted-strings (assignment-list data-text "symtab"))))
(define symbol-ids
  (for/hash ([name (in-vector symbol-names)] [i (in-naturals)]) (values name i)))
(define symbol-arity
  (for/hash ([name (in-vector symbol-names)])
    (define suffix (regexp-match #px"([0-9]+)$" name))
    (unless suffix (error 'symbol-arity "no arity suffix in ~a" name))
    (values name (string->number (cadr suffix)))))
(define defs
  (regexp-match* #px"\\(\"([^\"]+)\",\\s*\\[([^]]*)\\],\\s*\"([^\"]*)\"\\)"
                 (assignment-list data-text "defs")
                 #:match-select (lambda (m) (list (second m) (quoted-strings (third m)) (fourth m)))))

;; AST: (E x y), (= x y), (P symbol-id (args ...)), (N f), (A f),
;; (X f), and (I/K/D/Q f g). Integers are exact and zero-based.
(define (parse-dform text)
  (define tokens (list->vector (regexp-match* #px"dEq|d[A-Z]|[0-9]+|[()\\[\\];]" text)))
  (define cursor 0)
  (define (take)
    (when (>= cursor (vector-length tokens)) (error 'parse-dform "unexpected end"))
    (begin0 (vector-ref tokens cursor) (set! cursor (add1 cursor))))
  (define (expect str) (define x (take)) (unless (equal? x str) (error 'parse-dform "expected ~a received ~a" str x)))
  (define (nat)
    (define v (string->number (take)))
    (unless (exact-nonnegative-integer? v) (error 'parse-dform "natural expected")) v)
  (define (args)
    (expect "[")
    (if (equal? (vector-ref tokens cursor) "]") (begin (take) '())
        (let loop ([result (list (nat))])
          (match (take)
            ["]" (reverse result)]
            [";" (loop (cons (nat) result))]
            [x (error 'parse-dform "argument separator expected, received ~a" x)]))))
  (define (form)
    (expect "(")
    (define op (take))
    (define result
      (match op
        ["dE" (list 'E (nat) (nat))]
        ["dEq" (list '= (nat) (nat))]
        ["dP" (list 'P (nat) (args))]
        [(or "dN" "dA" "dX") (list (string->symbol (substring op 1)) (form))]
        [(or "dI" "dK" "dD" "dQ") (list (string->symbol (substring op 1)) (form) (form))]
        [x (error 'parse-dform "unknown constructor ~a" x)]))
    (expect ")") result)
  (define answer (form))
  (unless (= cursor (vector-length tokens)) (error 'parse-dform "extra tokens")) answer)

(define (parse-dform-list text)
  (define len (string-length text))
  (let loop ([i 0] [start #f] [depth 0] [out '()])
    (cond
      [(= i len) (unless (= depth 0) (error 'parse-dform-list "unbalanced source")) (reverse out)]
      [else
       (define c (string-ref text i))
       (cond
         [(char=? c #\() (loop (add1 i) (or start i) (add1 depth) out)]
         [(char=? c #\))
          (if (= depth 1)
              (loop (add1 i) #f 0 (cons (parse-dform (substring text start (add1 i))) out))
              (loop (add1 i) start (sub1 depth) out))]
         [else (loop (add1 i) start depth out)])])))

(define (parse-named-formula text [parameters '()])
  (define tokens (list->vector (string-split text)))
  (define cursor 0)
  (define (take)
    (when (>= cursor (vector-length tokens)) (error 'parse-named-formula "unexpected end of ~a" text))
    (begin0 (vector-ref tokens cursor) (set! cursor (add1 cursor))))
  (define (term env)
    (define name (take))
    (define b (index-of env name))
    (define p (index-of parameters name))
    (cond [b b] [p (+ (length env) p)]
          [else (error 'parse-named-formula "unbound variable ~a in ~a" name text)]))
  (define (form env)
    (define op (take))
    (match op
      ["N" (list 'N (form env))]
      [(or "A" "X") (define name (take)) (list (string->symbol op) (form (cons name env)))]
      [(or "I" "K" "D" "Q") (list (string->symbol op) (form env) (form env))]
      [(or "E" "=") (list (string->symbol op) (term env) (term env))]
      [name
       (unless (hash-has-key? symbol-ids name) (error 'parse-named-formula "unknown predicate ~a" name))
       (list 'P (hash-ref symbol-ids name) (for/list ([i (in-range (hash-ref symbol-arity name))]) (term env)))]))
  (define result (form '()))
  (unless (= cursor (vector-length tokens)) (error 'parse-named-formula "extra tokens in ~a" text)) result)

(define ax-names
  (let ([m (regexp-match #px"my @AXN = qw\\(([^)]*)\\)" (file->string (sixth source-paths)))])
    (unless m (error 'ax-names "AXN source declaration absent")) (string-split (second m))))
(define ax-source
  (for/hash ([m (in-list (regexp-match* #px"text zi_n \"([^\"]+)\"\\r?\\ntext zi_f \"([^\"]*)\""
                                          (file->string (seventh source-paths)) #:match-select values))])
    (values (second m) (third m))))
(define ax-forms (parse-dform-list (assignment-list init-text "AX0")))
(define def-forms (parse-dform-list (assignment-list init-text "DEF0")))
(unless (= (length ax-names) 7 (length ax-forms)) (error 'registry-reader "AX0 count mismatch"))
(unless (= (length defs) 670 (length def-forms)) (error 'registry-reader "DEF0 count mismatch"))
(define registry
  (append
   (for/list ([formula (in-list ax-forms)] [name (in-list ax-names)] [i (in-naturals)])
     (reg-entry i 'axiom name 0 formula (hash-ref ax-source name) '()))
   (for/list ([formula (in-list def-forms)] [d (in-list defs)] [i (in-naturals 7)])
     (reg-entry i 'definition (string-append "Def:" (first d)) (length (second d))
                formula (third d) (second d)))))
(define registry-vector (list->vector registry))
(define (registry-ref index) (vector-ref registry-vector index))

(define (closed-formula? f [depth 0])
  (define (ok x) (and (exact-nonnegative-integer? x) (< x depth)))
  (match f
    [(list (or 'E '=) x y) (and (ok x) (ok y))]
    [(list 'P p args) (and (exact-nonnegative-integer? p) (< p (vector-length symbol-names))
                           (= (length args) (hash-ref symbol-arity (vector-ref symbol-names p)))
                           (andmap ok args))]
    [(list 'N a) (closed-formula? a depth)]
    [(list (or 'A 'X) a) (closed-formula? a (add1 depth))]
    [(list (or 'I 'K 'D 'Q) a b) (and (closed-formula? a depth) (closed-formula? b depth))]
    [_ #f]))
(define (formula->prefix f)
  (match f
    [(list (or 'E '=) x y) (format "~a ~a ~a" (first f) x y)]
    [(list 'P p args) (string-join (cons (format "P~a/~a" p (length args)) (map number->string args)) " ")]
    [(list (or 'N 'A 'X) a) (format "~a ~a" (first f) (formula->prefix a))]
    [(list (or 'I 'K 'D 'Q) a b) (format "~a ~a ~a" (first f) (formula->prefix a) (formula->prefix b))]))
(define (formula->named f [depth 0])
  (define (term x) (if (< x depth) (format "v~a" (- depth x 1)) (format "f~a" (- x depth))))
  (match f
    [(list (or 'E '=) x y) (format "~a ~a ~a" (first f) (term x) (term y))]
    [(list 'P p args) (string-join (cons (vector-ref symbol-names p) (map term args)) " ")]
    [(list 'N a) (format "N ~a" (formula->named a depth))]
    [(list (or 'A 'X) a) (format "~a v~a ~a" (first f) depth (formula->named a (add1 depth)))]
    [(list (or 'I 'K 'D 'Q) a b) (format "~a ~a ~a" (first f) (formula->named a depth) (formula->named b depth))]))
(define (formula->pretty f [depth 0])
  (define (term x) (if (< x depth) (format "v~a" (- depth x 1)) (format "f~a" (- x depth))))
  (match f
    [(list 'E x y) (format "(~a in ~a)" (term x) (term y))]
    [(list '= x y) (format "(~a = ~a)" (term x) (term y))]
    [(list 'P p args) (format "~a(~a)" (vector-ref symbol-names p) (string-join (map term args) ","))]
    [(list 'N a) (format "not ~a" (formula->pretty a depth))]
    [(list (or 'A 'X) a) (format "(~a v~a. ~a)" (if (eq? (first f) 'A) "forall" "exists") depth
                                (formula->pretty a (add1 depth)))]
    [(list (or 'I 'K 'D 'Q) a b)
     (format "(~a ~a ~a)" (formula->pretty a depth)
             (hash-ref (hash 'I "->" 'K "and" 'D "or" 'Q "<->") (first f))
             (formula->pretty b depth))]))
(define (formula->core f)
  (match f
    [(list (or 'E '= 'P) _ _) f]
    [(list 'N a) (list 'N (formula->core a))]
    [(list 'A a) (list 'A (formula->core a))]
    [(list 'I a b) (list 'I (formula->core a) (formula->core b))]
    [(list 'X a) (list 'N (list 'A (list 'N (formula->core a))))]
    [(list 'K a b) (list 'N (list 'I (formula->core a) (list 'N (formula->core b))))]
    [(list 'D a b) (list 'I (list 'N (formula->core a)) (formula->core b))]
    [(list 'Q a b) (formula->core (list 'K (list 'I a b) (list 'I b a)))]))

(define registry-validation
  (for/list ([e (in-list registry)])
    (define source-form
      (if (eq? (reg-entry-kind e) 'axiom) (reg-entry-source-body e)
          (string-append (apply string-append (for/list ([p (in-list (reg-entry-parameters e))]) (format "A ~a " p)))
                         "Q " (substring (reg-entry-name e) 4) " "
                         (string-join (reg-entry-parameters e) " ") " " (reg-entry-source-body e))))
    (define same? (equal? (reg-entry-formula e) (parse-named-formula source-form)))
    (define closed? (closed-formula? (reg-entry-formula e)))
    (define roundtrip? (equal? (reg-entry-formula e) (parse-named-formula (formula->named (reg-entry-formula e)))))
    (unless (and same? closed? roundtrip?)
      (error 'registry-validation "index ~a source=~a closed=~a roundtrip=~a" (reg-entry-index e) same? closed? roundtrip?))
    (list (reg-entry-index e) same? closed? roundtrip?)))

(module+ main
  (define argv (current-command-line-arguments))
  (define destination (if (= (vector-length argv) 0) "REGISTRY.tsv" (vector-ref argv 0)))
  (call-with-output-file destination #:exists 'error
    (lambda (out)
      (fprintf out "registry_index\tkind\tname\tarity\tnamed_prefix\tde_bruijn_prefix\tprinted_formula\tsource_body\tparameters\tvalidation\n")
      (for ([e (in-list registry)])
        (fprintf out "~a\t~a\t~a\t~a\t~a\t~a\t~a\t~a\t~a\tclosed;source-identical;roundtrip\n"
                 (reg-entry-index e) (reg-entry-kind e) (reg-entry-name e) (reg-entry-arity e)
                 (formula->named (reg-entry-formula e)) (formula->prefix (reg-entry-formula e))
                 (formula->pretty (reg-entry-formula e)) (reg-entry-source-body e)
                 (string-join (reg-entry-parameters e) " ")))))
  (printf "entries=~a axioms=~a definitions=~a symbol-count=~a validated=~a destination=~a\n"
          (length registry) (length ax-forms) (length def-forms) (vector-length symbol-names)
          (length registry-validation) destination))
