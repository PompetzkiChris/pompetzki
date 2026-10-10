#lang racket/base
;; Add an explicit new operator definition to each exact source-signature row.
(require racket/file racket/list racket/string)
(define input-path "EXTENSION-FORMULAS.tsv")
(define output-path "EXTENSION-FORMULAS-v2.tsv")
(define zname "mm_output_element")
(define (read-tsv path)
  (call-with-input-file path
    (lambda (in)
      (define header (string-split (read-line in) "\t" #:trim? #f))
      (values header
        (for/list ([line (in-lines in)] #:unless (string=? line ""))
          (define cols (string-split line "\t" #:trim? #f))
          (unless (= (length cols) (length header)) (error 'tsv "columns ~a" path))
          cols)))))
(define-values (header rows) (read-tsv input-path))
(define index (for/hash ([h header] [i (in-naturals)]) (values h i)))
(define (ref row key) (list-ref row (hash-ref index key)))
(define (tokens s) (string-split s))
(define (join ts) (string-join ts " "))
(define (untype s)
  (string-join (for/list ([v (tokens s)]) (car (string-split v ":"))) " , "))
(define (outer-index ts sought depth-target)
  (let loop ([rest ts] [i 0] [depth 0])
    (cond [(null? rest) #f]
          [else
           (define t (car rest))
           (cond [(and (= depth depth-target) (equal? t sought)) i]
                 [(equal? t "(") (loop (cdr rest) (add1 i) (add1 depth))]
                 [(equal? t ")") (loop (cdr rest) (add1 i) (sub1 depth))]
                 [else (loop (cdr rest) (add1 i) depth)])])))
(define (equation-parts label formula result)
  (define ts (cdr (tokens formula)))
  (cond
    [(equal? label "df-bi")
     (values "( ph <-> ps )" "-. ( ( ph -> ps ) -> -. ( ps -> ph ) )"
             "The source $a is the primitive negation/implication expansion of the biconditional between (ph <-> ps) and this conjunction of the two implications.")]
    [(equal? result "wff")
     (define i (outer-index ts "<->" 1))
     (unless (and i (equal? (car ts) "(") (equal? (last ts) ")"))
       (error 'equation "outer biconditional ~a" label))
     (values (join (take (cdr ts) (sub1 i)))
             (join (take (drop ts (add1 i)) (- (length ts) i 2)))
             "Exact right-hand side of the source outer biconditional.")]
    [else
     (define i (outer-index ts "=" 0))
     (unless i (error 'equation "outer class equality ~a" label))
     (values (join (take ts i)) (join (drop ts (add1 i)))
             "Exact right-hand side of the source outer class equality; class equality is extensional, so its member equation has a fresh set-variable input.")]))
(define new-header
  '("new_symbol" "new_symbol_signature" "new_symbol_typed_counts"
    "new_defining_formula" "exact_defining_rhs" "source_defined_expression"
    "rhs_extraction_receipt" "new_symbol_fixed_registry_arity"
    "formula_registration_boundary"))
(define verified 0)
(define definitions 0)
(call-with-output-file output-path #:exists 'error
  (lambda (out)
    (displayln (string-join (append header new-header) "\t") out)
    (for ([row rows])
      (define label (ref row "label"))
      (define result (ref row "operator_result"))
      (define formula (ref row "exact_source_extension_formula"))
      (define operands (ref row "operator_operands"))
      (define binders (ref row "operator_binder_names"))
      (define operands-list (tokens operands))
      (define binder-list (tokens binders))
      (define is-def (string-prefix? label "df-"))
      (define class-result (equal? result "class"))
      (define new-symbol
        (string-append "MM_" (string-replace label "-" "_")
                       (if class-result "_member" "")))
      (define signature
        (if is-def
            (string-join (append (if class-result (list (string-append zname ":setvar")) '()) operands-list
                                (for/list ([b binder-list]) (string-append b ":binder-name"))) " ")
            (ref row "mandatory_signature")))
      (define lhs
        (if is-def
            (string-append new-symbol " [ "
                           (string-join (append (if class-result (list zname) '())
                                               (for/list ([v operands-list]) (car (string-split v ":")))) " , ")
                           (if (pair? binder-list) (string-append " ; binder " (string-join binder-list " , ")) "")
                           " ]")
            (string-append new-symbol " [ " (untype signature) " ]")))
      (define-values (defined rhs receipt)
        (if is-def
            (equation-parts label formula result)
            (values "" (string-trim (substring formula 2))
                    "Exact source assertion body; essential premises and distinct-variable conditions stay in their separate columns.")))
      (define new-formula
        (string-append "( " lhs " <-> "
                       (if class-result (string-append zname " e. " rhs) rhs) " )"))
      (define sv (length (filter (lambda (v) (string-suffix? v ":setvar")) (tokens signature))))
      (define wv (length (filter (lambda (v) (string-suffix? v ":wff")) (tokens signature))))
      (define cv (length (filter (lambda (v) (string-suffix? v ":class")) (tokens signature))))
      (define bv (length (filter (lambda (v) (string-suffix? v ":binder-name")) (tokens signature))))
      (define count-str (format "setvar=~a;wff=~a;class=~a;binder-name=~a" sv wv cv bv))
      (define fixed
        (cond [(not is-def) "naming-schema-only; does not establish assertion/rule"]
              [(or (positive? wv) (positive? bv)) "none-for-full-source-schema"]
              [(positive? cv) (format "none-for-proper-class-operands; set-restricted arity=~a" (+ sv cv))]
              [class-result "1 after constants and operations receive fixed first-order interpretations"]
              [else "0 as a formula-syntax abbreviation"]))
      (define boundary
        (cond
          [(not is-def)
           "The displayed biconditional defines an abbreviation for this assertion body. It does not assert the source axiom and does not reproduce an inference rule from its essential hypotheses. A proof or admitted asserted schema/rule is separately required."]
          [(or (positive? wv) (positive? bv))
           "The new symbol is a typed schema operator. Formula substitutions and class membership substitutions must preserve their free parameters and bound-variable names by capture-avoiding translation; the schema is not a predicate on a fixed list of set values."]
          [(positive? cv)
           "The new symbol's class operands retain the full source equation. To become a registry definition, each class operand must be translated to its membership formula and free parameters. Restricting every class operand to a set value yields the stated finite set arity but is a smaller domain."]
          [class-result
           "The fresh member argument is a set variable. The right-hand side still contains source complex-number constants/addition; translate those to fixed first-order membership/graph formulas before registering an arity-1 definition."]
          [else
           "The new symbol abbreviates this closed formula. Universal-bound x in df-tru is an auxiliary variable, so the new symbol has no set argument."]))
      (define extra (list new-symbol signature count-str new-formula rhs defined receipt fixed boundary))
      (for ([f extra])
        (when (regexp-match? #rx"[\t\r\n]" f) (error 'tsv "newline/tab ~a" label)))
      (displayln (string-join (append row extra) "\t") out)
      (set! verified (add1 verified))
      (when is-def (set! definitions (add1 definitions))))))
(unless (= verified 167) (error 'count "labels ~a" verified))
(unless (= definitions 87) (error 'count "definitions ~a" definitions))
(printf "explicit_extension_formulas=~a defining_rhs_extracted=~a output=~a\n" verified definitions output-path)
