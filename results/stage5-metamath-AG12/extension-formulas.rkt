#lang racket/base
;; Exact source equations and signatures for the source-label union.
(require racket/file racket/list racket/string racket/match
         (file "C:/ClaudeOutput/pompetzki/lanes/L5/mm3.rkt"))
(define source-path "C:/ClaudeOutput/formalization-toolchain-20260924/libraries/metamath-set-mm-28167ed89a49/set.mm")
(define input-path "SOURCE-LABELS.tsv")
(define output-path "EXTENSION-FORMULAS.tsv")
(struct op (result operands binder-names) #:transparent)
(define specs (make-hash))
(define (add labels result operands [binders '()])
  (for ([label (string-split labels)])
    (when (hash-has-key? specs label) (error 'spec "duplicate ~a" label))
    (hash-set! specs label (op result (string-split operands) binders))))
;; Each operand is a typed source metavariable. A binder-name is a syntactic
;; variable-name input rather than a set-valued argument of a registry predicate.
(add "df-bi df-an df-or df-nan df-xor df-nor df-vd1 df-vhc2" "wff" "ph:wff ps:wff")
(add "df-ifp df-3or df-3an df-had df-cad df-3nand df-redundp df-vd2 df-vhc3" "wff" "ph:wff ps:wff ch:wff")
(add "df-bnj17 df-vd3" "wff" "ph:wff ps:wff ch:wff th:wff")
(add "df-tru df-fal" "wff" "")
(add "df-ex df-nf df-mo df-eu df-bj-nnf" "wff" "ph:wff" '("x"))
(add "df-sb" "wff" "ph:wff t:setvar" '("x"))
(add "df-cdeq" "wff" "ph:wff x:setvar y:setvar")
(add "df-ich" "wff" "ph:wff" '("x" "y"))
(add "df-cleq df-clel df-ne df-nel df-ss df-pss" "wff" "A:class B:class")
(add "df-nfc" "wff" "A:class" '("x"))
(add "df-ral df-rex df-rmo df-reu" "wff" "ph:wff A:class" '("x"))
(add "df-als df-alseu" "wff" "ph:wff ps:wff" '("x"))
(add "df-rals df-ralseu" "wff" "ph:wff ps:wff A:class" '("x"))
(add "df-2reu" "wff" "ph:wff A:class B:class" '("x" "y"))
(add "df-disj" "wff" "A:class B:class" '("x"))
(add "df-br" "wff" "A:class R:class B:class")
(add "df-tr df-rel df-ord df-lim df-fun df-smo" "wff" "A:class")
(add "df-po df-so df-fr df-we df-er df-bnj13 df-bnj15 df-dmqs df-erALTV df-part" "wff" "R:class A:class")
(add "df-fn" "wff" "A:class B:class")
(add "df-f df-f1 df-fo df-f1o" "wff" "F:class A:class B:class")
(add "df-isom df-relp" "wff" "H:class R:class S:class A:class B:class")
(add "df-bnj19" "wff" "B:class A:class R:class")
(add "df-eqvrel df-disjALTV" "wff" "R:class")
(add "df-rn" "class" "A:class")
(add "df-txp df-pprod" "class" "A:class B:class")
(add "df-qmap" "class" "R:class")
(add "df-adjliftmap df-blockliftmap" "class" "R:class A:class")
(add "df-2 df-3 df-4 df-5 df-6 df-7 df-8 df-9" "class" "")
(define (parts s) (if (string=? s "") '() (string-split s)))
(define (var-name v) (car (string-split v ":")))
(define (var-type v) (cadr (string-split v ":")))
(define (count-type vars ty) (count (lambda (v) (equal? (var-type v) ty)) vars))
(define (typed-count vars)
  (format "setvar=~a;wff=~a;class=~a" (count-type vars "setvar") (count-type vars "wff") (count-type vars "class")))
(define (stringify ts) (string-join (vector->list ts) " "))
(define db (read-db source-path))
(define rows
  (call-with-input-file input-path
    (lambda (in) (read-line in)
      (for/list ([line (in-lines in)] #:unless (string=? line ""))
        (define cols (string-split line "\t" #:trim? #f))
        (unless (= 7 (length cols)) (error 'input "column count ~a" (length cols)))
        cols))))
(unless (= (length rows) 167) (error 'input "labels ~a" (length rows)))
(define algebra-labels
  (string-split "ax-cnex ax-resscn ax-1cn ax-icn ax-addcl ax-addrcl ax-mulcl ax-mulrcl ax-mulcom ax-addass ax-mulass ax-distr ax-i2m1 ax-1ne0 ax-rnegex ax-cnre"))
(define hilbert-labels
  (string-split "ax-hvcom ax-hvass ax-hv0cl ax-hvaddid ax-hvmulass ax-hvdistr1 ax-his1"))
(define modality-labels (string-split "ax-prv1 ax-prv2 ax-prv3"))
(define (definition-note label spec mandatory)
  (cond
    [(or (positive? (count-type (op-operands spec) "wff"))
         (pair? (op-binder-names spec)))
     "The displayed source equation is a typed syntactic schema. Arbitrary wff/class substitutions carry arbitrary finite free-variable support. Binder-name inputs are syntactic names, not values in the set domain. No fixed set-variable predicate arity represents the full operator; use capture-avoiding formula/class translation for each instance."]
    [(positive? (count-type (op-operands spec) "class"))
     "The displayed source equation defines the full class-valued/class-argument operator. A registry predicate accepts set values only; the source class arguments may be proper classes. Replacing classes by set variables gives only the set-restricted instance. Preserve the full equation by translating each class to its membership formula with its free parameters."]
    [(equal? (op-result spec) "class")
     "The displayed source equation defines a nullary class constant. A registry uses predicates on set variables, so its graph would have one set argument and require a fixed first-order interpretation of the complex-number constants and addition. Copying the numeral equation without those interpretations is not a registry definition."]
    [else
     "This nullary wff operator has no set-valued arguments. Its exact source equation can be expanded in formula syntax; df-tru has a dummy bound x, not a unary predicate input."]))
(define (axiom-note label mandatory)
  (cond
    [(member label algebra-labels)
     "This is an asserted complex/real-number axiom with the displayed typed signature, not an operator definition. Supplying definitional interpretations of CC, RR, numeric constants and arithmetic must be followed by a derivation of this assertion; adding P <-> this body only abbreviates the assertion and does not prove it."]
    [(member label hilbert-labels)
     "This is an asserted Hilbert-space axiom with the displayed typed signature, not an operator definition. The primitive space and operations need fixed interpretations and a derivation of this assertion; a predicate definition alone does not supply the asserted equation or closure fact."]
    [(member label modality-labels)
     "Prv is a primitive unary wff operator. The displayed assertion/rule is a modal provability schema, not a definition of that operator. Substituting identity for Prv is a separate interpretation and does not establish the supplied primitive schema."]
    [(equal? label "ax-mp")
     "This is the inference rule from ph and (ph -> ps) to ps. Preserve both essential premises. Registering the conclusion as a definition does not supply the rule."]
    [(equal? label "ax-gen")
     "This is the generalization rule from ph to A. x ph. Preserve the essential premise and the source rule's substitution conditions. It is not a predicate definition."]
    [else
     "This is an asserted axiom/schema with the displayed mandatory signature and distinct-variable conditions. A missing numbered registry entry needs a derivation under the judge rules or an admitted axiom/schema. Defining P <-> this body only abbreviates the body and does not assert it."]))
(define (arity-note label spec mandatory)
  (if spec
      (format "result=~a; operands(~a); binder_names=~a; fixed_registry_set_arity=~a"
              (op-result spec) (typed-count (op-operands spec))
              (length (op-binder-names spec))
              (cond
                [(or (positive? (count-type (op-operands spec) "wff"))
                     (positive? (count-type (op-operands spec) "class"))
                     (pair? (op-binder-names spec))) "none-for-full-schema"]
                [(equal? (op-result spec) "class") "1-only-after-fixed-constant-interpretation"]
                [else "0-formula-abbreviation"]))
      (format "assertion-or-rule; mandatory(~a); new_definition_arity=not-applicable" (typed-count mandatory))))
(define (set-restricted-graph label spec)
  (cond
    [(not spec) "not a definition"]
    [(or (positive? (count-type (op-operands spec) "wff")) (pair? (op-binder-names spec)))
     "not a fixed predicate: formula or binder-name operands"]
    [(equal? (op-result spec) "class")
     (format "set-restricted graph arity ~a = ~a class operands replaced by set values + 1 result set; the exact source equality remains the defining equation"
             (add1 (length (op-operands spec))) (length (op-operands spec)))]
    [else (format "set-restricted predicate arity ~a; exact source biconditional applies after each class operand is restricted to a set value"
                  (length (op-operands spec)))]))
(define verified 0)
(call-with-output-file output-path #:exists 'error
  (lambda (out)
    (display "label\tmandatory_signature\tmandatory_typed_counts\toperator_result\toperator_operands\toperator_binder_names\tauxiliary_or_dummy_variables\textension_arity\texact_source_extension_formula\tessential_hypotheses\tdistinct_variable_pairs\tset_restricted_graph_arity\textension_kind\tregistry_extension_boundary\n" out)
    (for ([cols rows])
      (define label (list-ref cols 1))
      (define a (lookup db label))
      (define mandatory
        (for/list ([h (assr-hyps a)] #:when (fhyp? (lookup db h)))
          (define f (lookup db h))
          (string-append (fhyp-var f) ":" (fhyp-type f))))
      (define src (string-append (assr-type a) " " (stringify (assr-toks a))))
      (unless (equal? src (list-ref cols 3)) (error 'source "statement mismatch ~a" label))
      (unless (equal? (string-join mandatory " ") (list-ref cols 5)) (error 'source "signature mismatch ~a" label))
      (define spec (hash-ref specs label #f))
      (when (and (string-prefix? label "df-") (not spec)) (error 'spec "missing ~a" label))
      (define op-vars (if spec (append (map var-name (op-operands spec)) (op-binder-names spec)) '()))
      (for ([operand op-vars])
        (unless (member operand (map var-name mandatory)) (error 'spec "~a missing operand ~a" label operand)))
      (define auxiliaries (if spec (filter (lambda (v) (not (member (var-name v) op-vars))) mandatory) '()))
      (define kind
        (cond [(not spec) (if (pair? (parts (list-ref cols 4))) "asserted-rule" "asserted-axiom/schema")]
              [(or (positive? (count-type (op-operands spec) "wff")) (pair? (op-binder-names spec))) "typed-definition-schema"]
              [(positive? (count-type (op-operands spec) "class")) "typed-class-definition"]
              [(equal? (op-result spec) "class") "nullary-class-constant-definition"]
              [else "nullary-formula-abbreviation"]))
      (define fields
        (list label (string-join mandatory " ") (typed-count mandatory)
              (if spec (op-result spec) "assertion")
              (if spec (string-join (op-operands spec) " ") "")
              (if spec (string-join (op-binder-names spec) " ") "")
              (string-join auxiliaries " ")
              (arity-note label spec mandatory) src (list-ref cols 4) (list-ref cols 6)
              (set-restricted-graph label spec) kind
              (if spec (definition-note label spec mandatory) (axiom-note label mandatory))))
      (for ([f fields])
        (when (regexp-match? #rx"[\t\r\n]" f) (error 'tsv "newline/tab in ~a" label)))
      (displayln (string-join fields "\t") out)
      (set! verified (add1 verified)))))
(unless (= verified 167) (error 'source "verified count ~a" verified))
(unless (= (hash-count specs) 87) (error 'spec "definition count ~a" (hash-count specs)))
(printf "source_formulas_verified=~a definition_signatures=~a output=~a\n" verified (hash-count specs) output-path)
