#lang racket/base
(require racket/file racket/list racket/string)

;; Creation-only ORDER-2 dependency classification. The step names are read
;; against Replay2.v and judge/racket/judge.rkt. Lists name a derivation's
;; constructors; these rows do not assert that the entire derivation was emitted.
(define conditional '("ax-frege52c" "ax-frege54c"))
(define missing '("ax-prv1" "ax-prv2" "ax-prv3"))
(define routes
  (hash
   "ax-mp" '("M" "" "SMp" "Two source essential hypotheses become prior lines; M applies them in minor,major order.")
   "ax-gen" '("G" "" "SGen" "Source essential hypothesis becomes a prior line; G binds its specified frame variable. Conditional proofs use H after hypotheses are closed.")
   "ax-4" '("Y" "dist" "SAx" "Universal quantifier distribution is a directly recognized axshape.")
   "ax-5" '("Y" "vac" "SAx" "Vacuous quantification is a directly recognized axshape; the source distinct-variable condition prevents free x in ph.")
   "ax-6" '("Y;E;M (or Y;V;T)" "refl" "SAx;SExi;SMp (or SAx;SInst;STaut)" "Reflexivity y=y, existential introduction with witness y, and modus ponens derive not forall x not x=y; specialization plus propositional reasoning also derives it.")
   "ax-7" '("Z" "" "SLeib" "Apply equality substitution to the formula u=z. The result is x=y -> (x=z -> y=z).")
   "ax-8" '("Z" "" "SLeib" "Apply equality substitution to the formula u e. z.")
   "ax-9" '("Z" "" "SLeib" "Apply equality substitution to the formula z e. u.")
   "ax-10" '("Y" "vac" "SAx" "The antecedent not forall x ph has no free x, so vac applies directly after binding and de Bruijn translation.")
   "ax-11" '("V;V;T;H;H" "" "SInst;STaut;SAlli" "Specialize the two quantifiers, compose the implications, then generalize each antecedent-free variable to commute quantifiers.")
   "ax-12" '("Z;Y;V;T;H" "refl" "SLeib;SAx;SInst;STaut;SAlli" "Equality substitution and specialization, with a fresh variable, give the guarded universal conclusion.")
   "ax-13" '("Y;Z;T" "vac;refl" "SAx;SLeib;STaut" "Use vacuity when x is distinct from the equality's variables; use reflexivity or equality substitution for permitted variable identifications.")
   "ax-wl-13v" '("Y;G;T" "vac;refl" "SAx;SGen;STaut" "Vacuity proves the consequent for distinct x,y; when x=y, generalized reflexivity contradicts the antecedent. Source x,z and y,z disjoint conditions remain required.")
   "ax-c5" '("V" "" "SInst" "Specialization at the same variable directly gives forall x ph -> ph.")
   "ax-c4" '("Y;T" "dist;vac" "SAx;STaut" "Distribution gives the quantified implication; vacuity of forall x ph supplies quantifier idempotence; propositional composition gives the source formula.")
   "ax-c7" '("Y;V;T" "vac" "SAx;SInst;STaut" "Vacuity of not forall x ph and contraposition yield forall x ph; specialize to ph.")
   "ax-c10" '("V;Y;V;T" "refl" "SInst;SAx;STaut" "Specialize the outer quantifier at y, use y=y, then specialize the inner universal formula.")
   "ax-c11" '("V;Z;T;H" "" "SInst;SLeib;STaut;SAlli" "Specialization and equality substitution give the result at a fresh variable; conditional universal introduction yields forall y ph.")
   "ax-c11n" '("V;Y;Z;T;H" "refl" "SInst;SAx;SLeib;STaut;SAlli" "Specialize forall x x=y, derive equality symmetry from reflexivity and substitution, then introduce the universal conclusion.")
   "ax-c15" '("V;Z;T;H" "" "SInst;SLeib;STaut;SAlli" "Equality substitution at a fresh variable gives the guarded ph consequence; introduce its universal quantifier and retain the source antecedents.")
   "ax-c9" '("V;Z;Y;T;H" "vac;refl" "SInst;SLeib;SAx;STaut;SAlli" "Equality case analysis, substitution, and conditional quantification give the equality-vacuity schema for all permitted variable identifications.")
   "ax-c14" '("V;Z;Y;T;H" "vac;refl" "SInst;SLeib;SAx;STaut;SAlli" "Equality case analysis and membership substitution give the membership-vacuity schema; source negated universals guard variable identifications.")
   "ax-c16" '("V;Z;T;H" "" "SInst;SLeib;STaut;SAlli" "Under forall x x=y, specialization identifies every value with y; equality substitution and conditional quantification give forall x ph. Retain source d(x,y).")
   "ax-frege52c" '("Z;V;T;H (conditional)" "" "SLeib;SInst;STaut;SAlli" "Order-counted existing Leibniz/class-substitution route. The source has arbitrary class operands; equality and class substitution need their displayed interpretation before this becomes a full-signature certificate.")
   "ax-frege54c" '("Y(refl) for represented sets; T;G after class-equality lowering (conditional)" "refl for set-variable instance" "SAx for represented sets; STaut;SGen after class lowering" "Order-counted existing reflexivity route. For arbitrary classes, interpret equality as pointwise membership equivalence and generalize its reflexive tautology; this interpretation is not inserted into the registry by this classification.")
   "ax-frege58b" '("V;Y;Z;T;H" "refl" "SInst;SAx;SLeib;STaut;SAlli" "Specialize forall x ph; capture-avoiding source substitution expansion may then require its equality-guard equivalence rather than direct variable replacement.")))

(define (cols row) (string-split row "\t" #:trim? #f))
(define rows (map cols (cdr (file->lines "LOGIC-ROUTES.tsv"))))
(unless (= (length rows) 85) (error 'routes "Expected 85 source logic rows"))
(define order-count 0)
(define full-count 0)
(call-with-output-file "ROUTES-2.tsv"
  (lambda (out)
    (displayln "label\tcovered_by_order\tfull_signature_covered\tjudge_step_kinds\tjudge_ax_shapes\tkernel_constructors\tsource_kernel_route\trouting_basis\ttranslation_boundary\toperator_signature\tsource_statement\tsource_mandatory_variables\tsource_disjoint_pairs\tessential_hypotheses" out)
    (for ([row (in-list rows)])
      (define label (car row))
      (define miss? (member label missing))
      (define cond? (member label conditional))
      (define def? (string-prefix? label "df-"))
      (define order? (not miss?))
      (define full? (and order? (not cond?)))
      (when order? (set! order-count (add1 order-count)))
      (when full? (set! full-count (add1 full-count)))
      (define info
        (cond
          [miss? (list "none" "" "none" "No provability interpretation or rule is supplied. A syntactic first-order abbreviation cannot assert the source modal rule/schema.")]
          [def? (list "T" "" "STaut" "Expand the source logical operator to the displayed formula using capture-avoiding translation. The source defining assertion becomes a propositional tautology over the expanded subformulas.")]
          [(hash-has-key? routes label) (hash-ref routes label)]
          [(string-contains? (list-ref row 4) "STaut")
           (list "T (also Y k/s/c for ax-1/2/3)" (if (member label '("ax-1" "ax-2" "ax-3")) "k/s/c respectively" "") "STaut" "The expanded source axiom is a propositional tautology; the original exact integer truth-table receipt has zero false assignments.")]
          [else (error 'routes "No classification for ~a" label)]))
      (define boundary
        (cond
          [miss? "Missing asserted provability rule/schema; full source ph operands preserved."]
          [cond? "Class lowering is conditional. Set-variable specialization proves a smaller-domain instance. This row does not add a full class interpretation. Existing class-equality, class-membership, or class-substitution dependencies remain subject to the coverage test."]
          [def? (string-append "Typed syntactic expansion, not a fixed set-predicate arity. Retain arbitrary finite free-variable support, binder names, source freshness/disjoint conditions, and source essential hypotheses. Class operand subformulas remain parameterized membership/equality formulas until supplied by their own routes. Expansion: " (list-ref row 3))]
          [else "First-order schema route with source substitutions, free parameters, and all distinct-variable conditions retained. Multiple kind names describe a derivation route; this row alone is not a judge verdict."]))
      (displayln
       (string-join
        (append (list label (if order? "1" "0") (if full? "1" "0"))
                (take info 3)
                (list (list-ref row 4) (list-ref info 3) boundary
                      (list-ref row 2) (list-ref row 5) (list-ref row 6)
                      (list-ref row 7) (list-ref row 8))) "\t") out)))
  #:exists 'error)
(unless (and (= order-count 82) (= full-count 80))
  (error 'routes "Unexpected totals ~a ~a" order-count full-count))
(printf "rows=~a covered_by_order=~a full_signature_covered=~a conditional=~a missing=~a\n"
        (length rows) order-count full-count (length conditional) (length missing))
