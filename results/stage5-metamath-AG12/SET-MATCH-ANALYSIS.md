# Set and class correspondence analysis

This file compares the full typed statements in SOURCE-LABELS.tsv with the literal formulas in REGISTRY.tsv. The registry has 677 entries: indices 0 through 6 are fixed set axioms, and indices 7 through 676 are closed definitions with set-valued arguments. Source class variables range over classes; deleting class-abstraction syntax from a theorem does not turn its class variables into set variables.

Use two separate columns in MAP.tsv: `full_signature_match` and `qualified_candidate`. A qualified candidate does not increase unconditional full-signature coverage. A named derivation records a mathematical correspondence; it is not a JDG1 certificate.

## Fixed set axioms

In this table a free source set variable is universally closed before comparing the source formula with a closed registry entry. Registry specialization recovers the original free-variable statement.

| Source | Entry | Formula correspondence | Required derivation |
|---|---|---|---|
| ax-ext | 0 Ext | `forall x y. ((forall z. (z in x <-> z in y)) -> x=y)` | Identical after universal closure and bound-variable renaming. |
| ax-pow | 3 Power | `forall x. exists y. forall z. ((forall w. (w in z -> w in x)) -> z in y)` | Identical after universal closure and bound-variable renaming. |
| ax-pr | 1 Pair | Source: `exists z. forall w. ((w=x or w=y) -> w in z)`. Target: `exists z. (x in z and y in z)`. | Equality substitution proves target implies source. Instantiate the source universal quantifier at x and y for the converse. |
| ax-un | 2 Union | Source: `exists y. forall z. ((exists w. (z in w and w in x)) -> z in y)`. Target: `exists y. forall w z. ((z in w and w in x) -> z in y)`. | Move the existential quantifier out of the antecedent, then commute universal quantifiers; y is the same witness. |
| ax-reg | 5 Found | Source witness y: `y in x and forall z. (z in y -> not z in x)`. Target witness y: `y in x and not exists z. (z in x and z in y)`. | Quantifier negation and conjunction commutation. |
| ax-inf2 | 4 Inf | Both assert a set containing an empty set and closed under exact successors. | Bound-variable renaming and conjunction commutation in both existential witnesses. |

`ax-inf` is the alternate Infinity axiom `forall x. exists y. (x in y and forall z in y. exists w in y. z in w)`. It has entry 4 as a ZF-equivalent Infinity counterpart, with dependencies stated. The source supplies named derivations `axinf` and `axinf2`. `axinf` derives the alternate form from standard Infinity using `omex` and `inf0`; `inf0` builds the successor iterates of x by recursion and takes their range. The opposite derivation `axinf2` uses Regularity, with its intermediate `inf2` and `inf3` results. Therefore the match is a named mathematical equivalence relative to the remaining ZF axioms, including Found 5; it is not a variable-renaming match or a fixed-length propositional conversion. Source locations: set.mm lines 102338 onward, 102649-102660, 102684 onward, and 102753-102759.

`ax-ac` has entry 6 Choice as its ZF-equivalent Choice counterpart, with dependencies stated. Entry 6 is the disjoint nonempty family formulation: a set meets each member of a pairwise disjoint family in exactly one element. The source theorem `dfac5` is precisely this formulation after expanding nonemptiness, intersection, restricted quantification, and unique existence. The source `ac8` derives it from Choice. The source `axac` gives the reverse conversion from the standard `ax-ac2` formulation to the alternate encoded formula used by `ax-ac`; that direction uses Regularity. Thus the source ax-ac and entry 6 are equivalent relative to the remaining ZF axioms, including Found 5. This is a named mathematical derivation rather than a syntactic equality. Source locations: set.mm 111913-111917, 117871-117881, 118029-118032, and 118323-118327.

These two conversions should receive an explicit `named ZF derivation` qualifier if the requested three match classes force them into `equivalent by a short derivation`. The short top-level named source proofs delegate to longer established results. No claim that those dependency proofs have been replayed into JDG1 is made here.

## Set specializations of class definitions

The source definitions in this section have unrestricted class variables. Their full typed signatures have no direct registry counterpart. The entries below are qualified candidates for a translator that has established set representatives for the indicated class parameters.

| Source | Qualified candidate | Qualifications and formula conversion |
|---|---|---|
| df-ss | 7 Def:Sub2, arity 2 | A and B are represented sets. Both bodies are `forall x. (x in A -> x in B)`. |
| df-br | 11 Def:App3, arity 3 | R, A, and B are represented sets. The ordered pair uses the Kuratowski representation of entries 8-10. Both bodies are `exists p. (p in R and Opr3(p,A,B))`. Pair existence and extensional uniqueness justify replacing the ordered-pair term by its relational witness. |
| df-tr | 17 Def:Tr1, arity 1 | A is a represented set. Expand membership in union, then move its existential quantifier through the implication. Both bodies become `forall x y. ((x in y and y in A) -> x in A)`. The source theorem `dftr2`, lines 49575-49578, states this formula directly. |
| df-ord | 18 Def:Ord1, arity 1 | A is a represented set and Found 5 is available. The target is transitivity plus membership trichotomy. The source theorem `dford2`, lines 102309-102315, establishes precisely this alternate definition using ax-reg. Without Foundation, transitivity and trichotomy do not supply the source well-foundedness clause. |
| df-cleq | 0 Ext as an axiom consequence | A and B are represented sets. Ext supplies the forward extensional implication to equality; equality substitution supplies equality implies same members. No separate registry definition introduces the source class-equality operation. |
| df-fun | 12 Def:Fnc1, arity 1 | F is a represented set and `Rel F` has already been established. Source `dffun2`, lines 62713-62717, gives `Fun F <-> (Rel F and single-valued pair part)`. Under Rel F, the second conjunct is exactly Fnc1. |
| df-fn | 76 Def:SqD2, arity 2 | F and A are represented sets and Nat1(A) is established. The extra Nat1 conjunct in SqD2 prevents an unconditional correspondence for arbitrary domains. |
| df-f | 77 Def:Sq3, arity 3 | F, A, B are represented sets and Nat1(A) is established. Sq3 adds the range bound Rng2(F,B) to SqD2(F,A). |
| df-f1 | 152 Def:Ix3, arity 3 | F, A, B are represented sets and Dm2(F,A) is established. Dm2 supplies graphhood and prohibits pair inputs outside A. Ix3 alone supplies neither condition. |
| df-isom | 103 Def:Iso3, arity 3 | H, A, B are represented sets, R and S are both specialized to membership, and Rel(H) is established. Target Iso3 is a membership isomorphism, not an isomorphism of arbitrary R and S. |

There is no single target entry for the general signatures of df-fo, df-f1o, df-er, or df-relp. Their set specializations can be composed from existing predicates and additional exact formulas, as described below. They should not be assigned to an existing entry merely because part of a formula is present there.

## Function formulas and counterexamples to partial matches

The exact existing bodies used here are:

```
Fnc1(f) := forall x y z. ((App3(f,x,y) and App3(f,x,z)) -> y=z)
Inj1(f) := forall x y z. ((App3(f,x,z) and App3(f,y,z)) -> x=y)
Tot2(f,a) := forall x. (x in a -> exists y. App3(f,x,y))
Rng2(f,b) := forall x y. (App3(f,x,y) -> y in b)
Dm2(f,a) := forall p. (p in f -> exists x y. (x in a and Opr3(p,x,y)))
Cov3(b,f,a) := forall y. (y in b -> exists x. (x in a and App3(f,x,y)))
```

Their indices are 12, 13, 14, 15, 75, and 28 respectively. Dm2 is stronger than a predicate describing only the pair part: it requires every member of f to be a pair and every first coordinate to belong to a.

Define the following exact additional set predicates by the displayed bodies. Each displayed equivalence is universally closed over its arguments.

```
Rel1(f) <-> forall p. (p in f -> exists x y. Opr3(p,x,y))                 [arity 1]
Fun1(f) <-> (Rel1(f) and Fnc1(f))                                     [arity 1]
Fn2(f,a) <-> (Fnc1(f) and Tot2(f,a) and Dm2(f,a))                      [arity 2]
Map3(f,a,b) <-> (Fn2(f,a) and Rng2(f,b))                              [arity 3]
Inject3(f,a,b) <-> (Map3(f,a,b) and Inj1(f))                           [arity 3]
Onto3(f,a,b) <-> (Map3(f,a,b) and Cov3(b,f,a))                         [arity 3]
Bijection3(f,a,b) <-> (Inject3(f,a,b) and Cov3(b,f,a))                  [arity 3]
```

These formulas correspond to the set specializations of df-rel, df-fun, df-fn, df-f, df-f1, df-fo, and df-f1o. They introduce seven definitions, not seven existing registry entries. Dm2 gives the exact domain bound, Tot2 gives the opposite domain inclusion, Rng2 gives range inclusion, and Cov3 gives the opposite range inclusion. Ordered-pair injectivity identifies the same function graph with the source graph.

For a finite ZF counterexample to using Fnc1 as Fun, let f be the singleton containing the empty set. The empty set is not a Kuratowski ordered pair. Hence the pair part of f is empty, Fnc1(f) holds, and Rel1(f) fails. Consequently Fun(f) fails.

For a finite counterexample to using Ix3 as an exact injective mapping, take a=b=empty and f to be the same singleton. Fnc1, Inj1, Tot2, and Rng2 hold, so Ix3(f,a,b) holds; the source mapping requirement fails because f is not a relation. A second obstruction is an extra pair whose first coordinate lies outside a: Tot2 constrains inputs in a but does not remove additional inputs.

SqD2 and Sq3 avoid these graph obstructions through Dm2, but impose a natural-number domain. Nat1 is `exists w. (Om1(w) and n in w)`, index 74. Source Fn and mapping definitions impose no such domain constraint.

Iso3 requires Fnc1, Inj1, totality on its first carrier, a range bound, surjectivity onto its second carrier, a bound on all pair inputs, and preservation and reflection of membership. It still admits nonpair members of its graph argument. Adding Rel1(H) removes them. Its signature has three set arguments; the source Isom signature has H, R, S, A, B with five class arguments.

The general set relation-preservation and isomorphism definitions require these exact formulas, with arities 5:

```
RelPres5(h,r,s,a,b) <->
  (Map3(h,a,b) and
   forall x y u v.
     ((x in a and y in a and App3(h,x,u) and App3(h,y,v)) ->
       (App3(r,x,y) -> App3(s,u,v))))

Isom5(h,r,s,a,b) <->
  (Bijection3(h,a,b) and
   forall x y u v.
     ((x in a and y in a and App3(h,x,u) and App3(h,y,v)) ->
       (App3(r,x,y) <-> App3(s,u,v))))
```

For arbitrary class relations r and s, replace App3(r,x,y) and App3(s,u,v) by their class-membership formulas for the relevant ordered pairs; a set variable for r or s is not sufficient.

For df-er, an exact additional set predicate can be defined by:

```
DomExact2(r,a) <-> forall x. ((exists y. App3(r,x,y)) <-> x in a)       [arity 2]
Er2(r,a) <->
  (Rel1(r) and DomExact2(r,a) and
   forall x y. (App3(r,y,x) -> App3(r,x,y)) and
   forall x y z. ((App3(r,x,y) and App3(r,y,z)) -> App3(r,x,z)))        [arity 2]
```

The last two clauses expand the source converse and composition inclusion. Rel1 and DomExact2 retain the other two source conjuncts. Symmetry plus transitivity supplies reflexivity on the exact domain; no unsupported replacement by a membership-isomorphism predicate occurs.

## Other set axioms and mathematical consequences

`ax-nul` has no separate equivalent registry entry. It follows directly from the first conjunct of Inf 4 by existential elimination, conjunction elimination, and existential introduction. Def:Emp1 at index 19 defines emptiness; its formula is not an existence axiom.

`ax-sep` and `ax-rep` are formula schemes. Ax.v and Replay2.v provide Separation and Collection machinery separately from the 677 numbered entries. An occurrence of a scheme can use that machinery after formula translation, but it is not a match to a member of AX0 ++ DEF0.

`ax-regs` is a formula scheme over ph. The source theorem `axregs`, set.mm lines 577314-577318, derives it in ZF. Its source comment, lines 577080-577085, states that the derivation uses ax-inf2. Found 5 has one set argument and contains no formula slot. A generic arbitrary-ph scheme is therefore not the same registry formula. A bounded set-class specialization, ph(x) = x in a, reduces to Found 5 by equality substitution and quantifier conversion. Unbounded formula instances need the named class-Foundation derivation and its ZF dependencies; they cannot be licensed by treating their formula-defined class as a set.

`ax-tco` is `forall x. exists y. (x in y and Tr1(y))`. It has no equivalent fixed registry entry. The source theorem `axtco`, lines 602654-602662, derives it using ax-ext, ax-rep, and ax-inf2. Def:Tr1 17 supplies the property, not an existence axiom for transitive containers. This is an established mathematical consequence of the theory rather than a matching definition or a replacement for Infinity, Replacement, or Extensionality.

The source algebra axioms for CC, RR, scalar operations, and Hilbert-space operations have no counterpart with the same signatures among these 677 entries. Registry predicate arguments are set variables; the registry does not declare the source designated classes CC, RR, or ~H, nor the addition, multiplication, or Hilbert operations appearing in those source axioms. A later construction of these objects inside ZFC would supply new definitions and new derivations, not a literal correspondence to a present generic predicate.

## Coverage qualification

Full-signature coverage must use the full-signature decisions. Set-qualified candidates remain separately reviewable. A theorem can enter a second set-specialized coverage count only after its actual substitutions establish the candidate's required set representation, graphhood, domain condition, relation specialization, and Foundation dependency. The mere use of a source label in a class-abstraction-free theorem establishes none of those conditions.

The mathematical derivation names above establish available source correspondences and their boundaries. They do not establish that L5's translator can currently emit or that either judge has accepted the required proof files.
