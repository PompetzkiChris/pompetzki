#lang racket/base
;; Final reports and SHA256 snapshots; creation-only output.
(require racket/file racket/list racket/string racket/path file/sha1
         (prefix-in reg: "registry-reader-v3.rkt"))
(define args (current-command-line-arguments))
(unless (= (vector-length args) 1) (error 'report "pass the Get-Date ISO timestamp"))
(define stamp (vector-ref args 0))
(define lane "C:\\ClaudeOutput\\pompetzki\\lanes\\AG12-setmm-registry\\")
(for ([f '("MAP.tsv" "COVERAGE.tsv" "VERIFY-FINAL.tsv" "SET-EXTENSION-PROTOTYPES.tsv" "EXTENSION-VERIFY.tsv")])
  (unless (file-exists? f) (error 'report "required output absent:~a" f)))
(define (digest-record path [label (path->string (if (path? path) path (string->path path)))])
  (define data (file->bytes path))
  (list label (bytes-length data) (string-upcase (bytes->hex-string (sha256-bytes data)))
        (file-or-directory-modify-seconds path)))
(define inputs
  (sort (remove-duplicates
    (append reg:source-paths
      (list "C:/ClaudeOutput/pompetzki/lanes/RULES-ROUND2-2026-10-09.md"
            "C:/ClaudeOutput/formalization-toolchain-20260924/libraries/metamath-set-mm-28167ed89a49/set.mm"
            "C:/ClaudeOutput/pompetzki/lanes/AG8/setmm_queue.tsv"
            "C:/ClaudeOutput/pompetzki/lanes/AG8/setmm_priority.rkt"
            "C:/ClaudeOutput/pompetzki/lanes/AG8/RESULTS.md"
            "C:/ClaudeOutput/pompetzki/lanes/AG8/summary_counts.tsv"
            "C:/ClaudeOutput/pompetzki/lanes/L5/mm3.rkt"
            "C:/ClaudeOutput/pompetzki/lanes/L5/mm2jdg7.rkt"
            "C:/ClaudeOutput/pompetzki/forcing-src/general/Prov.v"))) string<?))
(define input-records (map digest-record inputs))
(define (tsv-row out row) (displayln (string-join (map (lambda (x) (format "~a" x)) row) "\t") out))
(call-with-output-file "SOURCE-SHA256.tsv" #:exists 'error
  (lambda (out)
    (tsv-row out '("path" "bytes" "sha256" "mtime_epoch_seconds"))
    (for ([r input-records]) (tsv-row out r))))
(call-with-output-file "STATUS.txt" #:exists 'error
  (lambda (out)
    (fprintf out "~a COMPLETE. ORDER.md executed in ~a with new files only. MAP.tsv has 167 labels (80 axioms, 87 definitions), 8 numbered axiom counterparts (2 alpha matches, 6 named equivalences), 159 full-signature no-counterpart rows with exact typed extension formulas/arities, and 10 qualified set-specialization candidates. COVERAGE.tsv has 5757 ordered cohort rows; 22 are covered by the literal numbered-registry criterion (18 provable assertions, 4 syntax assertions), all with empty axiom/definition dependencies. Exact compressed-proof dependencies reproduce all 5757 AG8 rows with 0 differences. REGISTRY.tsv validates 677 entries; 11 set-only first-order prototypes and 84 propositional assignments passed. RESULTS.md and SHA256.tsv give the counts, qualification boundaries, provenance, and checksum snapshots. No JDG1 acceptance claim is made.\n" stamp lane)))
(define artifact-paths
  (sort (filter file-exists? (directory-list)) string<? #:key path->string))
(define artifact-records (for/list ([p artifact-paths]) (digest-record p)))
(define metric-rows
  '(("set.mm assertions" 50912)
    ("AG8 class-free cohort" 5757)
    ("Actual decoded class-free assertions" 5757)
    ("Provable assertions in the cohort (|- type)" 5753)
    ("Syntax assertions in the cohort (wff type)" 4)
    ("Cohort dependency-list differences" 0)
    ("Unused compressed-proof assertion table entries" 0)
    ("Relevant ax-* labels" 80)
    ("Relevant df-* labels" 87)
    ("Total MAP rows" 167)
    ("Numbered registry counterparts" 8)
    ("Identical up to renaming and universal closure" 2)
    ("Equivalent by named derivation" 6)
    ("No counterpart for the full source signature" 159)
    ("Axiom/rule labels without a numbered counterpart" 72)
    ("Definition labels without a full-signature numbered counterpart" 87)
    ("Qualified set-specialization candidates" 10)
    ("Registry-only covered cohort rows" 22)
    ("Covered provable assertions" 18)
    ("Covered syntax assertions" 4)
    ("Covered rows with empty dependencies" 22)
    ("Registry-only uncovered cohort rows" 5735)
    ("First 1000 registry-only covered rows" 2)
    ("AX0 axioms" 7)
    ("DEF0 definitions" 670)
    ("Registry entries" 677)
    ("Symbol-table symbols" 686)
    ("Direct source/registry structural checks" 3)
    ("Typed source-extension formulas" 167)
    ("Definition right-hand sides extracted" 87)
    ("Logical analysis rows" 85)
    ("Logical axiom/rule analysis rows" 44)
    ("Logical definition analysis rows" 41)
    ("Propositional axiom truth tables" 15)
    ("Exact integer Boolean assignments" 84)
    ("False assignments" 0)
    ("Extension source-formula equality checks" 167)
    ("Typed definition RHS/LHS roundtrips" 87)
    ("Outer equation reconstructions" 86)
    ("Primitive biconditional expansion assignments" 8)
    ("First-order set-definition prototypes" 11)
    ("Verified named set derivation source assertions" 11)))
(define covered-labels
  '("idi" "a1ii" "weq" "pm11.07" "wel" "conventions" "conventions-labels" "conventions-comments"
    "natded" "dummylink" "mathbox" "bj-0" "wl-section-prop" "wl-section-boot" "wl-section-impchain"
    "wl-impchain-com-1.1" "iddii" "sn-wcdeq" "idiALT" "iin1" "iin2" "iin3"))
(call-with-output-file "RESULTS.md" #:exists 'error
  (lambda (out)
    (fprintf out "# AG12 set.mm registry mapping\n\nCompleted: ~a, obtained from Get-Date.\n\n" stamp)
    (fprintf out "The authoritative output directory is `~a`. Execution host was verified as THEBIGMAGILLA, Alienware Area-51 AAT2265. The observed filesystem drives were C:, G:, and Temp. The lane directory was an ordinary directory with no link target. All program and artifact writes were confined to this existing lane directory, with creation-only file operations. Inputs outside the lane were read-only.\n\n" lane)
    (display "MAP.tsv maps every ax-* and df-* label used by the specified AG8 cohort. It contains exact source statements, mandatory variables and their types, essential hypotheses, disjoint-variable constraints, registry indices/names and printed formulas, match classes, named derivations, typed new-symbol definitions, and separate qualified set-specialization candidates. COVERAGE.tsv contains every cohort assertion in set.mm order and its required labels, missing labels, and registry-only coverage flag.\n\n" out)
    (display "| Metric | Exact count |\n|---|---:|\n" out)
    (for ([r metric-rows]) (fprintf out "| ~a | ~a |\n" (car r) (cadr r)))
    (fprintf out "| Read-only input checksum rows | ~a |\n| Existing and generated artifact checksum rows before RESULTS.md | ~a |\n\n" (length input-records) (length artifact-records))
    (display "The numbered matches are ax-ext ->0 Ext, ax-pr ->1 Pair, ax-un ->2 Union, ax-pow ->3 Power, ax-inf2 and ax-inf ->4 Inf, ax-reg ->5 Found, and ax-ac ->6 Choice. Ext and Power match after universal closure and alpha conversion. Pair uses equality substitution and specialization; Union uses existential-antecedent conversion; Foundation uses quantifier negation; Inf2 uses conjunction commutation. The alternate Infinity and Choice formulations use named ZF equivalences relative to the other ZF axioms and the stated schemas, including Foundation. The named top-level derivations delegate to established source proofs. The Infinity witnesses are axinf and axinf2. Choice equivalence is recorded directly by dfac0 and dfac5, with ac8 and axac describing the alternate forms. SET-DERIVATION-SOURCES.md retains the actual source assertions, source line numbers, and compressed-proof reference tables. No bound on the fully expanded length of those two ZF conversions is asserted.\n\n" out)
    (display "The strict coverage count uses the numbered AX0 ++ DEF0 registry alone. Its22 covered rows all have empty axiom/definition dependencies. Their labels, in source order, are:\n\n" out)
    (display (string-append "`" (string-join covered-labels "`, `") "`.\n\n") out)
    (display "The cohort includes 4 wff syntax assertions; all 4 occur in that covered list. Thus 18 of the 22 covered rows are |- assertions. Logical proof constructors and syntax expansions explain why a theorem may be translatable despite failing this literal registry-only dependency criterion. The first 1000 source theorems use ax-mp, ax-1, ax-2, ax-3, df-bi, df-an, and df-or; their proof rules and connective expansions are documented separately from the numbered registry. This report records dependency coverage, rather than judge-accepted translations.\n\n" out)
    (display "The source class variables have their full class signatures. A class-abstraction-free proof may still use proper classes, primitive class constants, and class-valued operations. The ten qualified candidates require set representatives or additional hypotheses; they do not increase full-signature coverage. They are df-ss, df-br, df-tr, df-ord, df-cleq, df-fun, df-fn, df-f, df-f1, and df-isom. For example, Sub2 matches subset for represented sets. Fnc1 alone permits nonpair members and therefore needs graphhood for the source function definition. SqD2 and Sq3 also impose a natural-number domain. The qualification formulas and counterexamples appear in SET-MATCH-ANALYSIS.md and SET-CANDIDATES.tsv.\n\n" out)
    (display "EXTENSION-FORMULAS-v2.tsv supplies all 167 exact source formulas, typed mandatory signatures, operator operands, binder names, dummy variables, and explicit new-symbol defining formulas. MAP.tsv includes those columns directly, so all 159 no-counterpart rows have the requested formula and arity information. For class-valued definitions the exact extension is a membership schema with a fresh set element argument. Formula operands and arbitrary class operands require capture-avoiding formula translation with their free parameters; they are not fixed arguments ranging over sets. The arity columns therefore distinguish typed schema arity from fixed set-predicate arity. Where the full source signature has no fixed first-order predicate arity, the table states that fact and gives the set-restricted arity or instance-based translation boundary.\n\n" out)
    (display "An axiom or inference rule cannot be supplied by a conservative definition alone. For those rows the exact source assertion, premises, and constraints are retained; the displayed predicate alias names the assertion body and does not assert it. Missing mathematical axioms require a derivation or an asserted extension. The source Prv operator needs an explicit provability interpretation or modal syntax/rules. The complex-number and Hilbert-space primitives need their own fixed interpretations and derivations. These are mathematical signature boundaries, rather than omitted formulas.\n\n" out)
    (display "SET-EXTENSION-PROTOTYPES.tsv gives 11 exact closed first-order definitions for represented sets, with hypothetical new symbol IDs 686 through 696: Rel1, Fun1, Fn2, Map3, Inject3, Onto3, Bijection3, RelPres5, Isom5, DomExact2, and Er2. Every row includes arity, source label, scope, named defining formula, and de Bruijn formula. All 11 passed closure, declared-arity, named-prefix and dform roundtrips, and body-scoping checks. They retain graphhood, exact domains, exact ranges, and the source relation arguments. No registry was modified.\n\n" out)
    (display "The independent compressed-proof pass decoded actual label uses for all source proofs and reproduced 5757 class-free assertions, with 0 queue dependency differences and 0 unused assertion references in compressed tables. All 677 registry formulas were checked against their named Data.v/lib sources, declared predicate arities, closure, and printing roundtrips. Additional structural checks independently parsed the source Ext, Power, and Inf2 formulas. Fifteen propositional axiom formulas passed 84 exhaustive exact integer 0/1 assignments with 0 false results. VERIFY-FINAL.tsv checks map/source/extension label equality, all 159 missing-formula/arity records, all 8 numbered references, and every coverage row and its order. EXTENSION-VERIFY.tsv records 167 source-formula equalities, 87 typed RHS/LHS parse roundtrips, 86 exact outer-equation reconstructions, and 8 integer Boolean checks of the primitive df-bi expansion. Overlapping wi and bj-0 syntax trees were handled by choosing a complete typed parse for existence and exact token roundtrip; no uniqueness claim is made. All result decisions use exact integers or syntactic equality. No JDG1 file was generated, so the two-judge rule produced no acceptance claim.\n\n" out)
    (display "The working scripts create new files only. inventory.rkt, inventory-v2.rkt, and inventory-v3.rkt stopped at the AG8 footer; inventory-v4.rkt handles its comment/footer rows. make-map-v2.rkt corrects a local binding in the first map script. Registry-reader correction versions, extension-table versions, and verification variants are preserved alongside their completed versions. Programs use the full Racket executable path and single-process substantive jobs, bounded to at most 4 active workers. This run finished before the 20-minute periodic-status interval and before the required delivery deadline. STATUS.txt is the final paragraph.\n\n" out)
    (display "The checksums below cover bytes captured at finalization. SHA256.tsv includes the actual RESULTS.md and STATUS.txt checksums and every other file present at that snapshot except SHA256.tsv itself. Its own checksum is printed by the reporting program and supplied with the final handover. The launcher-owned codex-run.log is a changing log; its checksum and byte count identify the captured snapshot. SOURCE-SHA256.tsv records all decision-source inputs and their filesystem modification times.\n\n" out)
    (display "| Artifact | Bytes captured | SHA256 |\n|---|---:|---|\n" out)
    (for ([r artifact-records]) (fprintf out "| ~a | ~a | `~a` |\n" (car r) (cadr r) (caddr r)))
    (display "| RESULTS.md | Recorded in SHA256.tsv | Actual digest in SHA256.tsv |\n| SHA256.tsv | Reported at completion | Detached digest in final handover |\n\n" out)
    (display "| Read-only input | Bytes captured | SHA256 |\n|---|---:|---|\n" out)
    (for ([r input-records]) (fprintf out "| ~a | ~a | `~a` |\n" (car r) (cadr r) (caddr r)))))
(define result-record (digest-record "RESULTS.md"))
(call-with-output-file "SHA256.tsv" #:exists 'error
  (lambda (out)
    (tsv-row out '("file" "bytes" "sha256" "mtime_epoch_seconds"))
    (for ([r (sort (cons result-record artifact-records) string<? #:key car)]) (tsv-row out r))))
(define manifest-record (digest-record "SHA256.tsv"))
(printf "RESULTS.md SHA256 ~a\nSTATUS.txt SHA256 ~a\nSHA256.tsv SHA256 ~a\nARTIFACT_HASH_ROWS ~a\nINPUT_HASH_ROWS ~a\n"
        (caddr result-record) (caddr (findf (lambda (r) (equal? (car r) "STATUS.txt")) artifact-records))
        (caddr manifest-record) (add1 (length artifact-records)) (length input-records))
