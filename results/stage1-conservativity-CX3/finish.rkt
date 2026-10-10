#lang racket/base
(require racket/file racket/list racket/path racket/port racket/string racket/system file/sha1)

(define lane (path->complete-path (or (current-load-relative-directory) (current-directory))))
(define general "C:/ClaudeOutput/pompetzki/forcing-src/general")
(define judge-link "C:/ClaudeOutput/pompetzki/forcing-src/codex-judge-link-20261009")
(define date-exe "C:/Program Files/Git/usr/bin/date.exe")
(define (date-text)
  (string-trim (with-output-to-string
    (lambda () (unless (system* date-exe "+%Y-%m-%dT%H:%M:%S%:z") (error 'date "failed"))))))
(define (sha256 path)
  (call-with-input-file path (lambda (in) (bytes->hex-string (sha256-bytes in)))))
(define (new-file name text)
  (call-with-output-file (build-path lane name) #:exists 'error (lambda (out) (display text out))))
(for ([name '("RESULTS.md" "STATUS.txt" "SOURCE-HASHES.txt" "MANIFEST.sha256")])
  (when (file-exists? (build-path lane name)) (error 'new-files-only "already exists: ~a" name)))
(define modules '("Conservativity2" "Stage2Conservativity2"))
(define validation-rows
  (for/list ([module-name modules])
    (define (receipt mode) (file->string (build-path lane (format "~a.~a1.receipt.txt" module-name mode))))
    (define c (receipt "compile"))
    (define k (receipt "check"))
    (unless (and (regexp-match? #px"exit-code: 0\\s*$" c)
                 (regexp-match? #px"exit-code: 0\\s*$" k)
                 (string-contains? (file->string (build-path lane (format "~a.check1.txt" module-name))) "Axioms: <none>"))
      (error 'validation "compiler/kernel receipt failed: ~a" module-name))
    (define (seconds s) (cadr (regexp-match #px"elapsed-whole-seconds: ([0-9]+)" s)))
    (format "| `~a` | 0 | ~a | 0 | ~a | `<none>` |\n" module-name (seconds c) (seconds k))))
(define coverage (file->string (build-path lane "stage2-coverage-receipt.txt")))
(unless (and (string-contains? coverage "Totals: 1656 theorems; 53069 steps;")
             (string-contains? coverage "Historical receipts: 7 both-judge ACCEPT rows and 70 both-judge REJECT mutant rows."))
  (error 'validation "Stage 2 coverage receipt differs"))

(define dependencies '("Syn" "Prov" "Kal" "Val" "Inv" "Parse" "Data" "Checks" "Ax" "Use"
                       "Expand" "Pure" "Elim" "Sub" "Replay" "ReplayT" "Replay2" "Replay3" "RpInit" "RpInitOk"))
(define source-paths
  (append
   (list "C:/ClaudeOutput/pompetzki/lanes/CODEX-ORDERS-2026-10-09.md"
         "C:/ClaudeOutput/abschluss/docs/RELEASE-DAY-ORDERS-2026-10-09.md")
   (for*/list ([name dependencies] [ext '(".v" ".vo")]) (build-path general (string-append name ext)))
   (for/list ([ext '(".v" ".vo")]) (build-path judge-link (string-append "JudgeBatch" ext)))))
(new-file "SOURCE-HASHES.txt"
  (string-append "CX3 imported project sources and compiled dependencies. SHA256.\n"
                 (apply string-append
                   (for/list ([path source-paths]) (format "~a  ~a\n" (sha256 path) path)))))
(define completed (date-text))
(define payload-files
  (sort (filter file-exists? (directory-list lane #:build? #t)) string<? #:key path->string))
(define file-table
  (apply string-append
    (for/list ([path payload-files])
      (format "| `~a` | ~a | `~a` |\n" (file-name-from-path path) (file-size path) (sha256 path)))))
(new-file "RESULTS.md"
  (string-append
    "# CX3: definitions are conservative\n\n"
    "Completed at " completed " (Git date.exe). Execution host verified by Win32_ComputerSystem: THEBIGMAGILLA, Alienware Area-51 AAT2265. Filesystem drives C:, G:, and Temp were listed; the lane directory is an ordinary directory with no link target. Authoritative deliverables are in C:\\ClaudeOutput\\pompetzki\\lanes\\CX3\\.\n\n"
    "The final proof sources are `Conservativity2.v` and `Stage2Conservativity2.v`, imported under logical prefix `CX3`. They contain 27 named lemmas/theorems/corollaries. Both compiled with Rocq 9.1.0 and passed recursive coqchk (no `-norec`). Both kernel summaries print `Axioms: <none>`. The compiler printed 23 requested assumption summaries, all `Closed under the global context`. No new Axiom, Parameter, Admitted, or admit occurs in either final source. The coqchk summaries also report no type-in-type dependencies, unsafe fixpoints, or assumed positivity.\n\n"
    "## General conservativity\n\n"
    "The requested theorem is proved with its original conclusion, for every pure formula including formulas with free variables:\n\n"
    "```coq\nTheorem gam_pure_conservative (f : form) :\n  syms f = [] -> prov Gam f -> prov ZFpure f.\n\nTheorem pure_provability_iff (f : form) :\n  syms f = [] -> (prov Gam f <-> prov ZFpure f).\n\nTheorem elim_all_pure (L : list (nat * nat * form)) (f : form) :\n  okb [] L = true -> syms f = [] ->\n  prov (GamL L) f -> prov ZFsym f.\n```\n\n"
    "`psub_pure_fixed` derives invariance of a pure formula under every predicate substitution from Syn.psub_none. `elim_all_pure` uses reverse induction on the definition list and the existing Elim.elim_step. For the registered theory it uses the existing proved finite check Elim.okb_Dall. `zfsym_top_substitution` applies Use.prov_psub_to to every remaining axiom, producing a pure Separation or Collection instance; `zfsym_pure_formula` retains the original pure conclusion. Reverse inclusion follows because every ZFpure axiom is a Gam axiom. There is no closedness, depth, memory, consistency, or oracle premise on this theorem.\n\n"
    "The other general statements are:\n\n"
    "```coq\nTheorem expanded_theorem_pure T f :\n  Good T -> syms (expD Pr T f) = [] ->\n  prov Gam f -> prov ZFpure (expD Pr T f).\n\nTheorem registered_expansion_pure ds f :\n  (forall d, In d ds -> In d Dall) ->\n  syms (expD Pr (buildT Pr [] ds) f) = [] ->\n  prov Gam f -> prov ZFpure (expD Pr (buildT Pr [] ds) f).\n\nCorollary all_registered_expansion_pure f :\n  syms (expD Pr (buildT Pr [] Dall) f) = [] ->\n  prov Gam f -> prov ZFpure (expD Pr (buildT Pr [] Dall) f).\n```\n\n"
    "Expansion uses the existing proved equivalence Expand.repl and modus ponens before applying conservativity. Its fallback is Pr, retaining uncovered predicates.\n\n"
    "## Stage 2 composition\n\n"
    "`Stage2Conservativity2.v` imports the main framework's JudgeLink.JudgeBatch.accepted_member_sound. It proves the 677-entry Stage 2 registry sound by taking AX0 ++ DEF0 as the left prefix of the proved RpInitOk.REG0. It removes AH [] through prov_mono and composes replay soundness, faithful expansion, and conservativity.\n\n"
    "The eleven definitions in registration order are Sub2, Sng2, Upr3, Opr3, App3, Fnc1, Emp1, Suc2, Ind1, Om1, Nat1 (symbol IDs 5, 6, 7, 8, 9, 10, 17, 18, 19, 20, 72). `stage2_table_good` proves the expansion equivalent in Gam, and `stage2_table_pure_check` kernel-checks that all eleven fully expanded bodies are pure. `covered` checks that every predicate has a table entry and the correct arity. Structural induction then proves purity for every covered formula.\n\n"
    "```coq\nTheorem stage2_theorem_pure f :\n  covered stage2_table f = true ->\n  prov Gam f -> prov ZFpure (stage2_expand f).\n\nTheorem stage2_accepted_member_pure ts t :\n  check_batch stage2_registry ts = true ->\n  In t ts -> t_hyps t = [] ->\n  covered stage2_table (tof (t_stmt t)) = true ->\n  prov ZFpure (stage2_expand (tof (t_stmt t))).\n```\n\n"
    "A general `accepted_expanded_member_pure` additionally supports any sound registry and Good table whose expanded statement is pure. All premises shown are arguments of the proved theorem; they are not global axioms.\n\n"
    "`stage2-coverage2.rkt` completed with exit 0. It read the seven current sigma1/out JDG1 files using the existing sigma1.rkt readers, checked all seven registries entry for entry against RpInit.v, checked that all 1,656 theorem hypothesis lists are empty, and matched all current hashes to the existing manifest. The statements use exactly the predicate/arity pairs (6,2), (7,3), (8,3), (9,3), (10,1), (17,1), (18,2), (20,1), (72,1), within the expansion table's vocabulary.\n\n"
    "| Stage 2 file | Theorems | Steps | Copied prelude | Generated |\n|---|---:|---:|---:|---:|\n"
    "| 01-numerals.jdg | 73 | 1679 | 7 | 66 |\n| 02-membership.jdg | 226 | 4168 | 13 | 213 |\n| 03-distinct.jdg | 248 | 4076 | 10 | 238 |\n| 04-bounded.jdg | 90 | 1596 | 13 | 77 |\n| 05-arithmetic.jdg | 432 | 20508 | 24 | 408 |\n| 06-sentences.jdg | 364 | 13904 | 25 | 339 |\n| 07-sigma1.jdg | 223 | 7138 | 27 | 196 |\n| Total | 1656 | 53069 | 119 | 1537 |\n\n"
    "The existing sigma1/judge-run-1.txt has seven original files ACCEPT, exit 0, and seventy mutants REJECT, exit 1, from both judges. These are existing receipts; CX3 did not rerun the judges or create new JDG derivations. CX3 proves the implication from Replay2.check_batch acceptance. It does not assert a kernel computation of those seven complete batches or the pending native judge/check_batch simulation theorem assigned to the other proof lanes. The actual-file coverage check is a Racket receipt; the conservativity, table purity, registry soundness and abstract accepted-member implication are Rocq proofs.\n\n"
    "The original sigma1/RESULTS.md gives a 154 prelude / 1502 generated split. Current indices and manifest give 119 / 1537; total 1656 and total steps 53069 agree. This correction is written here and in the new coverage receipt.\n\n"
    "## Compiler and kernel receipts\n\n"
    "All durations are integer differences of epoch seconds read from date.exe. Exact commands, start/end times and exits are in the companion `.receipt.txt` files.\n\n"
    "| Module | coqc exit | coqc seconds | recursive coqchk exit | coqchk seconds | Axioms |\n|---|---:|---:|---:|---:|---|\n"
    (apply string-append validation-rows) "\n"
    "The first `Conservativity.v` compilation failed at line 69 because an extra bracket in the conjunction pattern requested a disjunction. `Conservativity2.v` corrects the pattern. The first `Stage2Conservativity.v` compilation failed at line 23 when buildT_good did not infer the table through its evaluated literal. `Stage2Conservativity2.v` provides the explicit convertible buildT goal. The first coverage script failed on file-name-from-path; `stage2-coverage2.rkt` imports racket/path. The initial sources and their failure receipts are present beside the corrections.\n\n"
    "For reproducible new-file builds, copy the two final Rocq sources and run-rocq.rkt to a new empty local directory, then run the runner sequentially with `compile Conservativity2 1`, `compile Stage2Conservativity2 1`, and `check Stage2Conservativity2 1`. The runner creates logs exclusively and rejects recompiling an existing .vo. Its mappings import the original Cohen library and JudgeLink framework without writing to those directories. Run the coverage script with a new receipt path.\n\n"
    "## File hashes\n\n"
    "SHA256 hashes below cover every payload file present before this report was created, including preserved attempts and generated Rocq artifacts. SOURCE-HASHES.txt records the original project-source and dependency .vo hashes. MANIFEST.sha256 additionally covers RESULTS.md and STATUS.txt, excluding its own self-hash.\n\n"
    "| File | Bytes | SHA256 |\n|---|---:|---|\n" file-table))
(new-file "STATUS.txt"
  (string-append
    "CX3 complete at " completed " (date.exe), C:\\ClaudeOutput\\pompetzki\\lanes\\CX3\\: Conservativity2.v proves syms f = [] -> prov Gam f -> prov ZFpure f for all formulas, and the reverse inclusion gives equivalence on pure formulas. Stage2Conservativity2.v proves faithful pure expansion for the eleven Stage 2 definitions, the 677-entry registry's soundness, and the pure-ZF conclusion for every covered hypothesis-free member of an abstract accepted batch. Both modules compile exit 0 and pass recursive coqchk exit 0 with Axioms: <none>; 27 named results, 23 printed closed-context summaries. The current seven Stage 2 files contain 1656 statements and 53069 steps, all empty hypothesis lists and the nine covered predicate/arity pairs; hashes match the existing manifest. Existing both-judge receipts show 7 ACCEPT originals and 70 REJECT mutants. The native judge simulation and kernel evaluation of complete concrete batches are not asserted by these CX3 results. RESULTS.md, SOURCE-HASHES.txt and MANIFEST.sha256 provide statements, receipts and hashes.\n"))
(define all-files (sort (filter file-exists? (directory-list lane #:build? #t)) string<? #:key path->string))
(new-file "MANIFEST.sha256"
  (apply string-append
    (for/list ([path all-files]) (format "~a  ~a\n" (sha256 path) (file-name-from-path path)))))
(printf "CX3 report completed at ~a; manifest entries ~a\n" completed (length all-files))
