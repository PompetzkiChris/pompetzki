#lang racket/base
(require racket/file racket/list racket/path racket/port racket/string racket/system json file/sha1)

(define lane "C:/ClaudeOutput/pompetzki/lanes/CX3")
(define concrete "C:/ClaudeOutput/pompetzki/lanes/CX3B")
(define package-root "C:/ClaudeOutput/pompetzki/lanes/CEO/executive-20261009-183208/package/release-final-1925")
(define executive "C:/ClaudeOutput/pompetzki/lanes/CEO/executive-20261009-183208")
(define date-exe "C:/Program Files/Git/usr/bin/date.exe")
(define (date-text) (string-trim (with-output-to-string
  (lambda () (unless (system* date-exe "+%Y-%m-%dT%H:%M:%S%:z") (error 'date "failed"))))))
(define started (date-text))
(define digest-cache (make-hash))
(define (digest path)
  (hash-ref! digest-cache (path->string (path->complete-path path))
    (lambda () (call-with-input-file path (lambda (in) (bytes->hex-string (sha256-bytes in)))))))
(define (text name) (file->string (build-path lane name)))
(define (new-file name content)
  (call-with-output-file (build-path lane name) #:exists 'error (lambda (out) (display content out))))
(define outputs '("INTEGRATION-RECOVERY-1.json" "INTEGRATION-RECOVERY-1.md"
                  "STATUS-INTEGRATION-1.txt" "INTEGRATION-RECOVERY-1.sha256"))
(for ([name outputs]) (when (file-exists? (build-path lane name)) (error 'new-files-only "exists: ~a" name)))
(define (manifest-table path)
  (for/hash ([line (file->lines path)] #:when (regexp-match? #px"^[0-9a-fA-F]{64}  " line))
    (define m (regexp-match #px"^([0-9a-fA-F]{64})  (.+)$" line))
    (values (caddr m) (string-downcase (cadr m)))))
(define original-manifest (manifest-table (build-path lane "MANIFEST.sha256")))
(for ([(name hash-value) (in-hash original-manifest)])
  (unless (equal? (digest (build-path lane name)) hash-value) (error 'preserved-CX3 "mismatch: ~a" name)))
(define original-dependencies (manifest-table (build-path lane "SOURCE-HASHES.txt")))
(for ([(path hash-value) (in-hash original-dependencies)])
  (unless (equal? (digest path) hash-value) (error 'preserved-dependency "mismatch: ~a" path)))
(define concrete-manifest (manifest-table (build-path concrete "MANIFEST.sha256")))
(define package-manifest (manifest-table (build-path package-root "MANIFEST.sha256")))
(define rows '())
(define (record role live packaged original-table original-name)
  (define live-hash (digest live))
  (when original-table
    (unless (equal? live-hash (hash-ref original-table original-name #f))
      (error 'original-snapshot "mismatch: ~a" live)))
  (when packaged
    (unless (equal? live-hash (digest (build-path package-root packaged)))
      (error 'package-copy "mismatch: ~a" packaged))
    (unless (equal? live-hash (hash-ref package-manifest packaged #f))
      (error 'package-manifest "mismatch: ~a" packaged)))
  (set! rows (cons (hash 'role role 'live_path (path->string (path->complete-path live))
                       'bytes (file-size live) 'sha256 live-hash
                       'package_relative_path (or packaged 'null)
                       'package_copy_and_manifest_match (if packaged #t 'null)) rows)))
(define (cx3 name packaged role)
  (record role (build-path lane name) packaged original-manifest name))
(for ([name '("Conservativity2" "Stage2Conservativity2")])
  (for ([ext '(".v" ".vo" ".compile1.txt" ".compile1.receipt.txt" ".check1.txt" ".check1.receipt.txt")])
    (define file (string-append name ext))
    (cx3 file (and (not (equal? ext ".vo")) (string-append "rocq/CX3/" file)) "CX3 proof/interface receipt"))
  (unless (regexp-match? #px"(?m:^exit-code: 0\\r?$)" (text (string-append name ".check1.receipt.txt")))
    (error 'CX3-receipt "exit differs: ~a" name))
  (unless (string-contains? (text (string-append name ".check1.txt")) "Axioms: <none>")
    (error 'CX3-receipt "context differs: ~a" name)))
(for ([name '("RESULTS.md" "STATUS.txt")]) (cx3 name (string-append "docs/lanes/CX3/" name) "original CX3 result"))
(for ([name '("SOURCE-HASHES.txt" "stage2-coverage-receipt.txt" "MANIFEST.sha256")])
  (record "CX3 dependency/coverage snapshot" (build-path lane name)
          (string-append "rocq/CX3/" name) #f #f))
(define (cx3b name packaged role)
  (record role (build-path concrete name) packaged concrete-manifest name))
(for ([name '("Stage2Bridge2" "Stage2RegistryCertificate2" "Stage2DataRegistry")])
  (cx3b (string-append name ".v") (string-append "rocq/CX3B/" name ".v") "concrete baseline dependency")
  (cx3b (string-append name ".vo") #f "preserved concrete proof object"))
(define baseline-files '("01-numerals" "02-membership" "03-distinct" "04-bounded" "05-arithmetic" "06-sentences" "07-sigma1"))
(define baseline-counts '((73 1679) (226 4168) (248 4076) (90 1596) (432 20508) (364 13904) (223 7138)))
(for ([number (in-range 1 8)] [stem baseline-files])
  (define nn (if (< number 10) (string-append "0" (number->string number)) (number->string number)))
  (define certificate (string-append "Stage2Certificate" nn "c"))
  (define data (string-append "Stage2Data" nn))
  (for ([module (list certificate data)])
    (cx3b (string-append module ".v") (string-append "rocq/CX3B/" module ".v") "concrete baseline module")
    (cx3b (string-append module ".vo") #f "preserved concrete proof object"))
  (for ([suffix '(".compile1.txt" ".compile1.receipt.txt" ".check1.txt" ".check1.receipt.txt")])
    (cx3b (string-append certificate suffix) (string-append "receipts/CX3B/" certificate suffix) "completed baseline receipt"))
  (define check-receipt (file->string (build-path concrete (string-append certificate ".check1.receipt.txt"))))
  (unless (and (regexp-match? #px"(?m:^exit-code: 0\\r?$)" check-receipt)
               (not (string-contains? check-receipt "-norec"))
               (string-contains? (file->string (build-path concrete (string-append certificate ".check1.txt"))) "Axioms: <none>"))
    (error 'concrete-receipt "context/exit differs: ~a" certificate))
  (record "original baseline JDG1 source"
          (build-path "C:/ClaudeOutput/pompetzki/sigma1/out" (string-append stem ".jdg"))
          (string-append "data/certificates/sigma1/out/" stem ".jdg") #f #f))
(for ([name '("SOURCE-HASHES.txt" "judges-round2.tsv" "convert-emission-verification.json")])
  (cx3b name (string-append "receipts/CX3B/" name) "concrete source/transcription/judge receipt"))
(for ([path '("CLAIMS.md" "VALIDATION-MATRIX.md")])
  (record "release claim map" (build-path package-root path) path #f #f))
(record "post-reboot ownership" (build-path lane "LIVE-OWNERSHIP-RECOVERY-1.json") #f #f #f)
(for ([name '("COO-STATUS-20261009-2005.md"
              "package/coo-recovery-20261009-200631/current-source-scan.txt"
              "package/receipts-release-final-1925/verify-manifest.txt")])
  (record "package ownership/integrity receipt" (build-path executive name) #f #f #f))
(define finished (date-text))
(define owners (call-with-input-file (build-path lane "LIVE-OWNERSHIP-RECOVERY-1.json") read-json))
(define ordered-rows (reverse rows))
(new-file "INTEGRATION-RECOVERY-1.json"
  (string-append (jsexpr->string
    (hash 'started_from_date started 'finished_from_date finished
          'host "THEBIGMAGILLA / Alienware Area-51 AAT2265" 'ownership owners
          'kernel_jobs_started 0 'compiler_jobs_started 0 'judge_jobs_started 0
          'original_CX3_manifest_entries_verified (hash-count original-manifest)
          'original_dependency_hashes_verified (hash-count original-dependencies)
          'checked_rows ordered-rows 'package_root package-root
          'baseline_theorems 1656 'baseline_steps 53069
          'native_implementation_theorem "unfinished; owned by Stage 1 / CX4"
          'public_theorems
          (list "CX3.Conservativity2.gam_pure_conservative"
                "CX3.Conservativity2.pure_provability_iff"
                "CX3.Stage2Conservativity2.accepted_member_Gam"
                "CX3.Stage2Conservativity2.accepted_expanded_member_pure"
                "CX3.Stage2Conservativity2.stage2_accepted_member_pure"
                "CX3B.Stage2RegistryCertificate2.reg0_677_correct"
                "CX3B.Stage2Bridge2.stage2_batch_certificate_registered"))) "\n"))
(define baseline-table
  (apply string-append (for/list ([number (in-range 1 8)] [stem baseline-files] [counts baseline-counts])
    (define nn (string-append "0" (number->string number)))
    (format "| ~a.jdg | ~a | ~a | `CX3B.Stage2Certificate~ac.batch~a_closed` |\n"
            stem (car counts) (cadr counts) nn nn))))
(new-file "INTEGRATION-RECOVERY-1.md"
  (string-append
    "# CX3 release integration after recovery\n\nStarted " started "; completed " finished ", both from date.exe. Verified execution host: THEBIGMAGILLA, Alienware Area-51 AAT2265; local lane directory has no link target.\n\n"
    "The original CX3 proofs retain their exact statements and proof-object hashes. " (number->string (hash-count original-manifest))
    " original lane manifest entries and " (number->string (hash-count original-dependencies))
    " original project/dependency hashes were verified. This integration started zero compiler, kernel-checker, or judge jobs. The preserved compiler and recursive coqchk receipts are reused. Both CX3 checks ended exit 0 with Axioms: <none>; all 23 requested assumption summaries were closed.\n\n"
    "## Live ownership and existing package integration\n\n"
    "The Stage 1 worker is 01a12227-bb71-7db2-a7f2-518a76ceba25 and the CX4 worker is 01a122ad-bc25-7f33-9dd5-c3da7da04c1f. Both were active in the compact app ownership snapshot saved in LIVE-OWNERSHIP-RECOVERY-1.json. They own the unfinished execution-to-check_batch composition. Package ownership is recorded in " executive "/COO-STATUS-20261009-2005.md.\n\n"
    "The assembled source package is " package-root ". Its CLAIMS.md cites CX3's conservativity and accepted-member APIs; VALIDATION-MATRIX.md rows 2c and 2d mark CX3 and the seven CX3B baseline certificates CLOSED. Every shipped source/receipt selected in the JSON snapshot matched both its live file and its outer package manifest entry. The source package already contains the pure-Gam wiring; this receipt supplies its exact qualified APIs and proof dependencies.\n\n"
    "## Exact interfaces for Stage 1 and CX4\n\n"
    "Logical mappings for the completed logical bridge are:\n\n```text\n-Q C:/ClaudeOutput/pompetzki/forcing-src/general Cohen\n-Q C:/ClaudeOutput/pompetzki/forcing-src/codex-judge-link-20261009 JudgeLink\n-Q C:/ClaudeOutput/pompetzki/lanes/CX3 CX3\n-Q C:/ClaudeOutput/pompetzki/lanes/CX3B CX3B\n```\n\n"
    "In the source package the corresponding directories are rocq/general, rocq/codex/codex-judge-link-20261009, rocq/CX3, and rocq/CX3B. It ships source and completed receipts; the original checked .vo hashes are in the JSON.\n\n"
    "`CX3.Conservativity2.gam_pure_conservative` at Conservativity2.v:60 has type:\n\n```coq\nforall f : form, syms f = [] -> prov Gam f -> prov ZFpure f.\n```\n\n"
    "Its input formula may have free variables. `pure_provability_iff` at line 75 proves equivalence on precisely that pure language. No closedness or execution hypothesis is added to either statement.\n\n"
    "`CX3.Stage2Conservativity2.accepted_member_Gam` at Stage2Conservativity2.v:82 is the general replay bridge:\n\n```coq\nforall (hypothesis : N -> form) reg ts t,\n  reg_ok hypothesis reg -> check_batch reg ts = true ->\n  In t ts -> t_hyps t = [] -> prov Gam (tof (t_stmt t)).\n```\n\n"
    "For any Good expansion table T, `accepted_expanded_member_pure` at line 91 adds `Good T` and `syms (expD Pr T (tof (t_stmt t))) = []` and proves the corresponding ZFpure statement. For the fixed 677-entry Stage 2 registry, `stage2_accepted_member_pure` at line 121 discharges registry soundness and the eleven-definition table and requires only abstract batch acceptance, membership, no hypotheses, and `covered stage2_table (tof (t_stmt t)) = true`.\n\n"
    "Exact applications of the existing proved constants are:\n\n```coq\nCX3.Conservativity2.gam_pure_conservative f Hpure DGam\nCX3.Stage2Conservativity2.accepted_member_Gam\n  hypothesis reg ts t R C Hin Hnil\nCX3.Stage2Conservativity2.stage2_accepted_member_pure\n  ts t C Hin Hnil Cov\n```\n\n"
    "Here C must come from a proved Replay2 computation or from the completed implementation theorem with its parser, registry, outcome and resource contracts discharged. A native ACCEPT receipt alone is not that proof. Arbitrary initial registries still require reg_ok; the fixed registry obligation is discharged by stage2_registry_ok, with its 677-entry count kernel-proved.\n\n"
    "Dependencies: Cohen.Syn/Prov define form, syms and prov; Cohen.Ax/Elim define Gam and ZFpure; Cohen.Use.prov_psub_to and Cohen.Elim.elim_step/okb_Dall support conservativity; Cohen.Expand.repl/buildT_good support faithful expansion; Cohen.Replay2 supplies check_batch and theorem data; Cohen.Replay3 and JudgeLink.JudgeBatch supply abstract soundness; Cohen.RpInitOk.REG0_ok discharges the fixed registry. SOURCE-HASHES.txt and the integration JSON bind those original files.\n\n"
    "## Seven concrete Stage 2 batches are already closed\n\n"
    "CX3B completed seven entire baseline batch computations and their member proofs after the original CX3 report. The integration verified the preserved proof objects, all seven successful recursive check receipts and Axioms: <none> contexts against CX3B's original manifest; it did not repeat those checks. The source/transcription hashes and both-judge receipt are retained.\n\n"
    "| Source | Theorems | Steps | Closed member theorem |\n|---|---:|---:|---|\n" baseline-table
    "\nFor each NN the theorem has type `forall t, In t batchNN -> prov Gam (tof (t_stmt t)) /\\ prov ZFpure (stage2_expand (tof (t_stmt t)))`. The named `batchNN_accepted`, `batchNN_metadata`, and `registryNN_correct` are proved constants; acceptance and coverage are discharged for these concrete batches. Stage2RegistryCertificate2.reg0_677_correct proves registry equality, and Stage2Bridge2.stage2_batch_certificate_registered composes the proved acceptance and metadata with the CX3 interface.\n\n"
    "The seven files total 1656 theorems and 53069 steps. Later larger priority waves belong to CX3B's separate in-flight work. The original CX3 report remains the earlier abstract milestone; these concrete certificates close that earlier finite batch premise for the baseline seven.\n\n"
    "## Package receipt scope\n\n"
    "INTEGRATION-RECOVERY-1.json contains " (number->string (length ordered-rows))
    " exact path/size/hash rows, with package copies and outer-manifest matches for shipped artifacts. The outer package MANIFEST.sha256 authenticates the shipped layout. The inner CX3 and CX3B manifests describe original lane snapshots: compiled objects and auxiliary artifacts are omitted from the source package, and CX3B receipts are routed separately from sources.\n\n"
    "The source directory's existing post-reboot current-source-scan.txt records 26000 checked/good files and zero failures. The COO recovery status separately records archive structural failures; this receipt authenticates source-package copies and the completed logical proof interfaces and does not certify those archives.\n\n"
    "Pure-Gam release wiring is present and hash-matched. The unfinished Stage 1 and ELF implementation theorems remain with their live owners. No desired native verdict equivalence has been supplied as an assumption or substituted for those proofs.\n"))
(new-file "STATUS-INTEGRATION-1.txt"
  (string-append "CX3 integration complete at " finished " (date.exe): original "
    (number->string (hash-count original-manifest)) " lane hashes and " (number->string (hash-count original-dependencies))
    " dependency hashes verified; zero compiler/kernel/judge jobs started. Exact public conservativity, accepted-member and faithful-expansion APIs plus seven completed CX3B baseline member theorems are linked in INTEGRATION-RECOVERY-1.md/json. The source package release-final-1925 already contains the CX3 and CX3B sources/receipts and marks rows2c/2d CLOSED; selected package copies match the outer manifest. Free variables remain permitted by gam_pure_conservative. Native Stage1 and CX4 implementation-to-check_batch proofs remain with their active owners. Original results and manifests remain alongside this fresh receipt.\n"))
(define generated (append outputs '("write-integration-recovery-1.rkt" "LIVE-OWNERSHIP-RECOVERY-1.json")))
(define manifest-paths
  (append (map (lambda (name) (build-path lane name)) (filter (lambda (n) (not (equal? n "INTEGRATION-RECOVERY-1.sha256"))) generated))
          (map (lambda (row) (string->path (hash-ref row 'live_path))) ordered-rows)))
(new-file "INTEGRATION-RECOVERY-1.sha256"
  (apply string-append (for/list ([path (remove-duplicates manifest-paths equal?)])
    (format "~a  ~a\n" (digest path) (path->string path)))))
(printf "Integration complete: ~a original CX3 hashes, ~a dependency hashes, ~a integration rows; no proof jobs.\n"
        (hash-count original-manifest) (hash-count original-dependencies) (length ordered-rows))
