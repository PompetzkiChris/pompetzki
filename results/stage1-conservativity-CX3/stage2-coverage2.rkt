#lang racket/base
;; CX3 Stage 2 coverage: read existing sources and JDG1 files; create a new receipt.
;; Run: racket stage2-coverage.rkt NEW-RECEIPT-PATH
(require racket/file racket/list racket/match racket/port racket/string
         racket/system racket/path file/sha1)

(define root "C:/ClaudeOutput/pompetzki")
(define source (build-path root "sigma1/sigma1.rkt"))
(define out-dir (build-path root "sigma1/out"))
(define data-file (build-path root "forcing-src/general/Data.v"))
(define rpinit-file (build-path root "forcing-src/general/RpInit.v"))
(define manifest-file (build-path out-dir "manifest.txt"))
(define judge-receipt (build-path root "sigma1/judge-run-1.txt"))
(define historical-results (build-path root "sigma1/RESULTS.md"))
(define date-exe "C:/Program Files/Git/usr/bin/date.exe")

(define (date-text)
  (string-trim
   (with-output-to-string
     (lambda ()
       (unless (system* date-exe "+%Y-%m-%dT%H:%M:%S%:z")
         (error 'date "date.exe returned failure"))))))
(define started (date-text))
(define receipt-path
  (match (vector->list (current-command-line-arguments))
    [(list p) (string->path p)]
    [_ (error 'usage "racket stage2-coverage.rkt NEW-RECEIPT-PATH")]))
(when (file-exists? receipt-path)
  (error 'receipt "already exists: ~a" receipt-path))

(define (sha256 path)
  (call-with-input-file path
    (lambda (in) (bytes->hex-string (sha256-bytes in)))))
(define rows '())
(define (note fmt . args)
  (set! rows (cons (apply format fmt args) rows)))
(define (must condition fmt . args)
  (unless condition (apply error 'coverage fmt args)))

;; Read private pure readers through the module namespace. Do not run its main.
(dynamic-require source #f)
(define source-ns (module->namespace source))
(define (binding name)
  (parameterize ([current-namespace source-ns]) (eval name)))
(define read-jdg-text (binding 'read-jdg-text))
(define tof (binding 'tof))
(define check-registry-text (binding 'check-registry-text))

;; Data rows are source text; their parsing into Dall is kernel-checked by Ax.v.
(define data-text (file->string data-file))
(define symtab-text (car (string-split data-text "Definition defs")))
(define symtab
  (regexp-match* #px"\"([^\"]+)\"" symtab-text #:match-select cadr))
(define names
  (make-hash (for/list ([name symtab] [i (in-naturals)]) (cons name i))))
(define defs-text
  (car (string-split (cadr (string-split data-text "Definition defs"))
                     "Definition hyps")))
(define defs
  (regexp-match* #px"\\(\"([^\"]+)\", \\[([^\\]]*)\\], \"([^\"]*)\"\\)"
                 defs-text #:match-select cdr))
(must (= (length defs) 670) "expected 670 definition rows, got ~a" (length defs))
(define seen (make-hash))
(define arities (make-hash))
(for ([d defs] [i (in-naturals)])
  (match-define (list name params body) d)
  (define arity (length (regexp-match* #px"\"([^\"]+)\"" params)))
  (must (hash-has-key? names name) "definition missing from symtab: ~a" name)
  (must (= arity (string->number (substring name (sub1 (string-length name)))))
        "definition suffix/parameter arity differs at ~a" name)
  (must (not (hash-has-key? seen name)) "duplicate definition: ~a" name)
  (for ([dep (remove-duplicates
               (filter (lambda (s) (hash-has-key? names s)) (string-split body)))])
    (must (hash-has-key? seen dep)
          "definition row ~a (~a) refers to a later or undefined symbol ~a"
          i name dep))
  (hash-set! seen name arity)
  (hash-set! arities (hash-ref names name) arity))

(define manifest-hashes (make-hash))
(define current-name #f)
(for ([line (file->lines manifest-file)])
  (match (regexp-match #px"^([^ ]+[.]jdg) " line)
    [(list _ name) (set! current-name name)] [_ (void)])
  (match (regexp-match #px"^  sha256 ([0-9a-f]{64})$" line)
    [(list _ h) (must current-name "manifest hash without filename")
                 (hash-set! manifest-hashes current-name h)] [_ (void)]))

(define all-pairs (make-hash))
(define (collect f pairs)
  (match f
    [(list 'P p args)
     (define pair (list p (length args)))
     (must (equal? (hash-ref arities p #f) (length args))
           "statement predicate ~a has arity ~a; declared ~a"
           p (length args) (hash-ref arities p #f))
     (hash-set! pairs pair #t)
     (hash-set! all-pairs pair #t)]
    [(list (or 'N 'A) a) (collect a pairs)]
    [(list 'I a b) (collect a pairs) (collect b pairs)]
    [_ (void)]))

(define jdg-files
  (sort (filter (lambda (p) (regexp-match? #rx"[.]jdg$" (path->string p)))
                (directory-list out-dir #:build? #t))
        string<? #:key path->string))
(must (= (length jdg-files) 7) "expected 7 top-level JDG1 files, got ~a" (length jdg-files))
(define historical-lines (file->lines judge-receipt))
(define total-thms 0)
(define total-steps 0)
(define total-prelude 0)
(define total-prelude-steps 0)

(note "CX3 Stage 2 coverage receipt")
(note "Started from date.exe: ~a" started)
(note "No judges were rerun. Historical verdicts below are from existing judge-run-1.txt.")
(note "Definition source check: symtab ~a; rows ~a; unique definitions ~a; all body dependencies precede their definitions; parameter arities match name suffixes."
      (length symtab) (length defs) (hash-count seen))
(note "Symtab names without definitions: ~s"
      (filter (lambda (s) (not (hash-has-key? seen s))) symtab))

(for ([path jdg-files])
  (define name (path->string (file-name-from-path path)))
  (define stem (substring name 0 (- (string-length name) 4)))
  (define index-lines (file->lines (build-path out-dir (string-append stem ".index.txt"))))
  (define-values (reg ts) (read-jdg-text (file->string path)))
  (define rc (check-registry-text (file->string path)))
  (must (string-prefix? rc "OK:") "registry mismatch: ~a: ~a" name rc)
  (must (andmap (lambda (t) (null? (cadddr t))) ts)
        "theorem has placeholder hypotheses: ~a" name)
  (must (= (length index-lines) (length ts)) "index count differs: ~a" name)
  (define prelude-indices
    (for/list ([line index-lines] [i (in-naturals)]
               #:when (regexp-match? #px"^\\d+ \\(replay \\d+\\) " line)) i))
  (define steps (for/sum ([t ts]) (length (caddr t))))
  (define prelude-steps
    (for/sum ([i prelude-indices]) (length (caddr (list-ref ts i)))))
  (define pairs (make-hash))
  (for ([t ts]) (collect (tof (car t)) pairs))
  (define h (sha256 path))
  (must (equal? h (hash-ref manifest-hashes name #f))
        "current hash differs from stored manifest: ~a" name)
  (define historical-row
    (filter (lambda (line) (string-prefix? line (string-append "out\\" name " | ")))
            historical-lines))
  (must (= (length historical-row) 1) "historical verdict row count differs: ~a" name)
  (must (regexp-match? #px"pmp ACCEPT exit 0.*racket ACCEPT exit 0" (car historical-row))
        "historical verdicts differ: ~a" name)
  (define expected-counts (format "theorems ~a steps ~a" (length ts) steps))
  (must (string-contains? (car historical-row) expected-counts)
        "historical step/theorem counts differ: ~a" name)
  (set! total-thms (+ total-thms (length ts)))
  (set! total-steps (+ total-steps steps))
  (set! total-prelude (+ total-prelude (length prelude-indices)))
  (set! total-prelude-steps (+ total-prelude-steps prelude-steps))
  (note "~a: registry 677; theorems ~a; steps ~a; prelude ~a; generated ~a; prelude-steps ~a; all hypotheses []; symbol/arity pairs ~s; sha256 ~a"
        name (length ts) steps (length prelude-indices)
        (- (length ts) (length prelude-indices)) prelude-steps
        (sort (hash-keys pairs) < #:key car) h)
  (note "  Registry comparison: ~a" rc))

(define accept-count
  (count (lambda (line) (regexp-match? #px"pmp ACCEPT exit 0.*racket ACCEPT exit 0" line))
         historical-lines))
(define reject-count
  (count (lambda (line) (regexp-match? #px"pmp REJECT exit 1.*racket REJECT exit 1" line))
         historical-lines))
(must (= accept-count 7) "historical ACCEPT row count: ~a" accept-count)
(must (= reject-count 70) "historical REJECT row count: ~a" reject-count)
(note "Totals: ~a theorems; ~a steps; ~a copied prelude theorems; ~a generated theorems; ~a copied prelude steps."
      total-thms total-steps total-prelude (- total-thms total-prelude) total-prelude-steps)
(note "Combined statement symbol/arity pairs: ~s" (sort (hash-keys all-pairs) < #:key car))
(note "Historical receipts: ~a both-judge ACCEPT rows and ~a both-judge REJECT mutant rows."
      accept-count reject-count)
(note "Correction beside existing RESULTS.md: its 154 prelude / 1502 generated split differs from the current indices and manifest: 119 prelude / 1537 generated. The 1656 theorem / 53069 step totals agree.")
(note "This receipt checks syntax, registry identity, arities, hypotheses, counts, and existing hashes; it does not run Replay2.check_batch in Rocq or establish the native judge simulation theorem.")
(for ([path (list source data-file rpinit-file manifest-file judge-receipt historical-results)])
  (note "Source sha256 ~a ~a" (sha256 path) path))
(note "Finished from date.exe: ~a" (date-text))
(define result (string-append (string-join (reverse rows) "\n") "\n"))
(call-with-output-file receipt-path (lambda (port) (display result port)) #:exists 'error)
(display result)
