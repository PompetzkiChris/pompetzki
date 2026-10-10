#lang racket/base
(require racket/file racket/list racket/string racket/port)

(define lane (string->path "C:\\ClaudeOutput\\pompetzki\\lanes\\AG12-setmm-registry"))
(define judge-dir (string->path "C:\\ClaudeOutput\\pompetzki\\judge"))
(define output-dir (build-path lane "ROUTE-CHECK"))
(define pmp "C:\\ClaudeOutput\\pompetzki\\pompetzki.exe")
(define racket-exe "C:\\Program Files\\Racket\\racket.exe")
(define powershell-exe "C:\\Windows\\System32\\WindowsPowerShell\\v1.0\\powershell.exe")

(define (q x y) (list 'q x y))
(define (e x y) (list 'e x y))
(define (n f) (list 'n f))
(define (a f) (list 'a f))
(define (i f g) (list 'i f g))
(define (form-tokens f)
  (case (car f)
    [(e q) (map ~s* f)]
    [(n a) (cons (symbol->string (car f)) (form-tokens (cadr f)))]
    [(i) (append (list "i") (form-tokens (cadr f)) (form-tokens (caddr f)))]))
(define (~s* v) (format "~a" v))
(define (list-tokens vs) (cons (~s* (length vs)) (map ~s* vs)))
(define (step-tokens s)
  (case (car s)
    [(Y) (cons "Y" (form-tokens (cadr s)))]
    [(T) (append '("T") (list-tokens (cadr s)) (form-tokens (caddr s)))]
    [(E) (append (list "E" (~s* (cadr s))) (form-tokens (caddr s)))]
    [(M) (map ~s* s)]
    [(Z) (append '("Z") (form-tokens (cadr s)) (form-tokens (caddr s)))]))
(define (write-new path text)
  (call-with-output-file path #:exists 'error (lambda (out) (display text out))))

(struct sample (label stmt sig steps route instance variables) #:transparent)
(define ph (e 0 1))
(define ps (q 0 1))
(define ch (e 1 0))
(define f1 (i ph (i ps ph)))
(define f2 (i (i ph (i ps ch)) (i (i ph ps) (i ph ch))))
(define f3 (i (i (n ph) (n ps)) (i ps ph)))
;; Bound x has index 0; free y and z have indices 1 and 2 in each body.
(define f4 (i (a (i (e 0 1) (q 0 2))) (i (a (e 0 1)) (a (q 0 2)))))
;; x is absent from this ph, as the source disjoint-variable condition requires.
(define f5 (i ph (a (e 1 2))))
(define f6 (n (a (n (q 0 1)))))
(define f7 (i (q 0 1) (i (q 0 2) (q 1 2))))
(define f8 (i (q 0 1) (i (e 0 2) (e 1 2))))
(define f9 (i (q 0 1) (i (e 2 0) (e 2 1))))
;; The source ph depends on x. The outer RHS x binder is vacuous because the inner x binder shadows it.
(define f10 (i (n (a (e 0 1))) (a (n (a (e 0 2))))))

(define samples
  (list
   (sample "ax-1" f1 '(0 1) (list (list 'T '() f1)) "T/STaut"
           "ph=(x e. y); ps=(x=y)" "x,y")
   (sample "ax-2" f2 '(0 1) (list (list 'T '() f2)) "T/STaut"
           "ph=(x e. y); ps=(x=y); ch=(y e. x)" "x,y")
   (sample "ax-3" f3 '(0 1) (list (list 'T '() f3)) "T/STaut"
           "ph=(x e. y); ps=(x=y)" "x,y")
   (sample "ax-4" f4 '(0 1) (list (list 'Y f4)) "Y/SAx distribution"
           "ph=(x e. y); ps=(x=z); x bound; y,z free" "y,z")
   (sample "ax-5" f5 '(0 1) (list (list 'Y f5)) "Y/SAx vacuity"
           "ph=(y e. z); x absent from ph; source disjoint condition retained" "y,z")
   (sample "ax-6" f6 '(0) (list (list 'Y (q 0 0)) (list 'E 0 (i (q 0 0) f6)) (list 'M 0 1))
           "Y/SAx reflexivity; E/SExi; M/SMp"
           "-. A. x -. x=y; y free; witness y" "y")
   (sample "ax-7" f7 '(0 1 2) (list (list 'Z (q 0 3) f7)) "Z/SLeib equality"
           "x=y -> (x=z -> y=z); template q 0 3" "x,y,z")
   (sample "ax-8" f8 '(0 1 2) (list (list 'Z (e 0 3) f8)) "Z/SLeib left membership"
           "x=y -> (x e. z -> y e. z); template e 0 3" "x,y,z")
   (sample "ax-9" f9 '(0 1 2) (list (list 'Z (e 3 0) f9)) "Z/SLeib right membership"
           "x=y -> (z e. x -> z e. y); template e 3 0" "x,y,z")
   (sample "ax-10" f10 '(0) (list (list 'Y f10)) "Y/SAx vacuity after binding"
           "ph=(x e. y); -. A. x ph -> A. x -. A. x ph; y free" "y")))

(define (get-date)
  (define-values (proc stdout stdin stderr)
    (subprocess #f #f #f powershell-exe "-NoProfile" "-Command" "Get-Date -Format o"))
  (close-output-port stdin)
  (define result (port->string stdout))
  (define err (port->string stderr))
  (subprocess-wait proc)
  (unless (equal? 0 (subprocess-status proc)) (error 'Get-Date "~a" err))
  (string-trim result))

(define (powershell-command exe args)
  (string-append "& '" exe "' "
                 (string-join (for/list ([arg args]) (string-append "'" arg "'")) " ")))

(define (run-judge label kind exe args)
  (define prefix (string-append label "." kind))
  (define stdout-path (build-path output-dir (string-append prefix ".stdout.txt")))
  (define stderr-path (build-path output-dir (string-append prefix ".stderr.txt")))
  (define start (get-date))
  (define exit-code
    (call-with-output-file stdout-path #:exists 'error
      (lambda (stdout)
        (call-with-output-file stderr-path #:exists 'error
          (lambda (stderr)
            (parameterize ([current-directory judge-dir])
              (define-values (proc child-out child-in child-err)
                (apply subprocess stdout #f stderr exe args))
              (close-output-port child-in)
              (subprocess-wait proc)
              (subprocess-status proc)))))))
  (define finish (get-date))
  (define stdout (file->string stdout-path))
  (define stderr (file->string stderr-path))
  (define verdict
    (cond [(regexp-match? #px"(?m:^ACCEPT(?:[ \r\n]|$))" stdout) "ACCEPT"]
          [(regexp-match? #px"(?m:^REJECT(?:[ \r\n]|$))" stdout) "REJECT"]
          [(regexp-match? #rx"LIMIT|gosub: too deep|a memory block is full" (string-append stdout stderr)) "RESOURCE-STOP"]
          [else "OTHER"]))
  (write-new (build-path output-dir (string-append prefix ".run.txt"))
             (format "cwd: ~a\ncommand: ~a\nstarted: ~a\nfinished: ~a\nexit-code: ~a\nverdict: ~a\nstdout: ~a\nstderr: ~a\n"
                     judge-dir (powershell-command exe args) start finish exit-code verdict stdout-path stderr-path))
  (list exit-code verdict (string-trim stdout) (string-trim stderr)))

(make-directory output-dir)
(define rows
  (for/list ([s samples])
    (define file-name (string-append (sample-label s) ".jdg"))
    (define path (build-path output-dir file-name))
    (define theorem-tokens
      (append (form-tokens (sample-stmt s)) (list-tokens (sample-sig s))
              (list (~s* (length (sample-steps s)))) (append-map step-tokens (sample-steps s)) '("0")))
    (write-new path (string-append "JDG1\nR 0\nT 1\n" (string-join theorem-tokens " ") "\n"))
    (define pmp-result (run-judge (sample-label s) "pmp" pmp (list "judge-v3.pmp" (path->string path))))
    (define racket-result (run-judge (sample-label s) "racket" racket-exe (list "racket\\judge.rkt" (path->string path))))
    (printf "~a pmp ~a/~a racket ~a/~a\n" (sample-label s) (car pmp-result) (cadr pmp-result)
            (car racket-result) (cadr racket-result))
    (append (list (sample-label s) file-name (~s* (length (sample-steps s))) (sample-route s)
                  (sample-instance s) "none in source axiom" (sample-variables s))
            (map ~s* (take pmp-result 2)) (map ~s* (take racket-result 2)))))

(write-new (build-path output-dir "MANIFEST.tsv")
           (string-append
            "label\tfile\tsteps\troute\tinstance\tsource_essential_hypotheses\tfree_variables\tpmp_exit\tpmp_verdict\tracket_exit\tracket_verdict\n"
            (string-join (for/list ([row rows]) (string-join row "\t")) "\n") "\n"))
(define agrees
  (for/sum ([row rows])
    (if (and (equal? (list-ref row 7) "0") (equal? (list-ref row 8) "ACCEPT")
             (equal? (list-ref row 9) "0") (equal? (list-ref row 10) "ACCEPT")) 1 0)))
(write-new (build-path output-dir "READOUT.md")
           (format
            "# Routed logic axiom instances\n\nCreated: ~a (Get-Date).\n\n~a of 10 files have ACCEPT and exit 0 from both judges. Each file has an empty numbered registry, one theorem, no declared hypotheses, and 1 or 3 steps. The files contain 12 steps in total.\n\nThe sample is ax-1 through ax-10. Membership and equality atoms provide free-variable instances. ax-4 uses quantifier bodies that depend on x. ax-5 retains the source disjoint condition by choosing a body independent of x. ax-10 starts with a body that depends on x; the body under its outer RHS binder is independent of that binder because its inner x binder shadows it. ax-6 derives the existential formula from reflexivity by E and M. ax-7 through ax-9 use substitution templates with the free z index retained.\n\nNone of these ten source axioms has essential hypotheses. This sample therefore does not test ax-mp or ax-gen with essential premises, nor does it validate every route in LOGIC-ROUTES.tsv. Each run receipt records the exact PowerShell command, judge working directory, Get-Date start and finish, exit code, verdict, and paths to separate stdout and stderr files. MANIFEST.tsv records the route and verdicts per label.\n\nSource definitions: C:\\ClaudeOutput\\pompetzki\\forcing-src\\general\\Replay2.v (axshape and sstep); serialization: C:\\ClaudeOutput\\pompetzki\\judge\\rocq2jdg.rkt.\n"
            (get-date) agrees))
(unless (= agrees 10) (exit 1))
