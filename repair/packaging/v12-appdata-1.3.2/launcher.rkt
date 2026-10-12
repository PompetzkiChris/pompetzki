#lang racket/base
(require racket/class racket/cmdline racket/date racket/file racket/format racket/gui/base racket/list racket/path racket/port racket/string
         racket/system json net/sendurl "package-utils.rkt")
(define root-arg #f) (define action #f) (define input #f) (define output #f) (define menu-only? #f)
(command-line #:program "Abschluss Start"
  #:once-each
  [("--root") path "Portable bundle root" (set! root-arg path)]
  [("--version") "Print version" (set! action 'version)]
  [("--list") "List application actions" (set! action 'list)]
  [("--verify-install") "Check every installed file" (set! action 'verify)]
  [("--judge") file "Judge with pmp and the Racket cross-check" (set! action 'judge) (set! input file)]
  [("--launch") name "Launch math, cockpit, or docs" (set! action (string->symbol name))]
  [("--menu") "Show launcher controls" (set! menu-only? #t)]
  [("--ui-selftest") receipt "Exercise this launcher's owned GUI controls" (set! action 'ui-test) (set! output receipt)]
  [("--fixture") file "JDG fixture for owned-control test" (set! input file)]
  #:args () (void))
(define routes '((math "Math Workbench" "bin/MathWorkbench.exe")
                 (cockpit "Cockpit" "Abschluss.exe")
                 (judge "Judge a file" "judge/judge-v6.pmp")
                 (book-verify "Verify historical Book" "bin/bookverify.exe")
                 (posting-verify "Verify a posting" "bin/verified-book-check.exe")
                 (book-post "Post verified mathematics" "bin/verified-book-post.exe")
                 (docs "Documentation" "docs/1.3.2/USER-GUIDE.md")))
(when (eq? action 'version) (displayln version) (exit 0))
(define home (bundle-root root-arg))
(define (path relative) (safe-path home relative))
(define (check-file file) (unless (file-exists? file) (error 'Abschluss "required application file is missing: ~a" file)))
(define (launch file [args '()])
  (check-file file)
  (define-values (sp out in err)
    (parameterize ([current-directory home]) (apply subprocess #f #f #f file args)))
  (close-output-port in)
  (thread (lambda () (port->string out) (close-input-port out)))
  (thread (lambda () (port->string err) (close-input-port err)))
  (format "Started ~a" (file-name-from-path file)))
(define (judge file)
  (define source (path->complete-path file)) (check-file source)
  (define native (path "judge/judge-v6-windows.exe"))
  (define commands (list (if (file-exists? native) (list native source)
                            (list (path "pompetzki.exe") (path "judge/judge-v6.pmp") source))
                         (list (path "judge-rkt.exe") source)))
  (for ([command commands] [name '(pmp racket)])
    (for ([program (in-list (if (eq? name 'pmp) (take command 2) (take command 1)))]) (check-file program)))
  (define runs (for/list ([command commands]) (run-process command home)))
  (define (accepted? run)
    (and (= (hash-ref run 'exit) 0) (regexp-match? #px"\\bACCEPT\\b" (hash-ref run 'stdout))
         (not (regexp-match? #px"\\bREJECT\\b" (hash-ref run 'stdout)))))
  (define (rejected? run)
    (and (= (hash-ref run 'exit) 1) (regexp-match? #px"\\bREJECT\\b" (hash-ref run 'stdout))
         (not (regexp-match? #px"\\bACCEPT\\b" (hash-ref run 'stdout)))))
  (hasheq 'file (path->string source) 'runs runs
          'verdict (cond [(andmap accepted? runs) "ACCEPT"] [(andmap rejected? runs) "REJECT"] [else "CHECKS DISAGREE OR DID NOT COMPLETE"])))
(define (perform route)
  (case route
    [(math) (launch (path "bin/MathWorkbench.exe"))]
    [(cockpit) (launch (path "Abschluss.exe") (list (path->string (path "config"))))]
    [(docs) (check-file (path "docs/1.3.2/USER-GUIDE.md")) (send-url/file (path "docs/1.3.2/USER-GUIDE.md")) "Documentation opened"]
    [(verify)
     (define rows (verify-manifest home))
     (format "Manifest: ~a of ~a files match" (count (lambda (row) (hash-ref row 'match)) rows) (length rows))]
    [(judge)
     (define file (or input (get-file "Choose mathematics certificate" #f home #f #f '() '(("Mathematics certificate" "*.jdg")))))
     (if file (jsexpr->string (judge file)) "No file selected")]
    [(book-verify)
     (define result (run-process (list (path "bin/bookverify.exe") (path "book")) home))
     (string-append (hash-ref result 'stdout) (hash-ref result 'stderr))]
    [(book-post)
     (define file (get-file "Choose mathematics to verify and post" #f home #f #f '() '(("Mathematics certificate" "*.jdg"))))
     (define target (and file (put-file "Choose a new Book posting folder" #f home "new-posting")))
     (if (and file target)
         (let* ([date (date->string (seconds->date (current-seconds)) #f)]
                [stamp (format "~a-~a-~a" (date-year (seconds->date (current-seconds)))
                               (~r (date-month (seconds->date (current-seconds))) #:min-width 2 #:pad-string "0")
                               (~r (date-day (seconds->date (current-seconds))) #:min-width 2 #:pad-string "0"))]
                [result (run-process (list (path "bin/verified-book-post.exe") "--bundle" (path->string home)
                                          (path->string target) stamp (path->string file)) home 3600)])
           (string-append (hash-ref result 'stdout) (hash-ref result 'stderr)))
         "No posting requested")]
    [(posting-verify)
     (define folder (get-directory "Choose a verified mathematics posting" #f home))
     (if folder
         (let ([result (run-process (list (path "bin/verified-book-check.exe") "--bundle" (path->string home)
                                          (path->string folder)) home 3600)])
           (string-append (hash-ref result 'stdout) (hash-ref result 'stderr)))
         "No posting selected")]
    [(about) (format "Abschluss ~a â€” exact matrix mathematics by Christopher Pompetzki" version)]
    [else (error 'Abschluss "unknown action: ~a" route)]))
(define (make-window)
  (define frame (new frame% [label (string-append "Abschluss " version)] [width 600] [height 560]))
  (define panel (new vertical-panel% [parent frame] [alignment '(left top)] [border 20] [spacing 12]))
  (new message% [parent panel] [label "Exact matrix mathematics"] [font (make-object font% 20 'default 'normal 'bold)])
  (new message% [parent panel] [label "Enter matrices, compute, and read the complete answer in Math Workbench."])
  (define buttons (make-hash))
  (define answer (new text-field% [parent panel] [label "Answer"] [style '(multiple)] [min-height 180]))
  (define last-result #f)
  (for ([route (append (list '(math "Open Math Workbench"))
                      '((cockpit "Cockpit") (judge "Judge a file...") (book-verify "Verify historical Book")
                        (posting-verify "Verify a posting...")
                        (book-post "Post verified mathematics...") (docs "Documentation")
                        (verify "Verify installed files") (about "About")))])
    (define key (car route))
    (define button
      (new button% [parent panel] [label (cadr route)] [stretchable-width #t]
           [callback (lambda (_button _event)
             (with-handlers ([exn:fail? (lambda (e) (set! last-result (exn-message e)) (send answer set-value last-result))])
               (set! last-result (perform key)) (send answer set-value last-result)))]))
    (hash-set! buttons key button))
  (values frame buttons answer (lambda () last-result)))
(with-handlers ([exn:fail? (lambda (e) (eprintf "~a\n" (exn-message e)) (exit 2))])
  (case action
    [(list) (for ([row routes]) (printf "~a\t~a\t~a\n" (car row) (cadr row) (path->string (path (caddr row))))) (exit 0)]
    [(verify) (define rows (verify-manifest home)) (write-json rows) (newline)
              (exit (if (andmap (lambda (row) (hash-ref row 'match)) rows) 0 1))]
    [(judge) (define result (judge input)) (write-json result) (newline)
             (exit (if (equal? (hash-ref result 'verdict) "ACCEPT") 0 1))]
    [(math cockpit docs) (displayln (perform action)) (exit 0)]
    [(ui-test)
     (define-values (frame buttons answer result) (make-window))
     (define results
       (for/list ([key (if input '(about verify judge) '(about verify))])
         (send (hash-ref buttons key) command (new control-event% [event-type 'button]))
         (hasheq 'button (symbol->string key) 'label (send (hash-ref buttons key) get-label)
                 'answer (send answer get-value) 'callback_result (result))))
     (write-json-new output (hasheq 'version version 'bundle (path->string home)
                                   'controls (map symbol->string (hash-keys buttons)) 'runs results
                                   'test_visibility "Own GUI controls created and invoked without showing or focusing a window"))
     (send frame show #f) (exit 0)]
    [else
     (define-values (frame buttons answer result) (make-window))
     (send frame show #t)
     (unless menu-only?
       (queue-callback (lambda () (send (hash-ref buttons 'math) command (new control-event% [event-type 'button])))))]))
