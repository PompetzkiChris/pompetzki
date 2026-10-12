#lang racket/base
(require racket/class racket/cmdline racket/file racket/gui/base racket/list racket/path racket/port racket/string
         racket/system json "package-utils.rkt")
(define source-arg #f) (define target-arg #f) (define no-shortcut? #f) (define ui-test #f)
(command-line #:program "Install Abschluss"
  #:once-each
  [("--source") folder "Portable bundle to install" (set! source-arg folder)]
  [("--target") folder "New installation directory" (set! target-arg folder)]
  [("--no-shortcut") "Do not create a Start Menu shortcut" (set! no-shortcut? #t)]
  [("--ui-selftest") file "Exercise the owned installer controls" (set! ui-test file)]
  #:args () (void))
(define source (bundle-root source-arg))
(define (default-target)
  (define local (or (getenv "LOCALAPPDATA") (find-system-path 'pref-dir)))
  (define programs (build-path local "Programs"))
  (build-path (if (and (directory-exists? programs) (not (reparse? programs))) programs local) "Abschluss-1.3.1"))
(define (psquote text) (string-append "'" (string-replace text "'" "''") "'"))
(define (shortcut! target)
  (define folder (build-path (or (getenv "APPDATA") (find-system-path 'pref-dir)) "Microsoft" "Windows" "Start Menu" "Programs"))
  (define link (build-path folder "Abschluss 1.3.1.lnk"))
  (when (file-exists? link) (error 'install "Start Menu shortcut already exists: ~a" link))
  (make-directory* folder)
  (define script
    (string-append "$shell=New-Object -ComObject WScript.Shell; $link=$shell.CreateShortcut(" (psquote (path->string link))
                   "); $link.TargetPath=" (psquote (path->string (build-path target "Abschluss Start.exe")))
                   "; $link.WorkingDirectory=" (psquote (path->string target)) "; $link.Save()"))
  (define result (run-process (list (powershell-path)
                                   "-NoProfile" "-NonInteractive" "-WindowStyle" "Hidden" "-Command" script) source 30))
  (unless (= 0 (hash-ref result 'exit)) (error 'install "shortcut creation failed: ~a" (hash-ref result 'stderr)))
  (path->string link))
(define (install! target-text)
  (define rows (read-manifest source))
  (define checks (verify-manifest source))
  (unless (andmap (lambda (row) (hash-ref row 'match)) checks) (error 'install "the download does not match MANIFEST.sha256"))
  (for ([required '("Abschluss Start.exe" "bin/MathWorkbench.exe" "pompetzki.exe" "judge-rkt.exe"
                    "judge/judge-v6.pmp" "bin/verified-book-post.exe" "bin/verified-book-check.exe"
                    "Uninstall Abschluss.exe" "Uninstall-Abschluss.ps1")])
    (unless (file-exists? (safe-path source required)) (error 'install "required application file is missing: ~a" required)))
  (define target (validate-new-target source target-text))
  (make-directory target)
  (define copied '())
  (with-handlers ([exn:fail? (lambda (e)
                             (write-json-new (build-path target "INSTALLATION-PARTIAL.json")
                                             (hasheq 'version version 'files (reverse copied) 'error (exn-message e)))
                             (raise e))])
    (for ([row rows])
      (define relative (hash-ref row 'path))
      (define file (safe-path target relative))
      (make-directory* (path-only file))
      (copy-file (safe-path source relative) file #f)
      (set! copied (cons row copied)))
    (copy-file (build-path source "MANIFEST.sha256") (build-path target "MANIFEST.sha256") #f)
    (define shortcut (and (not no-shortcut?) (shortcut! target)))
    (write-json-new (build-path target "INSTALLATION.json")
                    (hash-set (hash-set (new-record source rows) 'shortcut (or shortcut #f))
                              'shortcut_sha256 (if shortcut (sha256-file shortcut) #f)))
    (hasheq 'status "INSTALLED" 'version version 'target (path->string target)
            'files (add1 (length rows)) 'shortcut (or shortcut #f))))
(define (window)
  (define frame (new frame% [label "Install Abschluss 1.3.1"] [width 580] [height 260]))
  (define panel (new vertical-panel% [parent frame] [alignment '(left top)] [border 20] [spacing 12]))
  (new message% [parent panel] [label "Install exact matrix mathematics on this computer."])
  (define location (new text-field% [parent panel] [label "New installation folder"]
                        [init-value (if target-arg target-arg (path->string (default-target)))]))
  (define answer (new text-field% [parent panel] [label "Answer"] [style '(multiple)] [min-height 100]))
  (define result #f)
  (define button
    (new button% [parent panel] [label "Install"]
         [callback (lambda (_button _event)
                     (with-handlers ([exn:fail? (lambda (e) (set! result (hasheq 'status "REFUSED" 'message (exn-message e)))
                                                   (send answer set-value (exn-message e)))])
                       (set! result (install! (send location get-value)))
                       (send answer set-value (format "Abschluss ~a installed in ~a" version (hash-ref result 'target)))))]))
  (values frame location button answer (lambda () result)))
(with-handlers ([exn:fail? (lambda (e) (eprintf "~a\n" (exn-message e)) (exit 2))])
  (cond
    [ui-test
     (set! no-shortcut? #t)
     (define-values (frame location button answer result) (window))
     (send button command (new control-event% [event-type 'button]))
     (write-json-new ui-test (hasheq 'controls (list (send button get-label)) 'location (send location get-value)
                                     'answer (send answer get-value) 'result (result)
                                     'test_visibility "Own installer controls invoked without showing or focusing a window"))
     (send frame show #f) (exit (if (equal? (hash-ref (result) 'status) "INSTALLED") 0 2))]
    [target-arg (write-json (install! target-arg)) (newline) (exit 0)]
    [else (define-values (frame location button answer result) (window)) (send frame show #t)]))
