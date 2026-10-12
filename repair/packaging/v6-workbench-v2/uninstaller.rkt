#lang racket/base
(require racket/cmdline racket/file racket/os racket/path racket/string racket/system json "package-utils.rkt")
(define root-arg #f) (define dry-run? #f)
(command-line #:program "Uninstall Abschluss"
  #:once-each [("--root") folder "Installation directory" (set! root-arg folder)]
  [("--dry-run") "List recorded installed files without removing them" (set! dry-run? #t)]
  #:args () (void))
(define root (bundle-root root-arg))
(define record (read-json-file (build-path root "INSTALLATION.json")))
(unless (and (equal? (hash-ref record 'version) version)
             (equal? (sha256-file (build-path root "MANIFEST.sha256")) (hash-ref record 'manifest_sha256)))
  (error 'uninstall "installation receipt and manifest do not match"))
(define entries (hash-ref record 'files))
(for ([entry entries]) (safe-path root (hash-ref entry 'path)))
(cond
  [dry-run? (write-json entries) (newline)]
  [else
   (define powershell (powershell-path))
   (define script (build-path root "Uninstall-Abschluss.ps1"))
   (unless (file-exists? script) (error 'uninstall "installed uninstall script is missing"))
   (define command (list powershell "-NoProfile" "-NonInteractive" "-WindowStyle" "Hidden" "-ExecutionPolicy" "Bypass"
                         "-File" (path->string script) "-InstallRoot" (path->string root) "-WaitForPid" (number->string (getpid))))
   (define log-path (build-path (find-system-path 'temp-dir)
                                (format "Abschluss-uninstall-~a-~a.log" (getpid) (current-seconds))))
   (define log (open-output-file log-path #:exists 'error))
   (define-values (process out in err) (apply subprocess log #f log (car command) (cdr command)))
   (close-output-port in) (close-output-port log)
   (printf "Recorded installed files will be removed after this program closes. Modified and additional files remain. Receipt: ~a\n" log-path)])
