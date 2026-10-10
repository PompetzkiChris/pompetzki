#lang racket/base
;; abschluss-verify.rkt -- Release asset verifier for Abschluss.
;; Checks SHA256SUMS, discovers the extracted bundle root, and runs every EXPECTED.tsv row.
;; Correction of the Antigravity AG5 source for the Abschluss 1.2.1 release.

(require racket/file
         racket/string
         racket/list
         racket/path
         racket/port
         racket/system
         racket/cmdline
         file/sha1
         file/unzip)

(define (sha256-hex path)
  (with-handlers ([exn:fail? (lambda (e) #f)])
    (call-with-input-file path
      (lambda (in)
        (bytes->hex-string (sha256-bytes in))))))

(define (verify-folder folder-str)
  (define folder (string->path folder-str))
  (unless (directory-exists? folder)
    (eprintf "Error: Directory not found: ~a\n" folder-str)
    (printf "NOT VERIFIED\n")
    (exit 1))

  (printf "===============================================================================\n")
  (printf "Abschluss Asset Verification: ~a\n" folder-str)
  (printf "===============================================================================\n\n")

  (define verified? #t)

  ;; --------------------------------------------------------------------------
  ;; Step (a): Verify SHA256SUMS.txt
  ;; --------------------------------------------------------------------------
  (printf "[Step a] Checking SHA256SUMS.txt...\n")
  (define sums-file
    (cond
      [(file-exists? (build-path folder "SHA256SUMS.txt"))
       (build-path folder "SHA256SUMS.txt")]
      [(file-exists? (build-path folder "sha256sums.txt"))
       (build-path folder "sha256sums.txt")]
      [else #f]))

  (unless sums-file
    (eprintf "Error: SHA256SUMS.txt not found in ~a\n" folder-str)
    (printf "NOT VERIFIED\n")
    (exit 1))

  (define sum-lines (file->lines sums-file))
  (define checked-count 0)
  (define ok-count 0)
  (define verified-files '())

  (for ([line sum-lines])
    (define trimmed (string-trim line))
    (unless (or (string=? trimmed "") (string-prefix? trimmed "#"))
      (set! checked-count (add1 checked-count))
      (define tokens (string-split trimmed))
      (cond
        [(>= (length tokens) 2)
         (define expected-hash (string-downcase (list-ref tokens 0)))
         (define raw-name (list-ref tokens 1))
         (define fn (if (string-prefix? raw-name "*") (substring raw-name 1) raw-name))
         (define target-file (build-path folder fn))
         (cond
           [(not (file-exists? target-file))
            (printf "  MISSING: ~a\n" fn)
            (set! verified? #f)]
           [else
            (define actual-hash (sha256-hex target-file))
            (cond
              [(and actual-hash (string=? (string-downcase actual-hash) expected-hash))
               (printf "  OK: ~a\n" fn)
               (set! ok-count (add1 ok-count))
               (set! verified-files
                     (cons (simplify-path (path->complete-path target-file) #f) verified-files))]
              [else
               (printf "  MISMATCH: ~a (expected ~a, got ~a)\n" fn expected-hash (or actual-hash "error"))
               (set! verified? #f)])])]
        [else
         (printf "  MALFORMED: ~a\n" trimmed)
         (set! verified? #f)])))

  (printf "SHA256 check: ~a / ~a files OK\n\n" ok-count checked-count)
  (when (zero? checked-count)
    (printf "  FAIL: SHA256SUMS.txt contains no file entries\n")
    (set! verified? #f))
  (unless verified?
    (printf "NOT VERIFIED\n")
    (exit 1))

  ;; --------------------------------------------------------------------------
  ;; Step (b): Unzip Windows bundle into a fresh temp directory
  ;; --------------------------------------------------------------------------
  (printf "[Step b] Locating and unzipping Windows bundle...\n")
  (define all-files (directory-list folder #:build? #t))
  (define win-zips
    (filter
     (lambda (f)
       (and (file-exists? f)
            (let ([s (string-downcase (path->string (file-name-from-path f)))])
              (and (string-suffix? s ".zip")
                   (or (string-contains? s "windows") (string-contains? s "win"))))))
     all-files))
  (define unlisted-win-zips
    (filter (lambda (f)
              (not (member (simplify-path (path->complete-path f) #f) verified-files)))
            win-zips))
  (when (pair? unlisted-win-zips)
    (for ([f unlisted-win-zips])
      (printf "  FAIL: Windows zip is not verified by SHA256SUMS.txt: ~a\n" (file-name-from-path f)))
    (printf "NOT VERIFIED\n")
    (exit 1))
  (unless (= (length win-zips) 1)
    (printf "  FAIL: Expected one verified Windows zip, found ~a\n" (length win-zips))
    (printf "NOT VERIFIED\n")
    (exit 1))
  (define win-zip (car win-zips))

  (define temp-dir #f)
  (cond
    [(not win-zip)
     (printf "  FAIL: No Windows zip found in ~a\n\n" folder-str)
     (set! verified? #f)]
    [else
     (printf "  Found Windows bundle: ~a\n" (path->string (file-name-from-path win-zip)))
     (set! temp-dir (make-temporary-file "abschluss-verify-~a" 'directory))
     (printf "  Extracting to temporary directory: ~a\n" (path->string temp-dir))
     (with-handlers
       ([exn:fail?
         (lambda (e)
           (eprintf "  Failed to unzip: ~a\n" (exn-message e))
           (set! verified? #f))])
       (define entries (zip-directory-entries (read-zip-directory win-zip)))
       (for ([entry entries])
         (define name (bytes->string/latin-1 entry))
         (when (or (regexp-match? #px"^[\\\\/]" name)
                   (regexp-match? #px":" name)
                   (regexp-match? #px"(?:^|[\\\\/])\\.\\.(?:[\\\\/]|$)" name))
           (error 'abschluss-verify "unsafe zip entry path: ~a" name)))
       (printf "  Archive paths: ~a entries checked\n" (length entries))
       (unzip win-zip (make-filesystem-entry-reader #:dest temp-dir))
       (printf "  Unzip successful.\n\n"))])

  ;; --------------------------------------------------------------------------
  ;; Step (c): Run pompetzki.exe judge-v3.pmp on every required EXPECTED.tsv row.
  ;; --------------------------------------------------------------------------
  (printf "[Step c] Checking selftest EXPECTED.tsv...\n")
  (when temp-dir
    ;; A release zip may put the payload at its root or one directory below it.
    ;; Discover the payload by Abschluss.exe, rather than assuming an unversioned zip root.
    (define bundle-roots
      (filter (lambda (p) (file-exists? (build-path p "Abschluss.exe")))
              (cons temp-dir
                    (filter directory-exists? (directory-list temp-dir #:build? #t)))))
    (cond
      [(not (= (length bundle-roots) 1))
       (printf "  FAIL: Expected one Abschluss bundle root, found ~a\n\n" (length bundle-roots))
       (set! verified? #f)]
      [else
       (define bundle-root (car bundle-roots))
       (printf "  Bundle root: ~a\n" bundle-root)
       (define expected-tsv
         (for/first ([p (list (build-path bundle-root "selftest" "EXPECTED.tsv")
                             (build-path bundle-root "EXPECTED.tsv"))]
                     #:when (file-exists? p))
           p))
       (cond
         [(not expected-tsv)
          (printf "  FAIL: Required selftest EXPECTED.tsv is missing\n\n")
          (set! verified? #f)]
         [else
          (define selftest-root (path-only expected-tsv))
          (printf "  Found EXPECTED.tsv: ~a\n" expected-tsv)
          ;; Prefer the selftest's own interpreter and judge, which have its registry data.
          (define pompetzki-exe
            (for/first ([p (list (build-path selftest-root "pompetzki.exe")
                                (build-path bundle-root "pompetzki.exe")
                                (build-path bundle-root "bin" "windows" "pompetzki.exe")
                                (build-path bundle-root "bin" "pompetzki.exe")
                                (build-path bundle-root "judge" "pompetzki.exe"))]
                        #:when (file-exists? p))
              p))
          (define judge-pmp
            (for/first ([p (list (build-path selftest-root "judge-v3.pmp")
                                (build-path bundle-root "judge" "judge-v3.pmp")
                                (build-path bundle-root "judge-v3.pmp")
                                (build-path bundle-root "bin" "judge-v3.pmp"))]
                        #:when (file-exists? p))
              p))
          (cond
            [(not (and pompetzki-exe judge-pmp))
             (printf "  FAIL: Required pompetzki.exe or judge-v3.pmp is missing\n\n")
             (set! verified? #f)]
            [else
             (define judge-dir (path-only judge-pmp))
             (define rows (file->lines expected-tsv))
             (define checks 0)
             (define passes 0)
             (for ([row rows])
               (define trimmed (string-trim row))
               (unless (or (string=? trimmed "") (string-prefix? trimmed "#"))
                 (set! checks (add1 checks))
                 (define parts (string-split trimmed "\t"))
                 (cond
                   [(not (and (= (length parts) 2)
                              (member (string-trim (cadr parts)) '("ACCEPT" "REJECT"))))
                    (printf "  FAIL: Malformed EXPECTED.tsv row: ~a\n" trimmed)]
                   [else
                    (define rel-jdg (car parts))
                    (define expected-verdict (string-trim (cadr parts)))
                    (define jdg-path (build-path selftest-root rel-jdg))
                    (cond
                      [(not (file-exists? jdg-path))
                       (printf "  FAIL: Missing JDG: ~a\n" rel-jdg)]
                      [else
                       (printf "  RUN: ~a (expected ~a)\n" rel-jdg expected-verdict)
                       (flush-output)
                       (define-values (sp stdout-port stdin-port stderr-port)
                         (parameterize ([current-directory judge-dir])
                           (subprocess #f #f 'stdout pompetzki-exe judge-pmp (path->string jdg-path))))
                       (close-output-port stdin-port)
                       (define out-str (port->string stdout-port))
                       (close-input-port stdout-port)
                       (when stderr-port (close-input-port stderr-port))
                       (subprocess-wait sp)
                       (define code (subprocess-status sp))
                       (define verdict-match (regexp-match #px"^(ACCEPT|REJECT|LIMIT)(?:\\s|$)" out-str))
                       (define actual-verdict (if verdict-match (cadr verdict-match) "UNKNOWN"))
                       (define expected-code (if (equal? expected-verdict "ACCEPT") 0 1))
                       (cond
                         [(and (equal? actual-verdict expected-verdict) (= code expected-code))
                          (set! passes (add1 passes))
                          (printf "  PASS: ~a -> ~a (exit ~a)\n" rel-jdg actual-verdict code)]
                         [else
                          (printf "  FAIL: ~a -> expected ~a exit ~a, got ~a exit ~a (~a)\n"
                                  rel-jdg expected-verdict expected-code actual-verdict code (string-trim out-str))])])]))
               (flush-output))
             (define selftest-passed? (and (positive? checks) (= checks passes)))
             (unless selftest-passed? (set! verified? #f))
             (printf "Selftest result: ~a (~a/~a rows)\n\n" (if selftest-passed? "PASSED" "FAILED") passes checks)])])])
    (printf "  Extracted verification files retained at: ~a\n\n" temp-dir))

  ;; --------------------------------------------------------------------------
  ;; Step (d): Final Verdict and Exit Code
  ;; --------------------------------------------------------------------------
  (if verified?
      (begin
        (printf "===============================================================================\n")
        (printf "VERIFIED\n")
        (printf "===============================================================================\n")
        (exit 0))
      (begin
        (printf "===============================================================================\n")
        (printf "NOT VERIFIED\n")
        (printf "===============================================================================\n")
        (exit 1))))

(module+ main
  (define args (current-command-line-arguments))
  (cond
    [(= (vector-length args) 1)
     (verify-folder (vector-ref args 0))]
    [else
     (eprintf "Usage: abschluss-verify <folder-with-SHA256SUMS.txt>\n")
     (printf "NOT VERIFIED\n")
     (exit 1)]))
