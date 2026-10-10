#lang racket/base
(require racket/file racket/string)
(define source (file->string "write-integration-recovery-1.rkt"))
(define corrected (string-replace source "\\\\r?" "\\r?"))
(when (equal? source corrected) (error 'correction "expected escape absent"))
(define final (string-replace corrected "\"write-integration-recovery-1.rkt\"" "\"write-integration-recovery-2.rkt\""))
(display-to-file final "write-integration-recovery-2.rkt" #:exists 'error)
(display-to-file
 "Command: racket write-integration-recovery-1.rkt\nExit: 1\nObserved error: write-integration-recovery-1.rkt:55:25: read-syntax: illegal alphabetic escape in the exit-code regexp. No integration output was created by this failed parse. The source is retained; write-integration-recovery-2.rkt uses the Racket carriage-return string escape in the regexp.\n"
 "INTEGRATION-RECOVERY-first-failure.txt" #:exists 'error)
