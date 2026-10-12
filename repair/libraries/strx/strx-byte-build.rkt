#lang racket/base
(require racket/file racket/path)
;; strx.pmp is authoritative. The historical nested include remains a generated copy.
(define here (or (path-only (find-system-path 'run-file)) (current-directory)))
(define source (build-path here "strx.pmp"))
(define output (build-path here "lib" "strx.pmp"))
(make-directory* (build-path here "lib"))
(copy-file source output #f)
(displayln "CREATED lib/strx.pmp from canonical strx.pmp")
