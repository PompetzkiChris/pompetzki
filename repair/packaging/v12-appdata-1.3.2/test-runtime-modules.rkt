#lang racket/base
(require json "package-utils.rkt")
(write-json (runtime-modules))
(newline)
