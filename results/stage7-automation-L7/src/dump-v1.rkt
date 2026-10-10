#lang racket/base
(require "l7core-v1.rkt" racket/list)
(define args (vector->list (current-command-line-arguments)))
(dump-replay (string->number (car args)) (string->number (cadr args)))
