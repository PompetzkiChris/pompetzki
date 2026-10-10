#lang racket/base
;; mut-file-v1.rkt -- lane L7: for a JDG1 file written by another program (here the pmp emitter eqchain-v1.pmp): the registry
;; check, the copy of the checker, the index, and the mutated copies that the copy of the checker rejects (mutants-v1.rkt's
;; kinds; none of the file's theorems is treated as prelude). Usage: racket mut-file-v1.rkt FILE.jdg DIR BASE
(require "l7core-v1.rkt" "mutants-v1.rkt" racket/list racket/match racket/string racket/file)
(match-define (list file dir base) (vector->list (current-command-line-arguments)))
(load-base!)
(define text (file->string file))
(define-values (rg ths) (read-jdg-text text))
(make-directory* (build-path dir "mut"))
(define notes '())
(define (note! . xs) (set! notes (cons (apply format xs) notes)) (printf "~a\n" (car notes)) (flush-output))
(note! "~a (~a bytes)" file (file-size file))
(note! "  theorems ~a, steps ~a" (length ths) (apply + (map (lambda (t) (length (caddr t))) ths)))
(note! "  sha256 ~a" (sha256-hex file))
(note! "  registry: ~a" (check-registry-text text))
(note! "  copy of the checker: ~a" (check-batch rg ths))
(write-new (build-path dir (string-append base ".index.txt"))
           (string-join (for/list ([t ths] [i (in-naturals)]) (format "~a ~a" i (show (tof (car t))))) "\n"))
(for ([m (mutants2 text (Neg (tof (car (last ths)))) (map (lambda (t) #f) ths))])
  (match-define (list tag mtext where v) m)
  (cond [(eq? (car v) 'REJECT)
         (write-new (build-path dir "mut" (string-append base "-" tag ".jdg")) mtext)
         (note! "  mutant ~a (~a): copy of the checker ~a" tag where v)]
        [else (note! "  mutant ~a (~a): NOT WRITTEN, the copy of the checker accepts it" tag where)]))
(write-new (build-path dir (string-append base ".manifest.txt")) (string-join (reverse notes) "\n"))
