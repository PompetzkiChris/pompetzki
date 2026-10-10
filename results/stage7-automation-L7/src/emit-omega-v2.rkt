#lang racket/base
;; emit-omega-v2.rkt -- lane L7, item 4: writes DIR/L7-4-omega-laws.jdg (the general laws of Add and Mul on omega),
;; its index, its mutants in DIR/mut and the manifest lines in DIR/L7-4-omega-laws.manifest.txt.
(require "l7core-v1.rkt" "omega-base-v1.rkt" "omega-kind-v5.rkt" "omega-laws-v3.rkt" racket/string)
(define dir (vector-ref (current-command-line-arguments) 0))
(load-base!)
;; the false twin of the last theorem: Nat x & Nat y & Mul(x,y,z) -> Add(x,y,z), closed
(define twin (c (let ([x (fresh-sym 'x)] [y (fresh-sym 'y)] [z (fresh-sym 'z)])
                  `(all ,x (all ,y (all ,z (imp (and (pr Nat ,x) (pr Nat ,y) ,(Mul x y z)) ,(Add x y z))))))))
(define notes (emit-file! dir "L7-4-omega-laws" "the laws of Add and Mul for all x, y, z in omega, by induction (L:IndLem)"
                          all-laws! twin))
(write-new (build-path dir "L7-4-omega-laws.manifest.txt") (string-join notes "\n"))
