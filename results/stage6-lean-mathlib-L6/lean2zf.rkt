#lang racket/base
;; lean2zf.rkt -- lane L6 (Stage 6 of PMP-BUILDOUT-2026-10-09), 2026-10-09: Lean 4 / Mathlib statements about the
;; natural numbers as ZF theorems over omega, in the judge's format JDG1. Untrusted: both judges check every file.
;;
;; Pipeline:
;;   lean/L6Export.lean   (Lean, import Mathlib) writes the statements of the first slice: lean/export-nat.sexp
;;   leanstmt.rkt         reads them into the statement language of sigma1.rkt (plus nall), or refuses with a reason
;;   engine.rkt           derives each statement in ZF: omega, values of terms, bridges, closure, induction
;;   zfnat.rkt            the general theorems behind + and * on omega (sigma1.rkt's Add/Mul formulas, L:RecThm)
;;   scripts.rkt          the hints per statement
;; Usage:
;;   racket lean2zf.rkt emit DIR            write DIR/L6-nat.jdg, its index, manifest and mutants (DIR/mut)
;;   racket lean2zf.rkt judge DIR RESULTS   run both judges on DIR/*.jdg and DIR/mut/*.jdg
(require racket/list racket/string racket/match racket/file racket/port file/sha1
         "zfcore.rkt" "zfbatch.rkt" "zfnat.rkt" "engine.rkt" "leanstmt.rkt" "scripts.rkt")

(define EXPORT "C:/ClaudeOutput/pompetzki/lanes/L6/lean/export-nat.sexp")

(define (sha256-hex path) (call-with-input-file path (lambda (in) (bytes->hex-string (sha256-bytes in)))))
(define (write-new path text) (call-with-output-file path #:exists 'error (lambda (o) (write-string text o))) (void))

;; ---- build the batch: (values text rows) ; rows: (list name module status detail steps ms)
(define (build!)
  (load-base!)
  (reset-batch!)
  (define export (read-export EXPORT))
  (define rows '())
  (for ([s SCRIPTS])
    (match-define (list name script) s)
    (define e (assoc name export))
    (define t0 (current-milliseconds))
    (define st0 (hash-ref stats 'steps 0)) (define pst0 (hash-ref stats 'prelude-steps 0))
    (define (row! mod status detail)
      (define r (list name mod status detail (- (+ (hash-ref stats 'steps 0) (hash-ref stats 'prelude-steps 0)) st0 pst0) (- (current-milliseconds) t0)))
      (set! rows (cons r rows))
      (printf "~a ~a ~a ~a steps ~a ms ~a\n" status name mod (list-ref r 4) (list-ref r 5) detail) (flush-output))
    (cond
      [(not e) (row! "?" 'absent "not in the export")]
      [else
       (define-values (st why) (lean->stmt (caddr e)))
       (cond
         [(not st) (row! (cadr e) 'refused why)]
         [else
          (with-handlers ([exn:fail? (lambda (x) (abort-all!) (row! (cadr e) 'FAIL (car (string-split (exn-message x) "\n"))))])
            (parameterize ([current-error-port (if (getenv "L6QUIET") (open-output-nowhere) (current-error-port))])
              (prove-theorem! name st script))
            (row! (cadr e) 'ok (stmt->string st)))])]))
  (values (batch-text) (reverse rows)))

;; ---- mutated copies (as sigma1.rkt): (list tag text)
(define (mutants text prelude-flags)
  (define-values (rg ths) (read-jdg-text text))
  (define tv (list->vector ths))
  (define pv (list->vector prelude-flags))
  (define nth (vector-length tv))
  (define (with-thm i t) (structure-text rg (for/list ([x tv] [j (in-naturals)]) (if (= j i) t x))))
  (define (first-step pred)
    (for*/first ([i (in-range nth)] #:unless (vector-ref pv i)
                 [sv (in-value (list->vector (caddr (vector-ref tv i))))] [k (in-range (vector-length sv))]
                 #:when (pred (vector-ref sv k)))
      (list i k)))
  (define (replace-step i k f)
    (match-define (list st sig steps hyps) (vector-ref tv i))
    (with-thm i (list st sig (for/list ([s steps] [j (in-naturals)]) (if (= j k) (f s) s)) hyps)))
  (define last-i (sub1 nth))
  (match-define (list lst lsig lsteps lhyps) (vector-ref tv last-i))
  (match-define (list pst psig psteps phyps) (vector-ref tv (sub1 last-i)))
  (define suc-entry (hash-ref def-entry 18))
  (filter
   values
   (list
    (list "neg-final" (with-thm last-i (list (list 'n lst) lsig lsteps lhyps)))
    (list "swap-final" (with-thm last-i (list pst lsig lsteps lhyps)))
    (match (first-step (lambda (s) (eq? (car s) 'T)))
      [(list i k) (list "taut-goal" (replace-step i k (lambda (s) (list 'T (cadr s) (list 'n (caddr s))))))] [_ #f])
    (match (first-step (lambda (s) (and (eq? (car s) 'M) (not (= (cadr s) (caddr s))))))
      [(list i k) (list "mp-swap" (replace-step i k (lambda (s) (list 'M (caddr s) (cadr s)))))] [_ #f])
    (match (first-step (lambda (s) (eq? (car s) 'U)))
      [(list i k) (list "use-shift" (replace-step i k (lambda (s) (list 'U (add1 (cadr s)) (caddr s)))))] [_ #f])
    (match (first-step (lambda (s) (match s [(list 'Z _ (list 'i (list 'q a b) _)) (not (= a b))] [_ #f])))
      [(list i k) (list "leib-swap" (replace-step i k (lambda (s) (match s [(list 'Z a (list 'i (list 'q x y) r)) (list 'Z a (list 'i (list 'q y x) r))]))))] [_ #f])
    (match (first-step (lambda (s) (eq? (car s) 'E)))
      [(list i k) (list "exi-witness" (replace-step i k (lambda (s) (list 'E (add1 (cadr s)) (caddr s)))))] [_ #f])
    (match (first-step (lambda (s) (eq? (car s) 'L)))
      [(list i k) (list "exel-var" (replace-step i k (lambda (s) (list 'L (cadr s) (add1 (caddr s)) (cadddr s)))))] [_ #f])
    (match (first-step (lambda (s) (eq? (car s) 'Y)))
      [(list i k) (list "sep-instance" (replace-step i k (lambda (s) (match s [(list 'Y f) (list 'Y (list 'n f))]))))] [_ #f])
    (list "drop-step" (with-thm last-i (list lst lsig (drop-right lsteps 1) lhyps)))
    (list "registry-suc"
          (structure-text (for/list ([e rg] [i (in-naturals)])
                            (if (= i suc-entry)
                                (list (let loop ([d (car e)])
                                        (match d
                                          [(list 'a x) (list 'a (loop x))]
                                          [(list 'b x y) (list 'b (loop x) (loop y))]
                                          [(list 'd (list 'e 0 1) (list 'q 0 1)) (list 'd (list 'e 0 1) (list 'q 0 2))]
                                          [_ d]))
                                      (cadr e))
                                e))
                          ths)))))

(define (key->string k) (if (string? k) k (format "~s" k)))

(define (cmd-emit dir)
  (make-directory* (build-path dir "mut"))
  (define t0 (current-milliseconds))
  (define-values (text rows) (build!))
  (define build-ms (- (current-milliseconds) t0))
  (define file (build-path dir "L6-nat.jdg"))
  (write-new file text)
  (define-values (rg ths) (read-jdg-text text))
  (define keys (map car (reverse out-thms)))
  (define pflags (map caddr (reverse out-thms)))
  (define stmts (map cadddr (reverse out-thms)))
  (define export (read-export EXPORT))
  ;; the listing: index, kind, key, statement
  (write-new (build-path dir "L6-nat.index.txt")
             (string-join
              (for/list ([k keys] [p pflags] [s stmts] [i (in-naturals)])
                (define kind (cond [p "prelude"] [(string? k) "mathlib"] [else "lemma"]))
                (define mod (if (string? k) (cadr (assoc k export)) ""))
                (define lean (if (string? k) (let-values ([(st why) (lean->stmt (caddr (assoc k export)))]) (stmt->string st)) ""))
                (format "~a\t~a\t~a\t~a\t~a\t~a" (+ i NBASE) kind (key->string k) mod lean (if p "" (show s))))
              "\n"))
  (define checker (check-batch rg ths))
  (define ok-rows (filter (lambda (r) (eq? (caddr r) 'ok)) rows))
  (define manifest
    (list (format "L6-nat.jdg  bytes ~a  sha256 ~a" (file-size file) (sha256-hex file))
          (format "registry ~a; theorems ~a (prelude ~a, lemmas ~a, Mathlib statements ~a); steps ~a (prelude ~a)"
                  NBASE (length ths) (hash-ref stats 'prelude 0) (- (hash-ref stats 'theorems 0) (length ok-rows)) (length ok-rows)
                  (+ (hash-ref stats 'steps 0) (hash-ref stats 'prelude-steps 0)) (hash-ref stats 'prelude-steps 0))
          (format "build ~a ms; largest tautology test ~a calls; total tautology calls ~a" build-ms (hash-ref stats 'taut-max 0) (hash-ref stats 'taut-calls 0))
          (format "copy of the checker: ~a" checker)
          (format "scripts ~a: ok ~a, failed ~a, refused ~a, absent ~a" (length rows) (length ok-rows)
                  (length (filter (lambda (r) (eq? (caddr r) 'FAIL)) rows))
                  (length (filter (lambda (r) (eq? (caddr r) 'refused)) rows))
                  (length (filter (lambda (r) (eq? (caddr r) 'absent)) rows)))))
  (for ([m (mutants text pflags)])
    (match-define (list tag mtext) m)
    (define mf (build-path dir "mut" (string-append "L6-nat-" tag ".jdg")))
    (write-new mf mtext)
    (define-values (mrg mths) (read-jdg-text mtext))
    (set! manifest (append manifest (list (format "mutant ~a: copy of the checker ~a" tag (check-batch mrg mths))))))
  (write-new (build-path dir "manifest.txt") (string-join manifest "\n"))
  (write-new (build-path dir "scripts-run.txt")
             (string-join (for/list ([r rows]) (format "~a\t~a\t~a\t~a\t~a\t~a" (caddr r) (car r) (cadr r) (list-ref r 4) (list-ref r 5) (cadddr r))) "\n"))
  (for ([l manifest]) (printf "~a\n" l)))

;; ---- the judges
(define JUDGE-DIR "C:/ClaudeOutput/pompetzki/judge")
(define PMP "C:/ClaudeOutput/pompetzki/pompetzki.exe")
(define RACKET "C:/Program Files/Racket/racket.exe")
(define (run-cmd dir exe args)
  (parameterize ([current-directory dir])
    (define t0 (current-milliseconds))
    (define-values (sp out in err) (apply subprocess #f #f #f exe args))
    (close-output-port in)
    (define o (port->string out)) (define e (port->string err))
    (subprocess-wait sp)
    (close-input-port out) (close-input-port err)
    (list (subprocess-status sp) (- (current-milliseconds) t0) (string-trim (string-append o e)))))
(define (verdict out) (cond [(regexp-match? #rx"^ACCEPT" out) "ACCEPT"] [(regexp-match? #rx"REJECT" out) "REJECT"]
                            [(regexp-match? #rx"LIMIT" out) "LIMIT"] [else "OTHER"]))
(define (one-line s) (string-join (string-split s) " "))
(define (cmd-judge dir results)
  (define (jdgs d) (sort (for/list ([f (directory-list d #:build? #t)] #:when (regexp-match? #rx"[.]jdg$" (path->string f))) (path->string f)) string<?))
  (define files (append (jdgs dir) (jdgs (build-path dir "mut"))))
  (define o (open-output-file results #:exists 'error))
  (for ([f files])
    (define full (path->string (path->complete-path f)))
    (match-define (list e1 t1 o1) (run-cmd JUDGE-DIR PMP (list "judge-v3.pmp" full)))
    (match-define (list e2 t2 o2) (run-cmd JUDGE-DIR RACKET (list "racket/judge.rkt" full)))
    (define row (format "~a | pmp ~a exit ~a ~a ms | racket ~a exit ~a ~a ms | pmp: ~a | racket: ~a"
                        f (verdict o1) e1 t1 (verdict o2) e2 t2 (one-line o1) (one-line o2)))
    (displayln row o) (flush-output o)
    (printf "~a\n" row) (flush-output))
  (close-output-port o))

(module+ main
  (match (vector->list (current-command-line-arguments))
    [(list "emit" dir) (cmd-emit dir)]
    [(list "judge" dir results) (cmd-judge dir results)]
    [_ (printf "usage: racket lean2zf.rkt emit DIR | judge DIR RESULTS\n")]))
