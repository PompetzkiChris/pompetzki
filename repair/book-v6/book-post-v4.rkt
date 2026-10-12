#lang racket/base
;; book-post-v3.rkt. Portable ledger writer for fresh judge receipts. Posts judged JDG1 files to two new ledgers in lane L9's Book format:
;;   BOOK-1.0.ledger      one F record per file that both judges ACCEPT, then one B posting per theorem of it
;;   NEGATIVE-1.0.ledger  one N record per file that both judges REJECT
;;   verified-book-post --bundle DIR OUTDIR "DATE" INPUT ...
;; DATE is the text of `date "+%Y-%m-%d %H:%M:%S %Z"` (every clock time comes from date); it is the posting time of
;; every record of this run. FOLDER ... are searched for *.jdg; a file is posted only when RECEIPTS.tsv has its row
;; (make-receipts.rkt, 15 columns). The tool refuses to run when either ledger file exists (append-only: a ledger is
;; written once, CREATE_NEW, never overwritten); it exits 1 then and writes nothing.
;;
;; Format: lane L9's (lanes\L9\book.pmp header; lanes\L9\tools\bookcheck.rkt recomputes it). One record per line,
;; TAB-separated, the last field the chain: chain(i) = sha256(chain(i-1) as 64 hex digits, LF, the other fields joined
;; by TAB); chain(0) = 64 zeros, per ledger file. Records H (head), F, B, N, E (end) as in L9. The JDG1 reader, the
;; stmt / drv / registry hashes, the cites and the axiom trace (ax / def / hypent) below are copied from bookcheck.rkt
;; (lane L9, written separately from book.pmp, which agrees with book.pmp on 10,234 records: CHECK OK).
;; Q10 additions, appended before the chain so L9's fields keep their positions:
;;   F: stmt = sha256 of the file's theorem statements (JDG1 text, one per line, each ending in LF); ax / def / hypent =
;;      the union of the theorems' axiom traces; receipt = the receipt file(s); posted = DATE
;;   N: receipt, posted
;; "verdicts" names RECEIPTS.tsv (L9: its V file). A start or end time the receipt does not give is "-".
;; Files that are neither booked nor negative (no row, sha256 not the judged one, registry not a prefix of REG0,
;; counts differing from the judges' printed counts, mixed verdicts, unreadable JDG1) are listed on stdout as SUSPENSE.
;; grok-fixed copy: located in repair/grok-bot-results/book-verification, so the registry module path gains one "../".
(require racket/list racket/string racket/file racket/bytes racket/port racket/path json "../../judge/registry-auth-v4.rkt")
(provide post-receipts! (rename-out [parse-file inspect-jdg]))

(define PFX "")
(define AXN '#("Ext" "Pair" "Union" "Power" "Inf" "Found" "Choice"))

(define (hex bs) (apply string-append (for/list ([b bs]) (string-append (if (< b 16) "0" "") (number->string b 16)))))
(define (sha-hex bs) (hex (sha256-bytes bs)))
(define (canon bs)
  (string->bytes/utf-8
   (string-join
    (for/list ([t (string-split (bytes->string/latin-1 bs))])
      (if (regexp-match? #px"^[0-9]+$" t) (number->string (string->number t 10)) t)) " ")))
(define (pad n w) (let ([s (number->string n)]) (string-append (make-string (max 0 (- w (string-length s))) #\0) s)))

;; ------------------------------------------------------------------ JDG1 reader (bookcheck.rkt)
(struct rd (buf [pos #:mutable] lim))
(define (ws? b) (or (= b 32) (= b 9) (= b 10) (= b 13)))
(define (skip! r)
  (let loop () (when (and (< (rd-pos r) (rd-lim r)) (ws? (bytes-ref (rd-buf r) (rd-pos r))))
                 (set-rd-pos! r (add1 (rd-pos r))) (loop))))
(define (tok! r)
  (skip! r)
  (when (>= (rd-pos r) (rd-lim r)) (error 'jdg1 "unexpected end at ~a" (rd-pos r)))
  (define s (rd-pos r))
  (let loop () (when (and (< (rd-pos r) (rd-lim r)) (not (ws? (bytes-ref (rd-buf r) (rd-pos r)))))
                 (set-rd-pos! r (add1 (rd-pos r))) (loop)))
  (values s (rd-pos r)))
(define (num! r)
  (define-values (s e) (tok! r))
  (for/fold ([v 0]) ([i (in-range s e)])
    (define d (- (bytes-ref (rd-buf r) i) 48))
    (unless (<= 0 d 9) (error 'jdg1 "not a number at ~a" s))
    (+ (* v 10) d)))
(define (tag! r)
  (define-values (s e) (tok! r))
  (unless (= (- e s) 1) (error 'jdg1 "not a tag at ~a" s))
  (integer->char (bytes-ref (rd-buf r) s)))
(define (list! r) (define n (num! r)) (for/list ([_ (in-range n)]) (num! r)))
(define (form! r)
  (case (tag! r)
    [(#\e #\q) (num! r) (num! r)]
    [(#\p) (num! r) (list! r)]
    [(#\n #\a #\x) (form! r)]
    [(#\i #\k #\d #\b) (form! r) (form! r)]
    [else (error 'jdg1 "form tag at ~a" (rd-pos r))])
  (void))
(define (step! r on-use)
  (case (tag! r)
    [(#\U) (on-use (num! r)) (list! r)]
    [(#\S) (num! r) (list! r)]
    [(#\G #\M) (num! r) (num! r)]
    [(#\T) (list! r) (form! r)]
    [(#\E #\V) (num! r) (form! r)]
    [(#\L #\H) (num! r) (num! r) (form! r)]
    [(#\Z) (form! r) (form! r)]
    [(#\Y) (form! r)]
    [else (error 'jdg1 "step tag at ~a" (rd-pos r))])
  (void))
(define (read-registry r)
  (define-values (s e) (tok! r))
  (unless (equal? (subbytes (rd-buf r) s e) #"JDG1") (error 'jdg1 "no JDG1"))
  (unless (char=? (tag! r) #\R) (error 'jdg1 "no R"))
  (define n (num! r))
  (for/list ([_ (in-range n)])
    (skip! r)
    (define a (rd-pos r))
    (form! r) (list! r)
    (canon (subbytes (rd-buf r) a (rd-pos r)))))

(define (ranges bits lo hi)
  (define runs
    (let loop ([i lo] [run #f] [acc '()])
      (cond [(>= i hi) (reverse (if run (cons (cons run (sub1 i)) acc) acc))]
            [(bitwise-bit-set? bits i) (loop (add1 i) (or run i) acc)]
            [run (loop (add1 i) #f (cons (cons run (sub1 i)) acc))]
            [else (loop (add1 i) #f acc)])))
  (string-join (for/list ([p runs]) (if (= (car p) (cdr p)) (number->string (car p)) (format "~a-~a" (car p) (cdr p)))) ","))
(define (popcount-range bits lo hi) (for/sum ([i (in-range lo hi)]) (if (bitwise-bit-set? bits i) 1 0)))
(define (trace-fields bits n0)
  (define axs (for/list ([i (in-range (min 7 n0))] #:when (bitwise-bit-set? bits i)) (vector-ref AXN i)))
  (define dhi (min 677 n0))
  (define dc (if (> dhi 7) (popcount-range bits 7 dhi) 0))
  (define hc (if (> n0 677) (popcount-range bits 677 n0) 0))
  (list (if (null? axs) "ax -" (string-append "ax " (string-join axs " ")))
        (if (= dc 0) "def 0 -" (format "def ~a ~a" dc (ranges bits 7 dhi)))
        (if (= hc 0) "hypent -" (string-append "hypent " (ranges bits 677 n0)))))
(define (source-of path)
  (define kx (let loop ([i (sub1 (string-length path))])
               (cond [(< i 0) -1] [(memv (string-ref path i) '(#\\ #\/)) i] [else (loop (sub1 i))])))
  (define pfl (string-length PFX))
  (define st (if (and (>= kx pfl) (string=? (substring path 0 pfl) PFX)) pfl 0))
  (define s (if (< kx st) "" (substring path st kx)))
  (if (string=? s "") "." s))

;; ------------------------------------------------------------------ parse one accepted file
;; returns (values n0 reghex prefix? m total thms) ; thms: (list j a se te ns cites tr hyps)
(define ref-entries #f)
(define (parse-file bs)
  (define r (rd bs 0 (bytes-length bs)))
  (define entries (read-registry r))
  (define n0 (length entries))
  (define prefix? (authenticated-token-prefix? (map (lambda (b) (string-split (bytes->string/latin-1 b))) entries)))
  (define reghex (sha-hex (bytes-join entries #" ")))
  (unless (char=? (tag! r) #\T) (error 'jdg1 "no T"))
  (define m (num! r))
  (define traces (make-vector m 0))
  (define thms
    (for/list ([j (in-range m)])
      (skip! r)
      (define a (rd-pos r))
      (form! r)
      (define se (rd-pos r))
      (list! r)
      (define ns (num! r))
      (define cites '())
      (define tr 0)
      (for ([_ (in-range ns)])
        (step! r (lambda (u)
                   (unless (memv u cites)
                     (set! cites (cons u cites))
                     (set! tr (bitwise-ior tr (if (< u n0) (arithmetic-shift 1 u) (vector-ref traces (- u n0)))))))))
      (define hyps (list! r))
      (define te (rd-pos r))
      (vector-set! traces j tr)
      (list j a se te ns (reverse cites) tr hyps)))
  (skip! r)
  (unless (= (rd-pos r) (rd-lim r)) (error 'jdg1 "text after the last theorem"))
  (values n0 reghex prefix? m (for/sum ([t thms]) (list-ref t 4)) thms))

(define (ints s) (map string->number (regexp-match* #px"\\d+" s)))
(define (counts-ok? out n0 m total)
  (define v (ints out))
  (and (>= (length v) 4) (equal? (take-right v 4) (list n0 m total (+ n0 m)))))

;; ------------------------------------------------------------------ ledger writer
(define (chain-line o head fields)
  (define body (string-join fields "\t"))
  (define new (sha-hex (bytes-append (string->bytes/latin-1 head) #"\n" (string->bytes/utf-8 body))))
  (write-bytes (string->bytes/utf-8 (string-append body "\t" new "\n")) o)
  new)

(define (verd v with-output?) ; v = (list word exit start end ms out)
  (string-append (list-ref v 0) " exit " (list-ref v 1) " " (list-ref v 2) " - " (list-ref v 3) " " (list-ref v 4) " ms"
                 (if with-output? (string-append " " (list-ref v 5)) "")))

(define (row-key p) (string-downcase (string-replace p "/" "\\"))) ; grok-fixed: one normalisation for rows and files
(define (resolved-exec)                                               ; grok-fixed: exec-file may be a bare PATH name
  (define e (find-system-path 'exec-file))
  (define-values (d n _) (split-path e))
  (or (and (eq? d 'relative) (find-executable-path e)) (path->complete-path e)))
(define self-source                                                   ; grok-fixed: hash the module actually loaded
  (let ([s (variable-reference->module-source (#%variable-reference))]) (and (path? s) s)))
(define (hex64? s) (and (string? s) (regexp-match? #px"^[0-9a-f]{64}$" s)))
(define (word-of text code)
  (define a (regexp-match? #px"\\bACCEPT\\b" text)) (define r (regexp-match? #px"\\bREJECT\\b" text))
  (cond [(and (equal? code 0) a (not r)) "ACCEPT"] [(and (equal? code 1) r (not a)) "REJECT"] [else "UNKNOWN"]))
;; grok-fixed: every receipt row must be backed by run-metadata.json in OUTDIR: same snapshot, sha256 before and after,
;; unchanged, verdict and exit per judge, and logged stdout/stderr whose SHA-256 matches and whose text re-classifies
;; to the same verdict. Rows lacking such backing are SUSPENSE.
(define (metadata-backing outdir)
  (define p (build-path outdir "run-metadata.json"))
  (define meta (and (file-exists? p) (with-handlers ([exn:fail? (lambda (e) #f)]) (call-with-input-file p read-json))))
  (define h (make-hash))
  (when (hash? meta)
    (for ([r (hash-ref meta 'runs '())] #:when (hash? r)) (hash-set! h (row-key (format "~a" (hash-ref r 'snapshot ""))) r)))
  h)
(define (backed? run c)
  (define (judge-ok? j word code)
    (and (hash? j) (equal? (hash-ref j 'verdict #f) word) (equal? (format "~a" (hash-ref j 'exit_code #f)) code)
         (for/and ([k '(stdout stderr)] [hk '(stdout_sha256 stderr_sha256)])
           (define f (hash-ref j k #f))
           (and (string? f) (file-exists? f) (equal? (sha-hex (file->bytes f)) (hash-ref j hk #f))))
         (let ([cmd (hash-ref j 'command '())]) (and (pair? cmd) (equal? (last cmd) (list-ref c 0))))
         (equal? word (word-of (bytes->string/utf-8 (bytes-append (file->bytes (hash-ref j 'stdout)) (file->bytes (hash-ref j 'stderr))) #\?)
                               (string->number code)))))
  (and (hash? run) (eq? (hash-ref run 'unchanged #f) #t)
       (equal? (hash-ref run 'input_sha256_before #f) (list-ref c 4))
       (equal? (hash-ref run 'input_sha256_after #f) (list-ref c 4))
       (judge-ok? (hash-ref run 'pmp #f) (list-ref c 1) (list-ref c 5))
       (judge-ok? (hash-ref run 'racket #f) (list-ref c 2) (list-ref c 10))))

(define (post-receipts! tsv outdir date folders)
  (define book (build-path outdir "BOOK-1.0.ledger"))
  (define neg (build-path outdir "NEGATIVE-1.0.ledger"))
  (when (or (file-exists? book) (file-exists? neg))
    (eprintf "REFUSED: ~a exists; ledgers are append-only and are never overwritten\n" (if (file-exists? book) book neg))
    (exit 1))
  (define tsvname (let-values ([(d n _) (split-path tsv)]) (path->string n)))
  ;; receipts
  (define rows (make-hash))
  (for ([ln (cdr (file->lines tsv))])
    (define c (string-split ln "\t" #:trim? #f))
    (unless (= (length c) 15) (error 'book-post "RECEIPTS row has ~a columns: ~a" (length c) (car c)))
    (hash-set! rows (row-key (car c)) c))
  ;; files
  (define files
    (sort (remove-duplicates
           (for*/list ([fd folders] [x (if (file-exists? fd) (list (string->path fd)) (in-directory fd))] #:when (regexp-match? #rx"[.]jdg$" (path->string x)))
             (path->string (simplify-path (path->complete-path x)))))
          string<?))
  (define source-path self-source)
  (define backing (metadata-backing outdir))
  (define self-sha (if (and source-path (file-exists? source-path))
                       (sha-hex (file->bytes source-path)) "embedded-in-executable"))
  (define racket-sha (sha-hex (file->bytes (resolved-exec))))
  (define suspense '())
  (define (suspend! p why) (set! suspense (cons (cons p why) suspense)))
  (define used (make-hash))
  (define ob (open-output-file book #:exists 'error))
  (define on (open-output-file neg #:exists 'error))
  (define hb (make-string 64 #\0)) (define hn (make-string 64 #\0))
  (define (head-fields name)
    (list "H000001" (string-append "segment " name) "previous - -" (string-append "opened " date)
          (string-append "book-post-v4.rkt " self-sha) (string-append "process-image " racket-sha)
          (string-append "run-metadata.json "
                         (let ([p (build-path outdir "run-metadata.json")])
                           (if (file-exists? p) (sha-hex (file->bytes p)) "-")))))
  (set! hb (chain-line ob hb (head-fields "BOOK-1.0.ledger")))
  (set! hn (chain-line on hn (head-fields "NEGATIVE-1.0.ledger")))
  (define nF 0) (define nB 0) (define nN 0) (define nrecB 1) (define nrecN 1)
  (define nproved 0) (define nqual 0) (define nsteps 0)
  (define stmt-first (make-hash))
  (for ([path files])
    (define key (row-key path))
    (define c (hash-ref rows key #f))
    (cond
      [(not c) (suspend! path "no receipt row")]
      [else
       (hash-set! used key #t)
       (define bs (file->bytes path))
       (define sha (sha-hex bs))
       (define pv (list (list-ref c 1) (list-ref c 5) (list-ref c 6) (list-ref c 7) (list-ref c 8) (list-ref c 9)))
       (define rv (list (list-ref c 2) (list-ref c 10) (list-ref c 11) (list-ref c 12) (list-ref c 13) (list-ref c 14)))
       (define receipt (list-ref c 3))
       (define judged (list-ref c 4))
       (cond
         [(not (and (hex64? judged) (equal? judged sha))) (suspend! path (format "sha256 ~a is not the judged ~a" sha judged))]
         [(not (backed? (hash-ref backing key #f) c)) (suspend! path "receipt row is not backed by run-metadata.json and its judge logs")]
         [(and (equal? (car pv) "ACCEPT") (equal? (car rv) "ACCEPT") (equal? (list-ref c 5) "0") (equal? (list-ref c 10) "0"))
          (define parsed
            (with-handlers ([exn:fail? (lambda (e) (suspend! path (string-append "JDG1: " (exn-message e))) #f)])
              (call-with-values (lambda () (parse-file bs)) list)))
          (when parsed
            (define-values (n0 reghex prefix? m total thms) (apply values parsed))
            (cond
              [(not prefix?) (suspend! path "registry is not a prefix of REG0 (replay-all.jdg)")]
              [(not (and (counts-ok? (list-ref c 9) n0 m total) (counts-ok? (list-ref c 14) n0 m total)))
               (suspend! path (format "counts ~a ~a ~a ~a differ from the judges' printed counts" n0 m total (+ n0 m)))]
              [else
               (set! nF (add1 nF))
               (define bfirst (add1 nB))
               (define src (source-of path))
               (define union (for/fold ([u 0]) ([t thms]) (bitwise-ior u (list-ref t 6))))
               (define stmts (sha-hex (apply bytes-append (for/list ([t thms]) (bytes-append (canon (subbytes bs (list-ref t 1) (list-ref t 2))) #"\n")))))
               (set! hb (chain-line ob hb
                          (append
                           (list (format "F~a" (pad nF 6)) (string-append "file " path) (string-append "sha256 " sha)
                                 (format "bytes ~a" (bytes-length bs)) (string-append "source " src)
                                 (format "registry ~a prefix ~a" n0 reghex) (format "theorems ~a" m) (format "steps ~a" total)
                                 (string-append "pmp " (verd pv #f)) (string-append "racket " (verd rv #f)) (string-append "verdicts " tsvname)
                                 (format "postings B~a-B~a" (pad bfirst 7) (pad (+ bfirst m -1) 7))
                                 (string-append "stmt " stmts))
                           (trace-fields union n0)
                           (list (string-append "receipt " receipt) (string-append "posted " date)))))
               (set! nrecB (add1 nrecB))
               (for ([t thms])
                 (define-values (j a se te ns cites tr hyps) (apply values t))
                 (define bn (+ bfirst j))
                 (define st (sha-hex (canon (subbytes bs a se))))
                 (define first (hash-ref stmt-first st #f))
                 (unless first (hash-set! stmt-first st bn))
                 (set! hb (chain-line ob hb
                            (append
                             (list (format "B~a" (pad bn 7)) (format "F~a" (pad nF 6)) (format "thm ~a" j) (format "entry ~a" (+ n0 j))
                                   (if (null? hyps) "Proved" "Qualified")
                                   (string-append "stmt " st)
                                   (string-append "drv " (sha-hex (canon (subbytes bs a te))))
                                   (format "steps ~a" ns)
                                   (if (null? hyps) "hyps -" (string-append "hyps " (string-join (map number->string hyps) ",")))
                                   (if first (string-append "first B" (pad first 7)) "first -")
                                   (if (null? cites) "cites -"
                                       (string-append "cites " (string-join (for/list ([u cites]) (if (< u n0) (format "R~a" u) (format "B~a" (pad (+ bfirst (- u n0)) 7)))) " "))))
                             (trace-fields tr n0)
                             (list (string-append "file " sha) (string-append "registry " reghex) (string-append "source " src)
                                   (string-append "pmp ACCEPT " (list-ref pv 3)) (string-append "racket ACCEPT " (list-ref rv 3))))))
                 (set! nrecB (add1 nrecB))
                 (if (null? hyps) (set! nproved (add1 nproved)) (set! nqual (add1 nqual))))
               (set! nB (+ nB m))
               (set! nsteps (+ nsteps total))]))]
         [(and (equal? (car pv) "REJECT") (equal? (car rv) "REJECT"))
          (set! nN (add1 nN))
          (set! hn (chain-line on hn
                     (list (format "N~a" (pad nN 6)) "Rejected" (string-append "file " path) (string-append "sha256 " sha)
                           (format "bytes ~a" (bytes-length bs)) (string-append "source " (source-of path))
                           (string-append "pmp " (verd pv #t)) (string-append "racket " (verd rv #t)) (string-append "verdicts " tsvname)
                           (string-append "receipt " receipt) (string-append "posted " date))))
          (set! nrecN (add1 nrecN))]
         [else (suspend! path (format "verdicts pmp ~a exit ~a, racket ~a exit ~a" (car pv) (list-ref c 5) (car rv) (list-ref c 10)))])]))
  (for ([(k c) rows] #:unless (hash-ref used k #f)) (suspend! (car c) "receipt row, but the file is not in the folders"))
  (set! hb (chain-line ob hb (list "E000001" "segment BOOK-1.0.ledger" (format "records ~a" nrecB)
                                   (if (= nF 0) "F -" (format "F000001-F~a" (pad nF 6)))
                                   (if (= nB 0) "B -" (format "B0000001-B~a" (pad nB 7))) "N -" "S -" "C -" (string-append "closed " date))))
  (set! hn (chain-line on hn (list "E000001" "segment NEGATIVE-1.0.ledger" (format "records ~a" nrecN) "F -" "B -"
                                   (if (= nN 0) "N -" (format "N000001-N~a" (pad nN 6))) "S -" "C -" (string-append "closed " date))))
  (close-output-port ob) (close-output-port on)
  (printf "files found ~a, receipt rows ~a\n" (length files) (hash-count rows))
  (printf "BOOK-1.0.ledger: F ~a B ~a (Proved ~a, Qualified ~a) steps ~a distinct statements ~a records ~a chain head ~a\n"
          nF nB nproved nqual nsteps (hash-count stmt-first) (add1 nrecB) hb)
  (printf "NEGATIVE-1.0.ledger: N ~a records ~a chain head ~a\n" nN (add1 nrecN) hn)
  (printf "SUSPENSE ~a\n" (length suspense))
  (for ([s (reverse suspense)]) (printf "  SUSPENSE ~a: ~a\n" (car s) (cdr s)))
  (if (null? suspense) 0 3))

(module+ main
  (eprintf "Use verified-book-post.rkt to run the judges and create a new ledger.\n")
  (exit 2))
