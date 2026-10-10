#lang racket/base
;; book-merge.rkt -- book-master (Abschluss 1.0). Merges the shipped Book and the Book ledger pairs that MERGE-PLAN.tsv
;; marks MERGE into one master Book, lane L9's journal format, as SPEC.md (same folder's parent) describes.
;;   racket book-merge.rkt MERGE-PLAN.tsv inventory.tsv OUTDIR "DATE"
;; DATE is the text of `date "+%Y-%m-%d %H:%M:%S %Z"`: the opened/closed time of every segment of this run.
;; Append-only: OUTDIR\book\J<k>.txt files are created new (an existing name stops the tool); when OUTDIR\book already
;; holds segments, their chain is re-verified, the run continues the chain and the numbering after the last one, and
;; sources already merged (ledger sha256 in an H record) are not merged again. Nothing existing is changed.
;; Writes OUTDIR\book\J<k>.txt, OUTDIR\DUPLICATES[-from-J<k>].tsv, OUTDIR\CONFLICTS[-from-J<k>].tsv and prints counts.
;; Every source is read twice: a first pass recomputes its chain (head and record count go into the H record), the
;; second pass recomputes it again while merging and stops on any difference; the file's sha256 must equal the plan's.
;; Strings hold the source bytes one-to-one (latin-1 decoding), so copied fields are written back byte for byte.
(require racket/list racket/string racket/file racket/port)

(define SHIPPED-DIR "C:\\ClaudeOutput\\pompetzki\\release-1.0\\handin\\queue\\Q23-book\\book")
(define L9-VERDICTS "C:\\ClaudeOutput\\pompetzki\\lanes\\L9\\verdicts\\")
(define AXN '("Ext" "Pair" "Union" "Power" "Inf" "Found" "Choice"))
(define ZERO (make-string 64 #\0))

(define (hex bs) (apply string-append (for/list ([b bs]) (string-append (if (< b 16) "0" "") (number->string b 16)))))
(define (sha256-file f) (call-with-input-file f (lambda (in) (hex (sha256-bytes in)))))
(define (pad n w) (let ([s (number->string n)]) (string-append (make-string (max 0 (- w (string-length s))) #\0) s)))
(define (L s) (string->bytes/latin-1 s))
(define (chain-of prev body) (hex (sha256-bytes (bytes-append (L prev) #"\n" (L body)))))
(define (split-tab s) (string-split s "\t" #:trim? #f))
(define (fld fs pfx) (for/first ([f fs] #:when (string-prefix? f pfx)) (substring f (string-length pfx))))
(define (fail fmt . a) (raise-user-error 'book-merge (apply format fmt a)))

;; lines of a file as latin-1 strings (LF ends; a CR is an error)
(define (for-lines path proc)
  (call-with-input-file path
    (lambda (in)
      (let loop ([n 1])
        (define b (read-bytes-line in 'linefeed))
        (unless (eof-object? b)
          (when (regexp-match? #rx#"\r" b) (fail "~a line ~a: CR byte" path n))
          (proc (bytes->string/latin-1 b) n)
          (loop (add1 n)))))))
;; record = (fields-without-chain chain)
(define (rec-of line)
  (define fs (split-tab line))
  (values (drop-right fs 1) (last fs)))

;; first pass over one source (list of files read as one chain): -> (values head records)
(define (prepass files)
  (define head ZERO) (define n 0)
  (for ([f files])
    (for-lines f (lambda (line k)
                   (define-values (fs ch) (rec-of line))
                   (define want (chain-of head (string-join fs "\t")))
                   (unless (equal? want ch) (fail "~a line ~a: chain ~a, recomputed ~a" f k ch want))
                   (set! head ch) (set! n (add1 n)))))
  (values head n))

;; ------------------------------------------------------------------ trace union (shipped Book F records)
(define (parse-ranges s) ; "7-23,25" -> list of ints ; "-" -> '()
  (if (equal? s "-") '()
      (append* (for/list ([p (string-split s ",")])
                 (define m (regexp-match #px"^([0-9]+)-([0-9]+)$" p))
                 (if m (for/list ([i (in-range (string->number (cadr m)) (add1 (string->number (caddr m))))]) i)
                     (list (string->number p)))))))
(define (render-ranges ints)
  (define xs (sort (remove-duplicates ints) <))
  (let loop ([xs xs] [acc '()])
    (cond [(null? xs) (string-join (reverse acc) ",")]
          [else (define a (car xs))
                (define-values (b rest) (let run ([b a] [r (cdr xs)]) (if (and (pair? r) (= (car r) (add1 b))) (run (car r) (cdr r)) (values b r))))
                (loop rest (cons (if (= a b) (number->string a) (format "~a-~a" a b)) acc))])))
(define (trace-union bfields-list) ; B records as field lists (L9 positions 11 ax, 12 def, 13 hypent)
  (define axs (make-hash)) (define defs '()) (define hyps '())
  (for ([b bfields-list])
    (for ([a (cdr (string-split (list-ref b 11) " "))] #:unless (equal? a "-")) (hash-set! axs a #t))
    (define d (string-split (list-ref b 12) " ")) ; "def" count ranges
    (set! defs (append (parse-ranges (caddr d)) defs))
    (set! hyps (append (parse-ranges (cadr (string-split (list-ref b 13) " "))) hyps)))
  (define ax-names (filter (lambda (a) (hash-ref axs a #f)) AXN))
  (define dd (remove-duplicates defs))
  (list (if (null? ax-names) "ax -" (string-append "ax " (string-join ax-names " ")))
        (if (null? dd) "def 0 -" (format "def ~a ~a" (length dd) (render-ranges dd)))
        (if (null? hyps) "hypent -" (string-append "hypent " (render-ranges hyps)))))

;; ------------------------------------------------------------------ master state
(define next (make-hash))           ; kind -> next number
(define (take-id! kind) (define n (hash-ref next kind 1)) (hash-set! next kind (add1 n)) n)
(define (id kind n) (string-append kind (pad n (if (equal? kind "B") 7 6))))
(define bkey (make-hash))           ; stmt+drv -> master B id string
(define stmt-first (make-hash))     ; stmt -> master B id string
(define fsha (make-hash))           ; file sha -> master F id
(define nsha (make-hash))           ; -> master N id
(define ssha (make-hash))           ; -> master S id
(define merged-sources (make-hash)) ; ledger sha256 (or "SHIPPED") -> segment
(define head ZERO)
(define seg-k 0)
(define prev-rel #f)
(define self-sha (sha256-file (path->string (syntax-source #'here))))
(define racket-sha (sha256-file (path->string (find-system-path 'exec-file))))

;; load an existing master (append mode)
(define (load-existing dir)
  (let loop ([k 1])
    (define rel (format "book/J~a.txt" (pad k 6)))
    (define p (build-path dir rel))
    (when (file-exists? p)
      (for-lines p
        (lambda (line n)
          (define-values (fs ch) (rec-of line))
          (define want (chain-of head (string-join fs "\t")))
          (unless (equal? want ch) (fail "existing ~a line ~a: chain differs" rel n))
          (set! head ch)
          (define tag (car fs)) (define kind (substring tag 0 1)) (define num (string->number (substring tag 1)))
          (unless (= num (hash-ref next kind 1)) (fail "existing ~a line ~a: ~a out of sequence" rel n tag))
          (hash-set! next kind (add1 num))
          (case kind
            [("H") (for ([f (list (list-ref fs 7) (list-ref fs 8))])
                     (define m (regexp-match #px" sha256 ([0-9a-f]{64}) " f))
                     (when m (hash-set! merged-sources (cadr m) rel)))
                   (when (equal? (list-ref fs 6) "source SHIPPED")
                     (when (regexp-match? #px"B PASS B[0-9]" (list-ref fs 9)) (hash-set! merged-sources "SHIPPED-B" rel))
                     (when (regexp-match? #px"N PASS N[0-9]" (list-ref fs 9)) (hash-set! merged-sources "SHIPPED-N" rel)))]
            [("F") (hash-set! fsha (fld fs "sha256 ") tag)]
            [("B") (define st (fld fs "stmt ")) (hash-ref! stmt-first st tag)
                   (hash-set! bkey (string-append st (fld fs "drv ")) tag)]
            [("N") (hash-set! nsha (fld fs "sha256 ") tag)]
            [("S") (hash-set! ssha (fld fs "sha256 ") tag)]
            [else (void)])))
      (set! seg-k k) (set! prev-rel rel)
      (loop (add1 k)))))

;; ------------------------------------------------------------------ writing
(define out-dir #f)
(define date-text #f)
(define dup-port #f)
(define conf-port #f)
(define seg-port #f)
(define seg-count #f)   ; records written in the segment (H included)
(define seg-ids #f)     ; kind -> (first . last)
(define seg-dups #f)    ; kind -> count
(define totals (make-hash))
(define (emit! fields)
  (define body (string-join fields "\t"))
  (define ch (chain-of head body))
  (write-bytes (L body) seg-port) (write-bytes #"\t" seg-port) (write-bytes (L ch) seg-port) (write-bytes #"\n" seg-port)
  (set! head ch)
  (set! seg-count (add1 seg-count))
  (define kind (substring (car fields) 0 1))
  (define num (string->number (substring (car fields) 1)))
  (unless (member kind '("H" "E"))
    (hash-update! seg-ids kind (lambda (p) (if p (cons (car p) num) (cons num num))) #f)
    (hash-update! totals kind add1 0)))
(define (dup! kind pair src-id src-chain key master)
  (hash-update! seg-dups kind add1 0)
  (hash-update! totals (string-append "dup-" kind) add1 0)
  (fprintf dup-port "~a\n" (string-join (list kind pair src-id src-chain key master) "\t")))
(define (conflict! . parts) (hash-update! totals "conflicts" add1 0) (fprintf conf-port "~a\n" (string-join parts "\t")))

(define (open-segment! source-fields)
  (set! seg-k (add1 seg-k))
  (define rel (format "book/J~a.txt" (pad seg-k 6)))
  (set! seg-port (open-output-file (build-path out-dir rel) #:exists 'error))
  (set! seg-count 0) (set! seg-ids (make-hash)) (set! seg-dups (make-hash))
  (define prev (if prev-rel (format "previous ~a ~a" prev-rel (sha256-file (build-path out-dir prev-rel))) "previous - -"))
  (emit! (append (list (id "H" (take-id! "H")) (string-append "segment " rel) prev (string-append "opened " date-text)
                       (string-append "book-merge.rkt " self-sha) (string-append "racket.exe " racket-sha))
                 source-fields))
  rel)
(define (close-segment! rel)
  (define (rng k) (let ([p (hash-ref seg-ids k #f)]) (if p (format "~a-~a" (id k (car p)) (id k (cdr p))) (string-append k " -"))))
  (define records seg-count)
  (emit! (list (id "E" (take-id! "E")) (string-append "segment " rel) (format "records ~a" records)
               (rng "F") (rng "B") (rng "N") (rng "S") "C -" (string-append "closed " date-text)
               (format "duplicates F ~a B ~a N ~a S ~a" (hash-ref seg-dups "F" 0) (hash-ref seg-dups "B" 0) (hash-ref seg-dups "N" 0) (hash-ref seg-dups "S" 0))))
  (close-output-port seg-port)
  (set! prev-rel rel))

;; one F group: F fields (source, chain dropped), its chain, and its B records ((fields . chain) ...)
;; derive: procedure F-fields B-list -> list of Q10 fields 12..17 (stmt ax def hypent receipt posted)
(define (book-group! pair f fch bs derive bmap)
  (define sha (fld f "sha256 "))
  (define m (length bs))
  ;; decide each posting in order: (b . #f) = new, (b . master-id) = duplicate of a booked posting or of an earlier
  ;; new posting of this same file (two theorems of one file with the same stmt and drv)
  (define local (make-hash))
  (define decisions
    (let loop ([bs bs] [n (hash-ref next "B" 1)] [acc '()])
      (cond
        [(null? bs) (reverse acc)]
        [else
         (define fs (car (car bs)))
         (define key (string-append (fld fs "stmt ") (fld fs "drv ")))
         (define seen (or (hash-ref bkey key #f) (hash-ref local key #f)))
         (cond [seen (loop (cdr bs) n (cons (cons (car bs) seen) acc))]
               [else (hash-set! local key (id "B" n)) (loop (cdr bs) (add1 n) (cons (cons (car bs) #f) acc))])])))
  (define fresh (for/sum ([d decisions]) (if (cdr d) 0 1)))
  (define seenF (hash-ref fsha sha #f))
  (cond
    [(and seenF (= fresh 0))
     (dup! "F" pair (car f) fch (string-append "sha256 " sha) seenF)
     (for ([d decisions])
       (define b (car d))
       (hash-set! bmap (car (car b)) (cdr d))
       (dup! "B" pair (car (car b)) (cdr b) (format "stmt ~a drv ~a" (fld (car b) "stmt ") (fld (car b) "drv ")) (cdr d)))]
    [else
     (when seenF (conflict! "F" pair (car f) (string-append "sha256 " sha) (format "already booked as ~a; ~a new postings, booked again" seenF fresh)))
     (define fnum (take-id! "F"))
     (define fid (id "F" fnum))
     (unless seenF (hash-set! fsha sha fid))
     (when (hash-ref nsha sha #f) (conflict! "F" pair (car f) (string-append "sha256 " sha) (format "accepted here, rejected as ~a" (hash-ref nsha sha))))
     ;; assign master B ids to the fresh postings, in order
     (define bfirst (hash-ref next "B" 1))
     (define assigned
       (let loop ([ds decisions] [n bfirst] [acc '()])
         (cond [(null? ds) (reverse acc)]
               [(cdr (car ds)) (loop (cdr ds) n (cons (cons (car (car ds)) (cdr (car ds))) acc))]
               [else (loop (cdr ds) (add1 n) (cons (cons (car (car ds)) (id "B" n)) acc))])))
     (define extra (derive f (map car bs)))
     (define pmp-text (substring (list-ref f 8) 4))
     (define rkt-text (substring (list-ref f 9) 7))
     (define receipt (list-ref extra 4)) ; the F's field 16, "receipt <path>"
     (unless (string-prefix? receipt "receipt ") (fail "~a ~a: field 16 is not a receipt: ~a" pair (car f) receipt))
     (emit! (append (list fid) (take (cdr f) 10)
                    (list (if (= fresh 0) "postings -" (format "postings ~a-~a" (id "B" bfirst) (id "B" (+ bfirst fresh -1)))))
                    extra
                    (list (format "booked ~a duplicates ~a" fresh (- m fresh)) (format "from ~a ~a" (car f) fch))))
     (for ([a assigned] [d decisions])
       (define b (car a)) (define fs (car b)) (define mid (cdr a))
       (define src-id (car fs))
       (cond
         [(cdr d) ; duplicate
          (hash-set! bmap src-id mid)
          (dup! "B" pair src-id (cdr b) (format "stmt ~a drv ~a" (fld fs "stmt ") (fld fs "drv ")) mid)]
         [else
          (define n (take-id! "B"))
          (unless (equal? (id "B" n) mid) (fail "internal: B numbering ~a vs ~a" (id "B" n) mid))
          (hash-set! bmap src-id mid)
          (define st (fld fs "stmt "))
          (define key (string-append st (fld fs "drv ")))
          (hash-set! bkey key mid)
          (define first (hash-ref stmt-first st #f))
          (unless first (hash-set! stmt-first st mid))
          (define cites
            (let ([c (list-ref fs 10)])
              (if (equal? c "cites -") c
                  (string-append "cites "
                                 (string-join (for/list ([u (cdr (string-split c " "))])
                                                (cond [(regexp-match? #px"^R[0-9]+$" u) u]
                                                      [(hash-ref bmap u #f)]
                                                      [else (fail "~a ~a cites ~a, not posted before it" pair src-id u)]))
                                              " ")))))
          (emit! (append (list mid fid) (take (list-tail fs 2) 7)
                         (list (if first (string-append "first " first) "first -") cites)
                         (take (list-tail fs 11) 8)
                         (list (string-append "pmp-verdict " pmp-text) (string-append "racket-verdict " rkt-text)
                               (list-ref f 10) receipt (format "from ~a ~a" src-id (cdr b)))))]))]))

(define (book-neg! pair kind fs ch)
  ;; kind "N" or "S"; fs: 12 master-shaped fields except id ... built by the caller (fields 1..10)
  (define sha (fld fs "sha256 "))
  (define table (if (equal? kind "N") nsha ssha))
  (define seen (hash-ref table sha #f))
  (cond
    [seen (dup! kind pair (car fs) ch (string-append "sha256 " sha) seen)]
    [else
     (define mid (id kind (take-id! kind)))
     (hash-set! table sha mid)
     (when (and (equal? kind "N") (hash-ref fsha sha #f))
       (conflict! "N" pair (car fs) (string-append "sha256 " sha) (format "rejected here, accepted as ~a" (hash-ref fsha sha))))
     (emit! (append (list mid) (cdr fs) (list (format "from ~a ~a" (car fs) ch))))]))

;; ------------------------------------------------------------------ sources
;; stream a source's records, re-verifying the chain; calls (on-rec fields chain) for every record
(define (stream-source files on-rec)
  (define h ZERO)
  (for ([f files])
    (for-lines f (lambda (line k)
                   (define-values (fs ch) (rec-of line))
                   (define want (chain-of h (string-join fs "\t")))
                   (unless (equal? want ch) (fail "~a line ~a: chain differs on the second pass" f k))
                   (set! h ch)
                   (on-rec fs ch f)))))

(define (merge-ledger-book! pair path)
  (define bmap (make-hash))
  (define cur-f #f) (define cur-fch #f) (define cur-bs '())
  (define (flush!)
    (when cur-f
      (book-group! pair cur-f cur-fch (reverse cur-bs)
                   (lambda (f bs) (take (list-tail f 12) 6)) ; Q10 fields 12..17 as written
                   bmap)
      (set! cur-f #f) (set! cur-bs '())))
  (stream-source (list path)
    (lambda (fs ch file)
      (define tag (car fs))
      (cond [(regexp-match? #px"^F[0-9]{6}$" tag) (flush!) (set! cur-f fs) (set! cur-fch ch)]
            [(regexp-match? #px"^B[0-9]{7}$" tag) (set! cur-bs (cons (cons fs ch) cur-bs))]
            [(regexp-match? #px"^E" tag) (flush!)]
            [(regexp-match? #px"^H" tag) (void)]
            [else (fail "~a: unexpected record ~a in a BOOK ledger" path tag)])))
  (flush!))

(define (merge-ledger-neg! pair path)
  (stream-source (list path)
    (lambda (fs ch file)
      (define tag (car fs))
      (cond [(regexp-match? #px"^N[0-9]{6}$" tag)
             (unless (= (length fs) 11) (fail "~a ~a: N has ~a fields" path tag (length fs)))
             (book-neg! pair "N" fs ch)]
            [(regexp-match? #px"^[HE]" tag) (void)]
            [else (fail "~a: unexpected record ~a in a NEGATIVE ledger" path tag)]))))

(define (shipped-files) (let loop ([k 1] [acc '()])
                          (define p (build-path SHIPPED-DIR "book" (format "J~a.txt" (pad k 6))))
                          (if (file-exists? p) (loop (add1 k) (cons (path->string p) acc)) (reverse acc))))
(define shipped-c '())
(define (merge-shipped! with-book? with-neg?)
  (define bmap (make-hash))
  (define opened "-")
  (define cur-f #f) (define cur-fch #f) (define cur-bs '())
  (define (derive f bs)
    (define vname (substring (list-ref f 10) 9))
    (define receipt (string-append L9-VERDICTS vname))
    (unless (file-exists? receipt) (fail "shipped ~a: receipt ~a missing" (car f) receipt))
    (append (list "stmt -") (trace-union bs) (list (string-append "receipt " receipt) (string-append "posted " opened))))
  (define (flush!)
    (when cur-f
      (when with-book? (book-group! "SHIPPED" cur-f cur-fch (reverse cur-bs) derive bmap))
      (set! cur-f #f) (set! cur-bs '())))
  (define (neg-like fs ch kind)
    ;; shipped N/S: 9 fields; add receipt and posted
    (unless (= (length fs) 9) (fail "shipped ~a has ~a fields" (car fs) (length fs)))
    (define vname (substring (list-ref fs 8) 9))
    (define receipt (string-append L9-VERDICTS vname))
    (unless (file-exists? receipt) (fail "shipped ~a: receipt ~a missing" (car fs) receipt))
    (book-neg! "SHIPPED" kind (append fs (list (string-append "receipt " receipt) (string-append "posted " opened))) ch))
  (stream-source (shipped-files)
    (lambda (fs ch file)
      (define tag (car fs))
      (define kind (substring tag 0 1))
      (case kind
        [("H") (flush!) (set! opened (substring (list-ref fs 3) 7))]
        [("F") (flush!) (set! cur-f fs) (set! cur-fch ch)]
        [("B") (set! cur-bs (cons (cons fs ch) cur-bs))]
        [("N") (flush!) (when with-neg? (neg-like fs ch "N"))]
        [("S") (flush!) (when with-book? (neg-like fs ch "S"))]
        [("C") (flush!) (set! shipped-c (cons (list tag ch file) shipped-c))]
        [("E") (flush!)]
        [else (fail "shipped: unknown record ~a" tag)])))
  (flush!))

;; ------------------------------------------------------------------ main
(define (main args)
  (unless (= (vector-length args) 4) (eprintf "usage: racket book-merge.rkt MERGE-PLAN.tsv inventory.tsv OUTDIR DATE\n") (exit 2))
  (define planf (vector-ref args 0))
  (set! out-dir (vector-ref args 2))
  (set! date-text (vector-ref args 3))
  (make-directory* (build-path out-dir "book"))
  (load-existing out-dir)
  (define first-new (add1 seg-k))
  (define suffix (if (= seg-k 0) "" (format "-from-J~a" (pad first-new 6))))
  (set! dup-port (open-output-file (build-path out-dir (format "DUPLICATES~a.tsv" suffix)) #:exists 'error))
  (set! conf-port (open-output-file (build-path out-dir (format "CONFLICTS~a.tsv" suffix)) #:exists 'error))
  (fprintf dup-port "kind\tpair\tsource_id\tsource_chain\tkey\tbooked_as\n")
  (fprintf conf-port "kind\tpair\tsource_id\tkey\tnote\n")
  ;; plan rows grouped by pair, in plan order
  (define rows (for/list ([ln (cdr (file->lines planf))]) (split-tab ln)))
  (define pairs (remove-duplicates (map cadr rows)))
  (define (row pair kind) (for/first ([r rows] #:when (and (equal? (cadr r) pair) (equal? (caddr r) kind))) r))
  (define skipped '())
  (for ([pair pairs])
    (define rb (row pair "BOOK")) (define rn (row pair "NEGATIVE"))
    (define (merge? r) (and r (equal? (list-ref r 8) "MERGE")))
    (define (spot-text r k) (cond [(not r) (string-append k " -")] [else (format "~a ~a" k (list-ref r 7))]))
    (cond
      [(equal? pair "SHIPPED")
       ;; the shipped journal has two parts, accepted (F/B/S) and rejected (N); each merges once, possibly in
       ;; different runs (a part is merged when an H of source SHIPPED shows "B PASS B…" / "N PASS N…")
       (define do-b (and (merge? rb) (not (hash-ref merged-sources "SHIPPED-B" #f))))
       (define do-n (and (merge? rn) (not (hash-ref merged-sources "SHIPPED-N" #f))))
       (when (and (merge? rb) (not do-b)) (set! skipped (cons "SHIPPED BOOK part: already merged" skipped)))
       (when (and (merge? rn) (not do-n)) (set! skipped (cons "SHIPPED NEGATIVE part: already merged" skipped)))
       (when (or do-b do-n)
         (define files (shipped-files))
         (define-values (h n) (prepass files))
         (define rel (open-segment! (list "source SHIPPED"
                                          (format "book ~a segments ~a head ~a records ~a" SHIPPED-DIR (length files) h n)
                                          "negative -"
                                          (format "spotcheck ~a ; ~a" (if do-b (spot-text rb "B") "B -") (if do-n (spot-text rn "N") "N -")))))
         (merge-shipped! do-b do-n)
         (close-segment! rel)
         (when do-b (hash-set! merged-sources "SHIPPED-B" rel))
         (when do-n (hash-set! merged-sources "SHIPPED-N" rel))
         (printf "~a SHIPPED (~a) records ~a head ~a\n" rel (string-join (append (if do-b '("BOOK part") '()) (if do-n '("NEGATIVE part") '())) ", ") n h))]
      [else
       (define (usable r)
         (and (merge? r)
              (let ([sha (list-ref r 4)])
                (cond [(hash-ref merged-sources sha #f)
                       (set! skipped (cons (format "~a ~a: same bytes as a source already merged (~a)" pair (caddr r) (hash-ref merged-sources sha)) skipped))
                       #f]
                      [else #t]))))
       (define ub (usable rb)) (define un (usable rn))
       (when (or ub un)
         (define (src-field r ok? label)
           (cond [(not ok?) (string-append label " -")]
                 [else
                  (define path (list-ref r 3))
                  (define now (sha256-file path))
                  (unless (equal? now (list-ref r 4)) (fail "~a: sha256 now ~a, plan ~a" path now (list-ref r 4)))
                  (define-values (h n) (prepass (list path)))
                  (format "~a ~a sha256 ~a head ~a records ~a" label path now h n)]))
         (define fb (src-field rb ub "book"))
         (define fn (src-field rn un "negative"))
         (define rel (open-segment! (list (string-append "source " pair) fb fn
                                          (format "spotcheck ~a ; ~a" (if ub (spot-text rb "B") "B -") (if un (spot-text rn "N") "N -")))))
         (when ub (merge-ledger-book! pair (list-ref rb 3)) (hash-set! merged-sources (list-ref rb 4) rel))
         (when un (merge-ledger-neg! pair (list-ref rn 3)) (hash-set! merged-sources (list-ref rn 4) rel))
         (close-segment! rel)
         (printf "~a ~a\n" rel pair) (flush-output))]))
  (close-output-port dup-port) (close-output-port conf-port)
  (printf "segments now ~a (new this run ~a, from J~a)\n" seg-k (- seg-k first-new -1) (pad first-new 6))
  (printf "booked this run: F ~a B ~a N ~a S ~a; duplicates not booked: F ~a B ~a N ~a S ~a; conflicts ~a\n"
          (hash-ref totals "F" 0) (hash-ref totals "B" 0) (hash-ref totals "N" 0) (hash-ref totals "S" 0)
          (hash-ref totals "dup-F" 0) (hash-ref totals "dup-B" 0) (hash-ref totals "dup-N" 0) (hash-ref totals "dup-S" 0)
          (hash-ref totals "conflicts" 0))
  (printf "master totals: F ~a B ~a N ~a S ~a\n" (sub1 (hash-ref next "F" 1)) (sub1 (hash-ref next "B" 1)) (sub1 (hash-ref next "N" 1)) (sub1 (hash-ref next "S" 1)))
  (printf "shipped C records not carried: ~a\n" (string-join (map car (reverse shipped-c)) " "))
  (for ([s (reverse skipped)]) (printf "not merged again: ~a\n" s))
  (printf "chain head ~a\n" head))

(module+ main (main (current-command-line-arguments)))
