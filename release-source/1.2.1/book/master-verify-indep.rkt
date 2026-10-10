#lang racket/base
;; master-verify-indep.rkt -- independent checker of the master Book (book-master\SPEC.md, sections 1-5).
;; Written 2026-10-10 from SPEC.md and the source formats only (Q10 book-post-v2.rkt, Q122 ledger-verify.rkt,
;; Q23 tools\bookverify.rkt, the Q99 ledger pair and the shipped journal); book-merge.rkt and master-verify.rkt were
;; not read. Read-only: it opens files for reading and writes nothing.
;;
;;   racket master-verify-indep.rkt MASTERDIR        (MASTERDIR holds book\J000001.txt ...)
;;
;; Checks:
;;  1. journal: LF line ends, UTF-8, chain(i) = sha256(chain(i-1) as 64 hex ++ LF ++ the other fields joined by TAB)
;;     over all segments in file order; H<k> first and E<k> last in book/J<k>.txt; H names the previous segment and its
;;     sha256 (from the file bytes); F B N S numbers run 1, 2, 3 ... over the journal (B 7 digits, others 6); arity and
;;     field prefixes of H F B N S E per SPEC 3.
;;  2. sources (H fields 6-9): each named ledger exists and has the stated sha256, line count and chain head; its
;;     chain is recomputed; its record counts agree with its own E records; a ledger sha256 is merged once; segment 1
;;     is SHIPPED; the shipped journal's two parts (B part: its F, B and S records; N part: its N records) are each
;;     merged at most once over the journal, a SHIPPED segment merging the parts its H field 9 gives as
;;     "B PASS <id>,<id>" / "N PASS <id>,<id>" (any other part text: the part is not in the segment, and its source
;;     records must have no master record there and are not counted as duplicates); spotcheck picks name records of
;;     the merged ledger (shipped journal). [amended 2026-10-10 for SPEC 2 and 3 as amended 06:39]
;;  3. provenance, by one ordered walk of the segment's source next to the segment: every F B N S "from <id> <chain>"
;;     names a record of that source with that chain value, in source order (BOOK ledger, then NEGATIVE ledger; the
;;     shipped journal in journal order); copied fields are byte-equal; changed fields (ids, F of a B, postings,
;;     first, cites, booked/duplicates, the added verdict/receipt fields, shipped receipt/posted/traces) are
;;     recomputed and compared.
;;  4. duplicates (SPEC 4): every source record the walk passes without a master record must be a duplicate
;;     (B: (stmt, drv) booked before; F: sha256 booked before and none of its postings booked; N, S: sha256 booked
;;     before in the kind); no two B with the same (stmt, drv); no two N (S) with one sha256; E "duplicates" equals
;;     the walk's count per kind, and source records = booked + duplicates per kind.
;; Prints the counts and the chain head, then INDEP CHECK OK (exit 0), or the first INDEP_SHOW (env, default 50) differences and
;; INDEP CHECK FAILED: n differences (exit 1).
(require racket/string racket/list)

;; ---------------------------------------------------------------- basics
(define HEXD "0123456789abcdef")
(define (hex bs)
  (define s (make-string (* 2 (bytes-length bs))))
  (for ([b (in-bytes bs)] [i (in-naturals)])
    (string-set! s (* 2 i) (string-ref HEXD (arithmetic-shift b -4)))
    (string-set! s (add1 (* 2 i)) (string-ref HEXD (bitwise-and b 15))))
  s)
(define (file-sha p) (call-with-input-file p (lambda (in) (hex (sha256-bytes in)))))
(define ZERO (make-string 64 #\0))
(define (chain-next prev body) (hex (sha256-bytes (bytes-append (string->bytes/latin-1 prev) #"\n" body))))
(define (hex64? s) (and (string? s) (regexp-match? #px"^[0-9a-f]{64}$" s)))
(define (pad n w) (let ([s (number->string n)]) (string-append (make-string (max 0 (- w (string-length s))) #\0) s)))
(define (width k) (if (equal? k "B") 7 6))
(define (mk-id k n) (string-append k (pad n (width k))))
(define (kcode k n) (+ (* (char->integer (string-ref k 0)) 100000000) n))
(define (pstr p) (if (path? p) (path->string p) p))
(define (short x)
  (define s (if (string? x) x (format "~a" x)))
  (if (> (string-length s) 140) (string-append (substring s 0 137) "...") s))
(define (last-tab lb)
  (let loop ([i (sub1 (bytes-length lb))])
    (cond [(< i 0) #f] [(= (bytes-ref lb i) 9) i] [else (loop (sub1 i))])))
(define (split-fields s) (list->vector (string-split s "\t" #:trim? #f)))
(define (fld v i) (if (< i (vector-length v)) (vector-ref v i) ""))
(define (after s pfx) (and (string? s) (string-prefix? s pfx) (substring s (string-length pfx))))
(define (ends-with-lf? p)
  (define n (file-size p))
  (and (> n 0) (call-with-input-file p (lambda (in) (file-position in (sub1 n)) (eqv? (read-byte in) 10)))))

;; ---------------------------------------------------------------- differences
(define ndiff 0)
(define shown '())
(define (diff! fmt . a)
  (set! ndiff (add1 ndiff))
  (when (<= ndiff (or (string->number (or (getenv "INDEP_SHOW") "")) 50)) (set! shown (cons (apply format fmt a) shown))))
(define (decode b where)
  (with-handlers ([exn:fail? (lambda (e) (diff! "~a: bytes are not UTF-8" where) (bytes->string/utf-8 b (integer->char 65533)))])
    (bytes->string/utf-8 b)))
(define (arity! where v n)
  (unless (= (vector-length v) n) (diff! "~a: ~a fields before the chain, SPEC gives ~a" where (vector-length v) n)))
(define (pfx! where v i p)
  (define s (fld v i))
  (unless (and (string-prefix? s p) (> (string-length s) (string-length p)))
    (diff! "~a field ~a: ~s, expected ~s..." where i (short s) p)))
(define (hexf! where v i p)
  (define a (after (fld v i) p))
  (cond [(hex64? a) a] [else (diff! "~a field ~a: ~s, expected ~s<64 hex digits>" where i (short (fld v i)) p) #f]))
(define (natf! where v i p)
  (define a (after (fld v i) p))
  (cond [(and a (regexp-match? #px"^(0|[1-9][0-9]*)$" a)) (string->number a)]
        [else (diff! "~a field ~a: ~s, expected ~s<number>" where i (short (fld v i)) p) #f]))
(define (rxf! where v i rx what)
  (or (regexp-match rx (fld v i))
      (begin (diff! "~a field ~a: ~s, expected ~a" where i (short (fld v i)) what) #f)))
(define (eqf! where i got want)
  (unless (equal? got want) (diff! "~a field ~a: ~s, expected ~s" where i (short got) (short want))))

;; ---------------------------------------------------------------- axiom traces (Q10 / L9 field format)
(define AXN '("Ext" "Pair" "Union" "Power" "Inf" "Found" "Choice"))
(define (ranges->bits s)
  (for/fold ([bits 0]) ([part (string-split s ",")])
    (define m (and bits (regexp-match #px"^([0-9]+)(?:-([0-9]+))?$" part)))
    (and m
         (let* ([a (string->number (cadr m))] [b (if (caddr m) (string->number (caddr m)) a)])
           (and (<= a b) (bitwise-ior bits (arithmetic-shift (sub1 (arithmetic-shift 1 (add1 (- b a)))) a)))))))
(define (trace->bits ax def hyp)
  (define axb
    (cond [(equal? ax "ax -") 0]
          [(after ax "ax ")
           => (lambda (r) (for/fold ([b 0]) ([n (string-split r " ")])
                            (define i (index-of AXN n))
                            (and b i (bitwise-ior b (arithmetic-shift 1 i)))))]
          [else #f]))
  (define defb
    (cond [(equal? def "def 0 -") 0]
          [(regexp-match #px"^def [1-9][0-9]* ([0-9,-]+)$" def) => (lambda (m) (ranges->bits (cadr m)))]
          [else #f]))
  (define hb (cond [(equal? hyp "hypent -") 0] [(after hyp "hypent ") => ranges->bits] [else #f]))
  (and axb defb hb (bitwise-ior axb defb hb)))
(define (bits->ranges bits lo hi)
  (define (run a b) (if (= a b) (number->string a) (format "~a-~a" a b)))
  (let loop ([i lo] [start #f] [acc '()])
    (cond [(>= i hi) (string-join (reverse (if start (cons (run start (sub1 i)) acc) acc)) ",")]
          [(bitwise-bit-set? bits i) (loop (add1 i) (or start i) acc)]
          [start (loop (add1 i) #f (cons (run start (sub1 i)) acc))]
          [else (loop (add1 i) #f acc)])))
(define (render-trace bits n0)
  (define axs (for/list ([n AXN] [i (in-naturals)] #:when (and (< i n0) (bitwise-bit-set? bits i))) n))
  (define dhi (min 677 n0))
  (define dc (for/sum ([i (in-range 7 dhi)]) (if (bitwise-bit-set? bits i) 1 0)))
  (define hc (for/sum ([i (in-range 677 n0)]) (if (bitwise-bit-set? bits i) 1 0)))
  (list (if (null? axs) "ax -" (string-append "ax " (string-join axs " ")))
        (if (= dc 0) "def 0 -" (format "def ~a ~a" dc (bits->ranges bits 7 dhi)))
        (if (= hc 0) "hypent -" (string-append "hypent " (bits->ranges bits 677 n0)))))

;; ---------------------------------------------------------------- global state over the whole journal
(define chain ZERO)                  ; master chain, continued over all segments
(define next-num (make-hash))        ; "F" "B" "N" "S" -> next expected number
(define n-records 0)
(define kind-count (make-hash))      ; H F B N S E -> records
(define proved 0)
(define qualified 0)
(define dup-claimed (make-hash))     ; F B N S -> sum of E "duplicates"
(define key-table (make-hash))       ; bytes stmt++drv -> master B number
(define stmt-first (make-hash))      ; bytes stmt -> master B number of the first posting with it
(define f-sha (make-hash))           ; file sha256 -> first master F number
(define n-sha (make-hash))
(define s-sha (make-hash))
(define ledger-seen (make-hash))     ; ledger sha256 -> segment that merged it
(define shipped-part-at (make-hash)) ; "B" | "N" (parts of the shipped journal) -> segment that merged it
(define union-all 0)                 ; shipped F traces = union over all its source postings
(define union-booked 0)              ; ... = union over its booked postings only

;; ---------------------------------------------------------------- sources
(struct srec (kind num id fields chain ord opened file))
(struct cf (src-id booked? mv mnum where theorems again nb nd nums allb bookb) #:mutable)
(define SHIPPED-KINDS '("H" "F" "B" "N" "S" "C" "E"))

;; Pass 1 over a source: chain (one chain over all files when continuous?, else one per file), line counts, an index
;; kind+number -> ordinal (ordinal = line number over the files, from 0), record counts, and those counts against the
;; source's own E ranges. Returns (values index counts per-file head), per-file = (list lines head) per file.
(define (scan-source files continuous?)
  (define index (make-hasheqv))
  (define counts (make-hash))
  (define emax (make-hash))
  (define ord -1)
  (define ch ZERO)
  (define per-file
    (for/list ([fa files])
      (define p (car fa))
      (define allowed (cadr fa))
      (unless continuous? (set! ch ZERO))
      (define nl 0)
      (call-with-input-file p
        (lambda (in)
          (let loop ()
            (define lb (read-bytes-line in 'linefeed))
            (unless (eof-object? lb)
              (set! nl (add1 nl))
              (set! ord (add1 ord))
              (define where (format "source ~a line ~a" (pstr p) nl))
              (when (regexp-match? #rx#"\r" lb) (diff! "~a: CR byte" where))
              (define tab (last-tab lb))
              (define body (if tab (subbytes lb 0 tab) lb))
              (define claimed (if tab (bytes->string/latin-1 (subbytes lb (add1 tab))) ""))
              (define want (chain-next ch body))
              (unless (equal? claimed want) (diff! "~a: chain ~a, recomputed ~a" where (short claimed) want))
              (set! ch want)
              (define idm (regexp-match #px#"^([A-Z])([0-9]+)(?:\t|$)" body))
              (cond
                [(not idm) (diff! "~a: no record id" where)]
                [else
                 (define kd (bytes->string/latin-1 (cadr idm)))
                 (define n (string->number (bytes->string/latin-1 (caddr idm))))
                 (unless (member kd allowed) (diff! "~a: a ~a record does not belong in this source" where kd))
                 (cond
                   [(member kd '("F" "B" "N" "S"))
                    (define c (kcode kd n))
                    (when (hash-ref index c #f) (diff! "~a: ~a appears twice in the source" where (mk-id kd n)))
                    (hash-set! index c ord)
                    (hash-update! counts kd add1 0)]
                   [(equal? kd "E")
                    (define v (split-fields (bytes->string/utf-8 body (integer->char 65533))))
                    (for ([i (in-range 3 7)])
                      (define m (regexp-match #px"^([FBNS])[0-9]+-[FBNS]([0-9]+)$" (fld v i)))
                      (when m (hash-update! emax (cadr m) (lambda (x) (max x (string->number (caddr m)))) 0)))]
                   [else (void)])])
              (loop)))))
      (list nl ch)))
  (for ([kd '("F" "B" "N" "S")])
    (unless (= (hash-ref counts kd 0) (hash-ref emax kd 0))
      (diff! "source ~a: ~a ~a records, its E records give ~a" (pstr (car (car files))) (hash-ref counts kd 0) kd
             (hash-ref emax kd 0))))
  (values index counts per-file ch))

;; Pass 2: the F B N S records of the source in order (H, E and C are passed over; H sets the "opened" date).
;; keep? (a kind -> boolean) passes over the records of a shipped part the segment does not merge.
(define (make-walker files keep?)
  (define rest files)
  (define port #f)
  (define cur-file #f)
  (define ord -1)
  (define opened #f)
  (define (next!)
    (cond
      [port
       (define lb (read-bytes-line port 'linefeed))
       (cond
         [(eof-object? lb) (close-input-port port) (set! port #f) (next!)]
         [else
          (set! ord (add1 ord))
          (define tab (last-tab lb))
          (define body (if tab (subbytes lb 0 tab) lb))
          (define ch (if tab (bytes->string/latin-1 (subbytes lb (add1 tab))) ""))
          (define v (split-fields (bytes->string/utf-8 body (integer->char 65533))))
          (define m (regexp-match #px"^([A-Z])([0-9]+)$" (fld v 0)))
          (define kd (and m (cadr m)))
          (cond
            [(equal? kd "H") (set! opened (after (fld v 3) "opened ")) (next!)]
            [(and (member kd '("F" "B" "N" "S")) (keep? kd))
             (srec kd (string->number (caddr m)) (fld v 0) v ch ord opened (pstr cur-file))]
            [else (next!)])])]
      [(null? rest) eof]
      [else (set! cur-file (car rest)) (set! rest (cdr rest)) (set! port (open-input-file cur-file)) (next!)]))
  next!)

(define (src-arity! s n)
  (unless (= (vector-length (srec-fields s)) n)
    (diff! "source ~a (~a): ~a fields before the chain, its format has ~a" (srec-id s) (srec-file s)
           (vector-length (srec-fields s)) n)))
(define (same! where v s idxs)
  (define sv (srec-fields s))
  (for ([i idxs])
    (unless (equal? (fld v i) (fld sv i))
      (diff! "~a field ~a differs from source ~a: ~s, source ~s" where i (srec-id s) (short (fld v i)) (short (fld sv i))))))
(define (receipt! where v i vi)
  ;; shipped Book: receipt = lanes\L9\verdicts\<verdicts name> (accepted relative, or as the tail of a longer path)
  (define p (after (fld v i) "receipt "))
  (define name (after (fld v vi) "verdicts "))
  (define tail (and name (string-append "lanes\\L9\\verdicts\\" name)))
  (define p2 (and p (string-replace p "/" "\\")))
  (unless (and p2 tail (or (equal? p2 tail) (string-suffix? p2 (string-append "\\" tail))))
    (diff! "~a field ~a: ~s, expected \"receipt ...lanes\\L9\\verdicts\\~a\"" where i (short (fld v i)) (or name "?"))))
(define (from! where v i kd)
  (define m (regexp-match #px"^from ([A-Z])([0-9]+) ([0-9a-f]{64})$" (fld v i)))
  (cond [(and m (equal? (cadr m) kd) (= (string-length (caddr m)) (width kd)))
         (list (string-append kd (caddr m)) (string->number (caddr m)) (cadddr m))]
        [else (diff! "~a field ~a: ~s, expected \"from ~a<id> <64 hex chain>\"" where i (short (fld v i)) kd) #f]))

;; ---------------------------------------------------------------- one segment
(define (process-segment dir k rel path prev-rel)
  (define in (open-input-file path))
  (define line-no 0)
  (define seg-count 0)                 ; records of this segment read so far
  (define seg-nums (make-hash))        ; kind -> numbers in this segment
  (define (next-master!)
    (define lb (read-bytes-line in 'linefeed))
    (cond
      [(eof-object? lb) eof]
      [else
       (set! line-no (add1 line-no))
       (define where (format "~a line ~a" rel line-no))
       (when (regexp-match? #rx#"\r" lb) (diff! "~a: CR byte" where))
       (define tab (last-tab lb))
       (define body (if tab (subbytes lb 0 tab) lb))
       (define claimed (if tab (bytes->string/latin-1 (subbytes lb (add1 tab))) ""))
       (define want (chain-next chain body))
       (unless (equal? claimed want) (diff! "~a: chain ~a, recomputed ~a" where (short claimed) want))
       (set! chain (if (hex64? claimed) claimed want))
       (define v (split-fields (decode body where)))
       (define id (fld v 0))
       (define m (regexp-match #px"^([HFBNSE])([0-9]+)$" id))
       (define kd (and m (cadr m)))
       (define num (and m (string->number (caddr m))))
       (set! n-records (add1 n-records))
       (set! seg-count (add1 seg-count))
       (cond
         [(not m) (diff! "~a: unknown record id ~s" where (short id))]
         [else
          (unless (= (string-length (caddr m)) (width kd))
            (diff! "~a: ~a has ~a digits, SPEC gives ~a" where id (string-length (caddr m)) (width kd)))
          (cond
            [(member kd '("H" "E")) (unless (= num k) (diff! "~a: ~a in segment ~a" where id k))]
            [else
             (define exp (hash-ref next-num kd 1))
             (unless (= num exp) (diff! "~a: ~a, expected ~a (numbers run without gaps)" where id (mk-id kd exp)))
             (hash-set! next-num kd (add1 num))])
          (hash-update! kind-count kd add1 0)
          (hash-update! seg-nums kd (lambda (l) (cons num l)) '())])
       (vector where kd num v)]))

  ;; ------------------------------------------------ H and its sources
  (define mode 'none)                  ; 'shipped | 'pair | 'none
  (define src-files '())
  (define index (make-hasheqv))
  (define src-counts (make-hash))
  (define merged-kinds #f)             ; SHIPPED: the kinds of the parts this segment merges; #f: every kind
  (define (resolve p)
    (cond [(absolute-path? p) p]
          [else (define q (build-path dir p)) (if (or (file-exists? q) (directory-exists? q)) q p)]))
  (define (check-H where v)
    (arity! where v 10)
    (eqf! where 1 (fld v 1) (string-append "segment " rel))
    (eqf! where 2 (fld v 2)
          (if prev-rel (string-append "previous " prev-rel " " (file-sha (build-path dir prev-rel))) "previous - -"))
    (pfx! where v 3 "opened ")
    (hexf! where v 4 "book-merge.rkt ")
    (hexf! where v 5 "racket.exe ")
    (define src (after (fld v 6) "source "))
    (cond
      [(not (and src (positive? (string-length src))))
       (diff! "~a field 6: ~s, expected \"source <pair id | SHIPPED>\"" where (short (fld v 6)))]
      [(equal? src "SHIPPED")
       ;; segment 1 is SHIPPED (any other source there is reported below); a later SHIPPED segment merges a part
       ;; held before. Which parts this segment merges is read from field 9 after the journal is scanned.
       (eqf! where 8 (fld v 8) "negative -")
       (define m (rxf! where v 7 #px"^book (.+) segments ([1-9][0-9]*) head ([0-9a-f]{64}) records ([0-9]+)$"
                       "\"book <folder> segments <n> head <hex> records <lines>\""))
       (when m
         (let ()
           (define folder (resolve (cadr m)))
           (define files (for/list ([i (in-range 1 (add1 (string->number (caddr m))))])
                           (build-path folder "book" (format "J~a.txt" (pad i 6)))))
           (define missing (filter (lambda (f) (not (file-exists? f))) files))
           (cond
             [(pair? missing) (diff! "~a field 7: shipped segment ~a does not exist" where (pstr (car missing)))]
             [else
              (define-values (ix cn per-file head) (scan-source (for/list ([f files]) (list f SHIPPED-KINDS)) #t))
              (eqf! where 7 (format "head ~a records ~a" head (for/sum ([pf per-file]) (car pf)))
                    (format "head ~a records ~a" (cadddr m) (list-ref m 4)))
              (set! mode 'shipped) (set! src-files files) (set! index ix) (set! src-counts cn)])))
       ;; field 9: "spotcheck <B part> ; <N part>"; a part is merged here iff its text is "<kd> PASS <id>,<id>"
       (define sm (rxf! where v 9 #px"^spotcheck (B [^;]+) ; (N [^;]+)$" "\"spotcheck <B part> ; <N part>\""))
       (define parts
         (cond
           [(not sm) '("B" "N")]           ; unreadable (counted above): the walk takes both parts
           [else
            (for/fold ([acc '()] #:result (reverse acc)) ([kd '("B" "N")] [whole (cdr sm)])
              (define pm (regexp-match (pregexp (format "^~a PASS ([^ ,;]+),([^ ,;]+)$" kd)) whole))
              (cond
                [(not pm) acc]
                [else
                 (for ([x (cdr pm)])
                   (define im (regexp-match (pregexp (format "^~a([0-9]{~a})$" kd (width kd))) x))
                   (unless (and im (hash-ref index (kcode kd (string->number (cadr im))) #f))
                     (diff! "~a field 9: pick ~a is no ~a record of the shipped journal" where x kd)))
                 (cons kd acc)]))]))
       (for ([kd parts])
         (define at (hash-ref shipped-part-at kd #f))
         (if at
             (diff! "~a field 9: merges the shipped journal's ~a part, already merged in segment ~a (each part once)"
                    where kd at)
             (hash-set! shipped-part-at kd k)))
       (when (and (null? parts) (> k 1))
         (diff! "~a field 9: ~s; this later SHIPPED segment merges no part of the shipped journal" where (short (fld v 9))))
       (set! merged-kinds (append (if (member "B" parts) '("F" "B" "S") '()) (if (member "N" parts) '("N") '())))
       ;; a part not merged here: its source records are not in this segment (not booked, not duplicates)
       (for ([kd '("F" "B" "N" "S")]) (unless (member kd merged-kinds) (hash-remove! src-counts kd)))]
      [else
       (when (= k 1) (diff! "~a: segment 1 has source ~a; SPEC 2 puts the shipped Book in segment 1" where src))
       (define (ledger i word kinds)
         (cond
           [(equal? (fld v i) (string-append word " -")) #f]
           [else
            (define m (rxf! where v i (pregexp (string-append "^" word " (.+) sha256 ([0-9a-f]{64}) head ([0-9a-f]{64}) records ([0-9]+)$"))
                            (format "\"~a <path> sha256 <hex> head <hex> records <lines>\" or \"~a -\"" word word)))
            (cond
              [(not m) #f]
              [(not (file-exists? (resolve (cadr m))))
               (diff! "~a field ~a: ledger ~a does not exist" where i (cadr m)) #f]
              [else
               (define p (resolve (cadr m)))
               (define sha (file-sha p))
               (eqf! where i (string-append "sha256 " sha) (string-append "sha256 " (caddr m)))
               (define seen (hash-ref ledger-seen sha #f))
               (when seen (diff! "~a field ~a: ledger sha256 ~a already merged in segment ~a" where i sha seen))
               (hash-set! ledger-seen sha k)
               (list p kinds (cadddr m) (string->number (list-ref m 4)) i)])]))
       (define lb (ledger 7 "book" '("H" "F" "B" "E")))
       (define ln (ledger 8 "negative" '("H" "N" "E")))
       (define present (filter values (list lb ln)))
       (when (and (equal? (fld v 7) "book -") (equal? (fld v 8) "negative -"))
         (diff! "~a: fields 7 and 8 name no ledger" where))
       (unless (null? present)
         (let ()
           (define-values (ix cn per-file head) (scan-source (for/list ([x present]) (list (car x) (cadr x))) #f))
           (for ([x present] [pf per-file])
             (eqf! where (list-ref x 4) (format "head ~a records ~a" (cadr pf) (car pf))
                   (format "head ~a records ~a" (caddr x) (cadddr x))))
           (set! mode 'pair) (set! src-files (map car present)) (set! index ix) (set! src-counts cn)))
       ;; SPEC 3 as amended: a part not merged is written "B -" / "N -" (the first text said "B none" / "N none")
       (define sm (rxf! where v 9 #px"^spotcheck (B -|B PASS ([^ ,;]+),([^ ,;]+)) ; (N -|N PASS ([^ ,;]+),([^ ,;]+))$"
                        "\"spotcheck B PASS <id>,<id> | B - ; N PASS <id>,<id> | N -\""))
       (when sm
         (for ([kd '("B" "N")] [merged (list lb ln)] [j '(1 4)])
           (define whole (list-ref sm j))
           (cond
             [(not merged)
              (unless (equal? whole (string-append kd " -"))
                (diff! "~a field 9: ~s, but no ledger with ~a records is merged here" where whole kd))]
             [(equal? whole (string-append kd " -"))
              (diff! "~a field 9: ~a -, but the ledger is merged (SPEC 2: 2 picks PASS)" where kd)]
             [else
              (for ([x (list (list-ref sm (+ j 1)) (list-ref sm (+ j 2)))])
                (define im (regexp-match (pregexp (format "^~a([0-9]{~a})$" kd (width kd))) x))
                (unless (and im (hash-ref index (kcode kd (string->number (cadr im))) #f))
                  (diff! "~a field 9: pick ~a is no ~a record of the merged ledger" where x kd)))])))]))

  (define head-rec (next-master!))
  (cond
    [(eof-object? head-rec) (diff! "~a: empty segment" rel)]
    [(not (equal? (vector-ref head-rec 1) "H")) (diff! "~a: first record is not H~a" rel (pad k 6))]
    [else (check-H (vector-ref head-rec 0) (vector-ref head-rec 3))])

  ;; ------------------------------------------------ the walk
  (define next-src! (if (eq? mode 'none) (lambda () eof)
                        (make-walker src-files (lambda (kd) (or (not merged-kinds) (member kd merged-kinds) #f)))))
  (define pos -1)
  (define (pull!) (define s (next-src!)) (unless (eof-object? s) (set! pos (srec-ord s))) s)
  (define dupc (make-hash))            ; kind -> source records passed without a master record
  (define srcB->m (make-hasheqv))      ; source B number -> master B number (booked, or the booked twin)
  (define cur #f)                      ; the source F whose postings are being walked

  (define (finalize!)
    (when (and cur (cf-booked? cur))
      (define v (cf-mv cur))
      (define where (cf-where cur))
      (define nb (cf-nb cur))
      (define nd (cf-nd cur))
      (eqf! where 18 (fld v 18) (format "booked ~a duplicates ~a" nb nd))
      (define m (cf-theorems cur))
      (when (and m (not (= (+ nb nd) m)))
        (diff! "~a: theorems ~a, but the walk finds ~a booked + ~a duplicate postings" where m nb nd))
      (define nums (reverse (cf-nums cur)))
      (unless (for/and ([a nums] [i (in-naturals)]) (= a (+ (car nums) i)))
        (diff! "~a: its booked postings are not contiguous" where))
      (eqf! where 11 (fld v 11)
            (if (null? nums) "postings -" (format "postings ~a-~a" (mk-id "B" (car nums)) (mk-id "B" (last nums)))))
      (when (and (cf-again cur) (= nb 0))
        (diff! "~a: file sha256 booked before as ~a and no new posting; SPEC 4 makes it a duplicate" where
               (mk-id "F" (cf-again cur))))
      (when (eq? mode 'shipped)
        (define rm (regexp-match #px"^registry ([0-9]+) " (fld v 5)))
        (when rm
          (define n0 (string->number (cadr rm)))
          (define got (list (fld v 13) (fld v 14) (fld v 15)))
          (cond [(equal? got (render-trace (cf-allb cur) n0)) (set! union-all (add1 union-all))]
                [(equal? got (render-trace (cf-bookb cur) n0)) (set! union-booked (add1 union-booked))]
                [else (diff! "~a fields 13-15: ~s, the union of its postings' traces is ~s" where
                             (short (string-join got " | ")) (short (string-join (render-trace (cf-allb cur) n0) " | ")))]))))
    (set! cur #f))

  (define (dup! s)
    (define kd (srec-kind s))
    (define sv (srec-fields s))
    (define where (format "~a: source ~a (no master record)" rel (srec-id s)))
    (hash-update! dupc kd add1 0)
    (cond
      [(equal? kd "F")
       (finalize!)
       (define sha (after (fld sv 2) "sha256 "))
       (unless (and sha (hash-ref f-sha sha #f))
         (diff! "~a: its file sha256 was not booked before, so it is no duplicate (SPEC 4)" where))
       (set! cur (cf (srec-id s) #f #f #f where (natf! where sv 6 "theorems ") #f 0 0 '() 0 0))]
      [(equal? kd "B")
       (cond [(not cur) (diff! "~a: B before any source F" where)]
             [else (unless (equal? (fld sv 1) (cf-src-id cur))
                     (diff! "~a: names ~a, but the walk is at source ~a" where (fld sv 1) (cf-src-id cur)))
                   (set-cf-nd! cur (add1 (cf-nd cur)))])
       (define stmt (after (fld sv 5) "stmt "))
       (define drv (after (fld sv 6) "drv "))
       (define mm (and stmt drv (hash-ref key-table (string->bytes/latin-1 (string-append stmt drv)) #f)))
       (if mm
           (hash-set! srcB->m (srec-num s) mm)
           (diff! "~a: no earlier master B has its stmt and drv, so it is no duplicate (SPEC 4)" where))
       (define tb (trace->bits (fld sv 11) (fld sv 12) (fld sv 13)))
       (when (and cur tb) (set-cf-allb! cur (bitwise-ior (cf-allb cur) tb)))]
      [else
       (finalize!)
       (define sha (after (fld sv 3) "sha256 "))
       (unless (and sha (hash-ref (if (equal? kd "N") n-sha s-sha) sha #f))
         (diff! "~a: its file sha256 was not booked before as ~a, so it is no duplicate (SPEC 4)" where kd))]))

  (define (advance kd num)
    (define o (hash-ref index (kcode kd num) #f))
    (cond
      [(not o) 'absent]
      [(<= o pos) 'passed]
      [else (let loop ()
              (define s (pull!))
              (cond [(eof-object? s) 'absent]
                    [(= (srec-ord s) o) s]
                    [else (dup! s) (loop)]))]))

  (define (map-cites where s)
    (define c (fld (srec-fields s) 10))
    (cond
      [(equal? c "cites -") c]
      [else
       (string-append
        "cites "
        (string-join
         (for/list ([t (string-split (or (after c "cites ") "") " ")])
           (define m (regexp-match #px"^B([0-9]+)$" t))
           (cond [(not m) t]
                 [(hash-ref srcB->m (string->number (cadr m)) #f) => (lambda (n) (mk-id "B" n))]
                 [else (diff! "~a: source cite ~a has no master posting before it" where t) (string-append "?" t)]))
         " "))]))

  (define (master-F where num v s)
    (finalize!)
    (arity! where v 20)
    (pfx! where v 1 "file ")
    (define sha (hexf! where v 2 "sha256 "))
    (natf! where v 3 "bytes ")
    (pfx! where v 4 "source ")
    (rxf! where v 5 #px"^registry [0-9]+ prefix [0-9a-f]{64}$" "\"registry <n0> prefix <hex>\"")
    (define m (natf! where v 6 "theorems "))
    (natf! where v 7 "steps ")
    (pfx! where v 8 "pmp ACCEPT ")
    (pfx! where v 9 "racket ACCEPT ")
    (pfx! where v 10 "verdicts ")
    (rxf! where v 11 #px"^postings (-|B[0-9]{7}-B[0-9]{7})$" "\"postings B<x>-B<y>\" or \"postings -\"")
    (unless (or (equal? (fld v 12) "stmt -") (hex64? (after (fld v 12) "stmt ")))
      (diff! "~a field 12: ~s, expected \"stmt <hex>\" or \"stmt -\"" where (short (fld v 12))))
    (pfx! where v 13 "ax ")
    (pfx! where v 14 "def ")
    (pfx! where v 15 "hypent ")
    (pfx! where v 16 "receipt ")
    (pfx! where v 17 "posted ")
    (rxf! where v 18 #px"^booked [0-9]+ duplicates [0-9]+$" "\"booked <k> duplicates <d>\"")
    (when s
      (cond
        [(eq? mode 'shipped)
         (src-arity! s 12)
         (same! where v s (range 1 11))
         (eqf! where 12 (fld v 12) "stmt -")
         (receipt! where v 16 10)
         (eqf! where 17 (fld v 17) (string-append "posted " (or (srec-opened s) "?")))]
        [else
         (src-arity! s 18)
         (same! where v s (append (range 1 11) (range 12 18)))]))
    (define again (and sha (hash-ref f-sha sha #f)))
    (when (and sha (not again)) (hash-set! f-sha sha num))
    (set! cur (cf (and s (srec-id s)) #t v num where m again 0 0 '() 0 0)))

  (define (master-B where num v s)
    (arity! where v 24)
    (rxf! where v 1 #px"^F[0-9]{6}$" "\"F<6 digits>\"")
    (natf! where v 2 "thm ")
    (natf! where v 3 "entry ")
    (define st (fld v 4))
    (cond [(equal? st "Proved") (set! proved (add1 proved))]
          [(equal? st "Qualified") (set! qualified (add1 qualified))]
          [else (diff! "~a field 4: status ~s" where (short st))])
    (define stmt (hexf! where v 5 "stmt "))
    (define drv (hexf! where v 6 "drv "))
    (natf! where v 7 "steps ")
    (pfx! where v 8 "hyps ")
    (unless (eq? (equal? st "Proved") (equal? (fld v 8) "hyps -"))
      (diff! "~a: status ~a with ~s (Proved iff hyps -)" where st (short (fld v 8))))
    (rxf! where v 9 #px"^first (-|B[0-9]{7})$" "\"first B<7 digits>\" or \"first -\"")
    (rxf! where v 10 #px"^cites (-|[RB][0-9]+( [RB][0-9]+)*)$" "\"cites -\" or \"cites <R/B ids>\"")
    (pfx! where v 11 "ax ")
    (pfx! where v 12 "def ")
    (pfx! where v 13 "hypent ")
    (hexf! where v 14 "file ")
    (hexf! where v 15 "registry ")
    (pfx! where v 16 "source ")
    (pfx! where v 17 "pmp ACCEPT ")
    (pfx! where v 18 "racket ACCEPT ")
    (pfx! where v 19 "pmp-verdict ")
    (pfx! where v 20 "racket-verdict ")
    (pfx! where v 21 "verdicts ")
    (pfx! where v 22 "receipt ")
    ;; its F
    (cond
      [(not (and cur (cf-booked? cur)))
       (diff! "~a: no booked F of its file precedes it in this segment" where)]
      [else
       (define fv (cf-mv cur))
       (eqf! where 1 (fld v 1) (mk-id "F" (cf-mnum cur)))
       (eqf! where 14 (fld v 14) (string-append "file " (or (after (fld fv 2) "sha256 ") "?")))
       (define frm (regexp-match #px"^registry [0-9]+ prefix ([0-9a-f]{64})$" (fld fv 5)))
       (eqf! where 15 (fld v 15) (string-append "registry " (if frm (cadr frm) "?")))
       (eqf! where 19 (fld v 19) (string-append "pmp-verdict " (or (after (fld fv 8) "pmp ") "?")))
       (eqf! where 20 (fld v 20) (string-append "racket-verdict " (or (after (fld fv 9) "racket ") "?")))
       (eqf! where 21 (fld v 21) (fld fv 10))
       (eqf! where 22 (fld v 22) (fld fv 16))
       (set-cf-nb! cur (add1 (cf-nb cur)))
       (set-cf-nums! cur (cons num (cf-nums cur)))])
    ;; its source record
    (when s
      (src-arity! s 19)
      (same! where v s (append (range 2 9) (range 11 19)))
      (when (and cur (cf-src-id cur) (not (equal? (fld (srec-fields s) 1) (cf-src-id cur))))
        (diff! "~a: source ~a names ~a, but the walk is at source ~a" where (srec-id s) (fld (srec-fields s) 1) (cf-src-id cur)))
      (eqf! where 10 (fld v 10) (map-cites where s)))
    (for ([t (string-split (or (after (fld v 10) "cites ") "") " ")])
      (define m (regexp-match #px"^B([0-9]+)$" t))
      (when m
        (define n (string->number (cadr m)))
        (unless (and (= (string-length (cadr m)) 7) (>= n 1) (< n num))
          (diff! "~a: cites ~a, which is no earlier posting" where t))))
    ;; (stmt, drv) once; first
    (when (and stmt drv)
      (define key (string->bytes/latin-1 (string-append stmt drv)))
      (define prior (hash-ref key-table key #f))
      (if prior
          (diff! "~a: duplicate (stmt, drv); the same pair is booked as ~a" where (mk-id "B" prior))
          (hash-set! key-table key num))
      (define sk (string->bytes/latin-1 stmt))
      (define fst (hash-ref stmt-first sk #f))
      (eqf! where 9 (fld v 9) (if fst (string-append "first " (mk-id "B" fst)) "first -"))
      (unless fst (hash-set! stmt-first sk num)))
    (when s (hash-set! srcB->m (srec-num s) num))
    (define tb (trace->bits (fld v 11) (fld v 12) (fld v 13)))
    (unless tb (diff! "~a: ax/def/hypent trace is not readable" where))
    (when (and cur tb)
      (set-cf-allb! cur (bitwise-ior (cf-allb cur) tb))
      (set-cf-bookb! cur (bitwise-ior (cf-bookb cur) tb))))

  (define (master-NS where kd num v s)
    (finalize!)
    (arity! where v 12)
    (if (equal? kd "N") (eqf! where 1 (fld v 1) "Rejected") (pfx! where v 1 "reason "))
    (pfx! where v 2 "file ")
    (define sha (hexf! where v 3 "sha256 "))
    (natf! where v 4 "bytes ")
    (pfx! where v 5 "source ")
    (pfx! where v 6 (if (equal? kd "N") "pmp REJECT" "pmp "))
    (pfx! where v 7 (if (equal? kd "N") "racket REJECT" "racket "))
    (pfx! where v 8 "verdicts ")
    (pfx! where v 9 "receipt ")
    (pfx! where v 10 "posted ")
    (when (and (equal? kd "S") (not (eq? mode 'shipped)))
      (diff! "~a: S record in a segment whose source is not the shipped Book" where))
    (when s
      (cond
        [(eq? mode 'shipped)
         (src-arity! s 9)
         (same! where v s (range 1 9))
         (receipt! where v 9 8)
         (eqf! where 10 (fld v 10) (string-append "posted " (or (srec-opened s) "?")))]
        [else
         (src-arity! s 11)
         (same! where v s (range 1 11))]))
    (when sha
      (define tbl (if (equal? kd "N") n-sha s-sha))
      (define p (hash-ref tbl sha #f))
      (if p
          (diff! "~a: file sha256 already booked as ~a (SPEC 4: key = file sha256)" where (mk-id kd p))
          (hash-set! tbl sha num))))

  (define (handle! mr)
    (define where (vector-ref mr 0))
    (define kd (vector-ref mr 1))
    (define num (vector-ref mr 2))
    (define v (vector-ref mr 3))
    (define fr (from! where v (cond [(equal? kd "F") 19] [(equal? kd "B") 23] [else 11]) kd))
    ;; SHIPPED segment: a record of a part its H field 9 does not merge must have no master record here
    (define held? (and merged-kinds (not (member kd merged-kinds))))
    (when held?
      (diff! "~a: ~a (from ~a) is of the shipped journal's ~a part, which this segment does not merge (H field 9)"
             where (fld v 0) (if fr (car fr) "?") (if (equal? kd "N") "N" "B")))
    (define s
      (and fr (not held?)
           (let ([r (advance kd (cadr fr))])
             (cond
               [(srec? r)
                (unless (equal? (srec-chain r) (caddr fr))
                  (diff! "~a: from ~a ~a, but source record ~a has chain ~a" where (car fr) (caddr fr) (car fr) (srec-chain r)))
                r]
               [(eq? r 'passed)
                (diff! "~a: from ~a lies before the previous booked source record (out of source order, or booked twice)" where (car fr))
                #f]
               [else (diff! "~a: from ~a: no such record in this segment's source" where (car fr)) #f]))))
    (cond [(equal? kd "F") (master-F where num v s)]
          [(equal? kd "B") (master-B where num v s)]
          [else (master-NS where kd num v s)]))

  (define (drain!)
    (let loop () (define s (pull!)) (unless (eof-object? s) (dup! s) (loop)))
    (finalize!))

  (define (check-E where v)
    (arity! where v 10)
    (eqf! where 1 (fld v 1) (string-append "segment " rel))
    (eqf! where 2 (fld v 2) (format "records ~a" (sub1 seg-count)))
    (for ([kd '("F" "B" "N" "S")] [i (in-range 3 7)])
      (define ns (sort (hash-ref seg-nums kd '()) <))
      (eqf! where i (fld v i) (if (null? ns) (string-append kd " -") (string-append (mk-id kd (car ns)) "-" (mk-id kd (last ns))))))
    (eqf! where 7 (fld v 7) "C -")
    (pfx! where v 8 "closed ")
    (define dm (rxf! where v 9 #px"^duplicates F ([0-9]+) B ([0-9]+) N ([0-9]+) S ([0-9]+)$" "\"duplicates F <a> B <b> N <c> S <d>\""))
    (when dm
      (for ([kd '("F" "B" "N" "S")] [c (cdr dm)])
        (define claimed (string->number c))
        (hash-update! dup-claimed kd (lambda (x) (+ x claimed)) 0)
        (define booked (length (hash-ref seg-nums kd '())))
        (define srcn (hash-ref src-counts kd 0))
        (unless (= srcn (+ booked claimed))
          (diff! "~a: source has ~a ~a records; the segment books ~a and E claims ~a duplicates" where srcn kd booked claimed))
        (unless (= claimed (hash-ref dupc kd 0))
          (diff! "~a: E claims ~a ~a duplicates; the walk passes ~a ~a source records without a master record" where
                 claimed kd (hash-ref dupc kd 0) kd)))))

  (let loop ()
    (define mr (next-master!))
    (cond
      [(eof-object? mr) (diff! "~a: no E record at the end of the segment" rel) (drain!)]
      [(not (vector-ref mr 1)) (loop)]
      [(equal? (vector-ref mr 1) "E")
       (drain!)
       (check-E (vector-ref mr 0) (vector-ref mr 3))
       (unless (eof-object? (peek-bytes 1 0 in)) (diff! "~a: records after the E record" rel))]
      [(equal? (vector-ref mr 1) "H") (diff! "~a: H record inside the segment" (vector-ref mr 0)) (loop)]
      [else (handle! mr) (loop)]))
  (close-input-port in))

;; ---------------------------------------------------------------- main
(define (main dir)
  (define segs (let loop ([k 1] [acc '()])
                 (define rel (format "book/J~a.txt" (pad k 6)))
                 (if (file-exists? (build-path dir rel)) (loop (add1 k) (cons rel acc)) (reverse acc))))
  (when (null? segs) (diff! "no book/J000001.txt under ~a" dir))
  (define bdir (build-path dir "book"))
  (when (directory-exists? bdir)
    (for ([p (directory-list bdir)])
      (define s (path->string p))
      (when (and (regexp-match? #px"^J[0-9]+\\.txt$" s) (not (member (string-append "book/" s) segs)))
        (diff! "book/~a lies outside the segment sequence J000001 ... J~a" s (pad (length segs) 6)))))
  (for ([rel segs] [k (in-naturals 1)])
    (define path (build-path dir rel))
    (unless (ends-with-lf? path) (diff! "~a: does not end with LF" rel))
    (with-handlers ([exn:fail? (lambda (e) (diff! "~a: checker stopped in this segment: ~a" rel (short (exn-message e))))])
      (process-segment dir k rel path (and (> k 1) (list-ref segs (- k 2))))))
  (define (c kd) (hash-ref kind-count kd 0))
  (define (d kd) (hash-ref dup-claimed kd 0))
  (printf "segments ~a records ~a\n" (length segs) n-records)
  (printf "F ~a B ~a N ~a S ~a E ~a H ~a\n" (c "F") (c "B") (c "N") (c "S") (c "E") (c "H"))
  (printf "B Proved ~a Qualified ~a\n" proved qualified)
  (printf "duplicates claimed in E: F ~a B ~a N ~a S ~a\n" (d "F") (d "B") (d "N") (d "S"))
  (printf "shipped F traces: union of all postings ~a, of booked postings only ~a\n" union-all union-booked)
  (printf "shipped parts merged: B ~a N ~a\n"
          (let ([k (hash-ref shipped-part-at "B" #f)]) (if k (format "segment ~a" k) "-"))
          (let ([k (hash-ref shipped-part-at "N" #f)]) (if k (format "segment ~a" k) "-")))
  (printf "chain head ~a\n" chain)
  (cond [(= ndiff 0) (printf "INDEP CHECK OK\n") 0]
        [else (for ([s (reverse shown)]) (printf "DIFF ~a\n" s))
              (printf "INDEP CHECK FAILED: ~a differences\n" ndiff) 1]))

(module+ main
  (define args (current-command-line-arguments))
  (unless (= (vector-length args) 1)
    (eprintf "usage: racket master-verify-indep.rkt MASTERDIR\n")
    (exit 2))
  (exit (main (vector-ref args 0))))
