#lang racket/base
;; pmpc.rkt -- pmp to x64: a pmp program becomes the machine program, statement for statement (2026-10-09, first cut).
;; No interpreter at run time: every variable is a fixed 8-byte cell, every statement a fixed instruction sequence.
;;
;; The statement forms (PmpCore and the input/output forms of PmpFull that the judge uses):
;;   set X const A | add A B | sub A B | mul A B | peek A W | alloc A      poke A W B
;;   text X "LIT" | text X arg     read X F     when zero|nonzero|negative A goto L     goto L     gosub L     return
;;   label L     say "LIT"     show A     print T     check zero A     trace on|off
;; An operand A is a variable or a decimal integer. A text T is the pair of cells T and T_len.
;; Semantics as the interpreter's: 64-bit two's-complement words; peek/poke of 1, 2, 4 or 8 bytes, little endian;
;; alloc returns zeroed memory; say/print write the text and a newline, show the signed decimal and a newline;
;; check zero A stops with "line N: check zero failed: not the zero vector" and exit 1 when A is not 0; the end of the
;; program exits 0. One difference: text X "LIT" points X at one static copy of LIT (the interpreter makes a fresh copy
;; each time); a program that writes into a literal would see the difference (judge-v3.pmp does not).
;; Output is NASM source for Windows x64 (kernel32 only); nasm -f win64 and gcc as the linker driver make the .exe.
;; usage: racket pmpc.rkt PROGRAM.pmp OUT.asm
(require racket/string racket/list racket/file racket/port)

(define (die fmt . xs) (apply eprintf (string-append "pmpc: " fmt "\n") xs) (exit 2))

;; ---- reading: lines of tokens; ';' starts a comment outside a string; "..." is one token (kept with its quotes)
(define (tokenize-line s lno)
  (let loop ([i 0] [acc '()])
    (cond
      [(>= i (string-length s)) (reverse acc)]
      [else
       (define c (string-ref s i))
       (cond
         [(memv c '(#\space #\tab #\return)) (loop (add1 i) acc)]
         [(char=? c #\;) (reverse acc)]
         [(char=? c #\")
          (define j (let f ([k (add1 i)]) (cond [(>= k (string-length s)) (die "line ~a: unterminated string" lno)]
                                                [(char=? (string-ref s k) #\") k] [else (f (add1 k))])))
          (loop (add1 j) (cons (substring s i (add1 j)) acc))]
         [else
          (define j (let f ([k i]) (if (or (>= k (string-length s)) (memv (string-ref s k) '(#\space #\tab #\return #\;)))
                                       k (f (add1 k)))))
          (loop j (cons (substring s i j) acc))])])))

(define (int-token? t) (regexp-match? #px"^[0-9]+$" t))
(define (name-token? t) (regexp-match? #px"^[A-Za-z_][A-Za-z0-9_]*$" t))
(define (mangle t) (string-append "v_" t))
(define (lbl t) (string-append "L_" t))

;; ---- literals (the bytes between the quotes; \q is a double quote, as in the interpreter)
(define lits '())
(define (lit! tok)
  (define body (substring tok 1 (sub1 (string-length tok))))
  (define bytes (string->bytes/utf-8 (regexp-replace* #rx"\\\\q" body "\"")))
  (define name (format "lit_~a" (length lits)))
  (set! lits (cons (cons name bytes) lits))
  (values name (bytes-length bytes)))

(define vars (make-hash))
(define (var! t) (unless (name-token? t) (die "not a name: ~a" t)) (hash-set! vars t #t) (mangle t))

(define out (open-output-string))
(define (e fmt . xs) (write-string (apply format fmt xs) out) (newline out))

(define (load-op reg t)
  (cond [(int-token? t) (e "    mov ~a, ~a" reg t)]
        [else (e "    mov ~a, [~a]" reg (var! t))]))

(define (store x reg) (e "    mov [~a], ~a" (var! x) reg))

(define (width w) (or (string->number w) (die "bad width ~a" w)))

(define (stmt toks lno)
  (define (bad) (die "line ~a: cannot compile: ~a" lno (string-join toks " ")))
  (match-toks toks lno bad))

(define (match-toks toks lno bad)
  (define n (length toks))
  (define (t i) (list-ref toks i))
  (case (t 0)
    [("trace") (void)]
    [("label") (e "~a:" (lbl (t 1)))]
    [("goto") (e "    jmp ~a" (lbl (t 1)))]
    [("gosub") (e "    call ~a" (lbl (t 1)))]
    [("return") (e "    ret")]
    [("when")
     (unless (and (= n 5) (equal? (t 3) "goto")) (bad))
     (load-op "rax" (t 2))
     (e "    test rax, rax")
     (e "    ~a ~a" (case (t 1) [("zero") "jz"] [("nonzero") "jnz"] [("negative") "js"] [else (bad)]) (lbl (t 4)))]
    [("set")
     (define x (t 1))
     (case (t 2)
       [("const") (load-op "rax" (t 3)) (store x "rax")]
       [("add" "sub" "mul")
        (load-op "rax" (t 3)) (load-op "rcx" (t 4))
        (e "    ~a rax, rcx" (case (t 2) [("add") "add"] [("sub") "sub"] [("mul") "imul"]))
        (store x "rax")]
       [("peek")
        (load-op "rcx" (t 3))
        (case (width (t 4))
          [(1) (e "    movzx eax, byte [rcx]")] [(2) (e "    movzx eax, word [rcx]")]
          [(4) (e "    mov eax, dword [rcx]")] [(8) (e "    mov rax, [rcx]")] [else (bad)])
        (store x "rax")]
       [("alloc") (load-op "rcx" (t 3)) (e "    call rt_alloc") (store x "rax")]
       [else (bad)])]
    [("poke")
     (load-op "rcx" (t 1)) (load-op "rax" (t 3))
     (case (width (t 2))
       [(1) (e "    mov [rcx], al")] [(2) (e "    mov [rcx], ax")] [(4) (e "    mov [rcx], eax")] [(8) (e "    mov [rcx], rax")]
       [else (bad)])]
    [("text")
     (define x (t 1))
     (cond
       [(and (= n 3) (equal? (t 2) "arg"))
        (e "    call rt_arg") (store x "rax") (store (string-append x "_len") "rdx")]
       [(and (= n 3) (regexp-match? #rx"^\"" (t 2)))
        (define-values (nm len) (lit! (t 2)))
        (e "    lea rax, [~a]" nm) (store x "rax") (e "    mov rax, ~a" len) (store (string-append x "_len") "rax")]
       [else (bad)])]
    [("read")
     (define x (t 1)) (define f (t 2))
     (load-op "rcx" f) (e "    mov rdx, [~a]" (var! (string-append f "_len")))
     (e "    call rt_read") (store x "rax") (store (string-append x "_len") "rdx")]
    [("say")
     (unless (regexp-match? #rx"^\"" (t 1)) (bad))
     (define-values (nm len) (lit! (t 1)))
     (e "    lea rcx, [~a]" nm) (e "    mov rdx, ~a" len) (e "    call rt_line")]
    [("print")
     (load-op "rcx" (t 1)) (e "    mov rdx, [~a]" (var! (string-append (t 1) "_len"))) (e "    call rt_line")]
    [("show") (load-op "rcx" (t 1)) (e "    call rt_show")]
    [("check")
     (unless (and (= n 3) (equal? (t 1) "zero")) (bad))
     (load-op "rax" (t 2))
     (e "    test rax, rax")
     (e "    jz .ok~a" lno)
     (e "    mov rcx, ~a" lno)
     (e "    call rt_checkfail")
     (e ".ok~a:" lno)]
    [else (bad)]))

;; ---- the runtime: Windows x64, kernel32 only; every call into Windows from an aligned frame
(define runtime #<<END
; ---------------------------------------------------------------- runtime (pmpc)
rt_frame_in:
    ret
; rt_alloc(rcx = bytes) -> rax: zeroed, committed memory
rt_alloc:
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 48
    mov rdx, rcx
    xor ecx, ecx
    mov r8d, 0x3000
    mov r9d, 4
    call VirtualAlloc
    test rax, rax
    jnz .ok
    lea rcx, [msg_alloc]
    mov rdx, msg_alloc_len
    call rt_line
    mov ecx, 1
    call rt_exit
.ok:
    mov rsp, rbp
    pop rbp
    ret
; rt_out(rcx = bytes, rdx = len): into the output buffer
rt_out:
    push rsi
    push rdi
    mov rsi, rcx
.more:
    test rdx, rdx
    jz .done
    mov rax, [outpos]
    cmp rax, OUTSZ
    jb .room
    push rdx
    push rsi
    call rt_flush
    pop rsi
    pop rdx
    mov rax, [outpos]
.room:
    lea rdi, [outbuf]
    mov cl, [rsi]
    mov [rdi+rax], cl
    inc rax
    mov [outpos], rax
    inc rsi
    dec rdx
    jmp .more
.done:
    pop rdi
    pop rsi
    ret
rt_line:
    call rt_out
    lea rcx, [nl]
    mov rdx, 1
    jmp rt_out
; rt_show(rcx = signed word): decimal and a newline
rt_show:
    push rbx
    lea rbx, [numbuf+31]
    mov byte [rbx], 10
    mov rax, rcx
    xor r8d, r8d
    test rax, rax
    jns .pos
    neg rax
    mov r8d, 1
.pos:
    mov r9, 10
.dig:
    xor edx, edx
    div r9
    dec rbx
    add dl, '0'
    mov [rbx], dl
    test rax, rax
    jnz .dig
    test r8d, r8d
    jz .emit
    dec rbx
    mov byte [rbx], '-'
.emit:
    mov rcx, rbx
    lea rdx, [numbuf+32]
    sub rdx, rbx
    call rt_out
    pop rbx
    ret
; rt_flush: the buffer to standard output
rt_flush:
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 64
    mov rax, [outpos]
    test rax, rax
    jz .none
    mov rcx, [hout]
    lea rdx, [outbuf]
    mov r8, [outpos]
    lea r9, [written]
    mov qword [rsp+32], 0
    call WriteFile
    mov qword [outpos], 0
.none:
    mov rsp, rbp
    pop rbp
    ret
; rt_exit(rcx = code)
rt_exit:
    push rcx
    call rt_flush
    pop rcx
    and rsp, -16
    sub rsp, 32
    call ExitProcess
; rt_checkfail(rcx = source line)
rt_checkfail:
    push rcx
    lea rcx, [msg_line]
    mov rdx, 5
    call rt_out
    pop rcx
    push rcx
    call rt_show_noline
    lea rcx, [msg_check]
    mov rdx, msg_check_len
    call rt_line
    pop rcx
    mov ecx, 1
    call rt_exit
rt_show_noline:
    push rbx
    lea rbx, [numbuf+32]
    mov rax, rcx
    mov r9, 10
.dig:
    xor edx, edx
    div r9
    dec rbx
    add dl, '0'
    mov [rbx], dl
    test rax, rax
    jnz .dig
    mov rcx, rbx
    lea rdx, [numbuf+32]
    sub rdx, rbx
    call rt_out
    pop rbx
    ret
; rt_arg -> rax = the command-line argument after the program name, rdx = its length
rt_arg:
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 32
    call GetCommandLineA
    mov rsp, rbp
    pop rbp
    mov rcx, rax
    cmp byte [rcx], '"'
    jne .unq
    inc rcx
.q:
    mov dl, [rcx]
    test dl, dl
    jz .end
    inc rcx
    cmp dl, '"'
    jne .q
    jmp .sp
.unq:
    mov dl, [rcx]
    test dl, dl
    jz .end
    cmp dl, ' '
    je .sp
    inc rcx
    jmp .unq
.sp:
    cmp byte [rcx], ' '
    jne .end
    inc rcx
    jmp .sp
.end:
    mov rax, rcx
    xor edx, edx
.len:
    cmp byte [rax+rdx], 0
    je .trim
    inc rdx
    jmp .len
.trim:
    test rdx, rdx
    jz .done
    cmp byte [rax+rdx-1], ' '
    jne .done
    dec rdx
    jmp .trim
.done:
    ret
; rt_read(rcx = path, rdx = path length) -> rax = the file's bytes (zero-terminated), rdx = their number
rt_read:
    push rbp
    mov rbp, rsp
    push rbx
    push rsi
    push rdi
    push r12
    and rsp, -16
    sub rsp, 64
    lea rdi, [pathbuf]
    mov rsi, rcx
    mov rcx, rdx
    cmp rcx, 4000
    jb .cp
    mov rcx, 4000
.cp:
    rep movsb
    mov byte [rdi], 0
    lea rcx, [pathbuf]
    mov edx, 0x80000000
    mov r8d, 1
    xor r9d, r9d
    mov qword [rsp+32], 3
    mov qword [rsp+40], 0x80
    mov qword [rsp+48], 0
    call CreateFileA
    cmp rax, -1
    jne .opened
    lea rcx, [msg_open]
    mov rdx, msg_open_len
    call rt_line
    mov ecx, 1
    call rt_exit
.opened:
    mov rbx, rax
    mov rcx, rbx
    lea rdx, [fsize]
    call GetFileSizeEx
    mov rcx, [fsize]
    add rcx, 1
    call rt_alloc
    mov r12, rax
    xor esi, esi
.rd:
    mov rax, [fsize]
    sub rax, rsi
    jz .closed
    mov r8, rax
    cmp r8, 0x40000000
    jb .chunk
    mov r8, 0x40000000
.chunk:
    mov rcx, rbx
    lea rdx, [r12+rsi]
    lea r9, [got]
    mov qword [rsp+32], 0
    call ReadFile
    mov eax, [got]
    test eax, eax
    jz .closed
    add rsi, rax
    jmp .rd
.closed:
    mov rcx, rbx
    call CloseHandle
    mov byte [r12+rsi], 0
    mov rax, r12
    mov rdx, rsi
    lea rsp, [rbp-32]
    pop r12
    pop rdi
    pop rsi
    pop rbx
    pop rbp
    ret
END
  )

(module+ main
  (define args (current-command-line-arguments))
  (define src (vector-ref args 0))
  (define dst (vector-ref args 1))
  (define lines (file->lines src))
  (e "    ; ---- the program: ~a" src)
  (for ([s lines] [lno (in-naturals 1)])
    (define toks (tokenize-line s lno))
    (unless (null? toks) (stmt toks lno)))
  (e "    xor ecx, ecx")
  (e "    call rt_exit")
  (define prog (get-output-string out))
  (call-with-output-file dst #:exists 'error
    (lambda (o)
      (define (w . xs) (for ([x xs]) (write-string x o)) (newline o))
      (w "; written by pmpc.rkt from " src " -- the machine program of the pmp program, statement for statement")
      (w "bits 64")
      (w "default rel")
      (w "extern GetStdHandle, WriteFile, ExitProcess, CreateFileA, ReadFile, VirtualAlloc, GetCommandLineA, GetFileSizeEx, CloseHandle")
      (w "global start")
      (w "OUTSZ equ 1048576")
      (w "section .data")
      (w "nl: db 10")
      (w "msg_alloc: db 'alloc failed'")
      (w "msg_alloc_len equ $ - msg_alloc")
      (w "msg_open: db 'cannot open the file'")
      (w "msg_open_len equ $ - msg_open")
      (w "msg_line: db 'line '")
      (w "msg_check: db ': check zero failed: not the zero vector'")
      (w "msg_check_len equ $ - msg_check")
      (for ([l (reverse lits)])
        (w (car l) ": db " (string-join (append (for/list ([b (cdr l)]) (number->string b)) (list "0")) ", ")))
      (w "section .bss")
      (w "alignb 16")
      (w "outbuf: resb OUTSZ")
      (w "outpos: resq 1")
      (w "hout: resq 1")
      (w "written: resq 1")
      (w "fsize: resq 1")
      (w "got: resq 1")
      (w "numbuf: resb 40")
      (w "pathbuf: resb 4096")
      (for ([v (sort (hash-keys vars) string<?)]) (w (mangle v) ": resq 1"))
      (w "section .text")
      (w "start:")
      (w "    and rsp, -16")
      (w "    sub rsp, 32")
      (w "    mov ecx, -11")
      (w "    call GetStdHandle")
      (w "    mov [hout], rax")
      (write-string prog o)
      (write-string runtime o)
      (newline o)))
  (printf "pmpc: ~a statements' lines read, ~a variables, ~a literals -> ~a\n" (length lines) (hash-count vars) (length lits) dst))
