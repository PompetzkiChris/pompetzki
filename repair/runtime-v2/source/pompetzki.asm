; pompetzki.asm - the Pompetzki language, fourth cut. x64 assembly, NASM, Win64. No runtime, no library, no compiler
; behind it: the executable imports a handful of kernel32/shell32 functions and nothing else.
;
; The language:
;   - a value is a vector or a matrix over Q, exact, with numerators and denominators of any size; nothing is
;     ever rounded, the only limit is the arena (Menschenwerk)
;   - a program is a sequence of linear maps applied, composed, added, tensored (Kronecker), powered, inverted
;   - every map is checked by Rank-Nullity: dim(domain) = rank + nullity, by Gauss-Jordan elimination over Q
;   - the only predicate is zero: "check zero X" passes when X is the zero vector, and fails the program otherwise
;   - "check independent A B ..." fails when one of the maps is a combination of the others (dependent = dead code)
;   - "check orthogonal A B" fails unless A^T B = 0, the condition under which the two can run side by side
;   - kernel, image, left inverse (nullity 0), right inverse (full rank), solve, rref, iterate, projection
;
; Source is line-oriented. Words are separated by spaces; comments begin with ';'. Numbers are integers or
; fractions: 3, -7, 1/2, -22/7.
;   space V 3                                  a space named V of dimension 3
;   vector v : V [ 1 2 3 ]                     a vector in V (the ": V" may be left out)
;   map A : V -> W [ [ 1 0 0 ] [ 0 1 0 ] ]     a map, rows in brackets; ": V -> W" may be left out
;   let w apply A v                            w = A v
;   let C compose B A                          C = B A
;   let S add A B   /  let D sub A B           sums and differences of maps or vectors
;   let T tensor A B                           Kronecker product
;   let P power A 10                           A^10
;   let U transpose A                          A^T
;   let K scale 3/2 A                          (3/2) A
;   let K kernel A                             a basis of the kernel, one column each
;   let I image A                              a basis of the image, one column each
;   let L left inverse A                       L A = 1, exists when the nullity is 0
;   let R right inverse A                      A R = 1, exists when the rank is the dimension of the codomain
;   let B inverse A                            both at once
;   let x solve A b                            A x = b, fails when b is not in the image
;   let E rref A                               reduced row echelon form
;   let w iterate A 100 v                      A applied 100 times to v
;   let I identity 3 / augment A B / stack A B / directsum A B / entry v i / entry M i j
;   let t trace A / let d det A                exact scalars, as 1x1 values
;   let c charpoly A                           det(x - A), coefficients highest first; let Z evaluate c A is p(A)
;   let U orthogonalize A                      Gram-Schmidt on the columns, no roots, so no normalising
;   let P projector A                          A (A^T A)^-1 A^T, the orthogonal projection onto the image
;   load v file.txt / load matrix M file.txt  read a file of exact numbers; load v arg uses the command-line path
;   save v file.txt                           write a value out as exact numbers (round-trips with load)
;   let s total v                             the exact sum of every entry (the reconciliation primitive)
;   show X / show rank A / show nullity A      output
;   check zero X                               the predicate
;   check independent A B C                    the linter
;   check orthogonal A B                       the concurrency condition
;   check projection P                         P^2 = P
;   check injective A / surjective A / isomorphism A
; The imperative layer (extern, blob, set, poke, label, goto, gosub, return, when, show wide) is documented in
; README.md; it works on machine words and lets a program call Windows.
;
;   pompetzki.exe program.pmp [argument]         run
;   pompetzki.exe emit program.pmp output.exe    write a standalone executable of the program
; Build: nasm -f win64 pompetzki.asm -o pompetzki.obj
;        gcc -nostdlib -o pompetzki.exe pompetzki.obj -lkernel32 -lshell32 -Wl,-e,start -Wl,--subsystem,console

default rel
%ifndef LINUX
global start
extern GetStdHandle, WriteFile, ExitProcess, CreateFileA, ReadFile, VirtualAlloc, GetCommandLineA
extern LoadLibraryA, GetProcAddress, GetCommandLineW, CommandLineToArgvW, CreateFileW
extern GetModuleFileNameW, CloseHandle, GetLocalTime, GetFileSizeEx
%endif

MAXTOK equ 1000000
MAXSYM equ 16384
MAXDIM equ 4096
MAXRET equ 256
ARENA  equ 1024*1024*1024
MAGIC  equ 0x31494B5A4B504D50   ; 'PMPKZKI1'

section .data
msg_usage:     db 'pompetzki <program.pmp> [argument]   |   pompetzki emit <program.pmp> <output.exe>', 10
msg_usage_len  equ $ - msg_usage
msg_nofile:    db 'cannot open the program file', 10
msg_nofile_len equ $ - msg_nofile
msg_nowrite:   db 'cannot write the output file', 10
msg_nowrite_len equ $ - msg_nowrite
msg_loadfail:  db 'load: cannot open the data file', 10
msg_loadfail_len equ $ - msg_loadfail
msg_overflow:  db 'Menschenwerk: a value left the 64-bit integers. Nothing was rounded; the program stops.', 10
msg_overflow_len equ $ - msg_overflow
msg_arena:     db 'Menschenwerk: the arena is full. Nothing was rounded; the program stops.', 10
msg_arena_len  equ $ - msg_arena
msg_word:      db 'Menschenwerk: a machine word cannot hold this value', 10
msg_word_len   equ $ - msg_word
msg_divzero:   db 'division by zero', 10
msg_divzero_len equ $ - msg_divzero
msg_shape:     db 'shape: the dimensions do not match', 10
msg_shape_len  equ $ - msg_shape
msg_unknown:   db 'unknown name', 10
msg_unknown_len equ $ - msg_unknown
msg_syntax:    db 'syntax', 10
msg_syntax_len equ $ - msg_syntax
msg_notzero:   db 'check zero failed: not the zero vector', 10
msg_notzero_len equ $ - msg_notzero
msg_dependent: db 'check independent failed: one of these maps is a combination of the others', 10
msg_dependent_len equ $ - msg_dependent
msg_notorth:   db 'check orthogonal failed: A^T B is not zero', 10
msg_notorth_len equ $ - msg_notorth
msg_notproj:   db 'check projection failed: P^2 is not P', 10
msg_notproj_len equ $ - msg_notproj
msg_notinj:    db 'check injective failed: the kernel is not zero', 10
msg_notinj_len equ $ - msg_notinj
msg_notsur:    db 'check surjective failed: the image is not the whole space', 10
msg_notsur_len equ $ - msg_notsur
msg_notiso:    db 'check isomorphism failed: the map is not both injective and surjective', 10
msg_notiso_len equ $ - msg_notiso
msg_noleft:    db 'left inverse: the map is not injective (its kernel is not zero)', 10
msg_noleft_len equ $ - msg_noleft
msg_noright:   db 'right inverse: the map is not surjective (its image is not the whole space)', 10
msg_noright_len equ $ - msg_noright
msg_nosol:     db 'solve: the vector is not in the image', 10
msg_nosol_len  equ $ - msg_nosol
msg_norefute:  db 'refute: the system is solvable, so no impossibility certificate exists', 10
msg_norefute_len equ $ - msg_norefute
msg_nonull:    db 'nullvector: the map is injective (nullity 0), so no nonzero null vector exists', 10
msg_nonull_len equ $ - msg_nonull
msg_nocow:     db 'cowitness: the map is surjective, so no nonzero covector vanishes on its image', 10
msg_nocow_len  equ $ - msg_nocow
msg_noproc:    db 'record: no process is open (use `process "path"` first)', 10
msg_noproc_len equ $ - msg_noproc
msg_ok_nonzero: db 'nonzero: yes', 10
msg_ok_nonzero_len equ $ - msg_ok_nonzero
msg_notnonzero: db 'check nonzero failed: it is the zero', 10
msg_notnonzero_len equ $ - msg_notnonzero
msg_ok_nonneg: db 'nonnegative: yes', 10
msg_ok_nonneg_len equ $ - msg_ok_nonneg
msg_notnonneg: db 'check nonnegative failed: an entry is negative', 10
msg_notnonneg_len equ $ - msg_notnonneg
msg_noquot: db 'quotient: the second span is not inside the first', 10
msg_noquot_len equ $ - msg_noquot
msg_nobdry: db 'homology: the boundary of a boundary is not zero', 10
msg_nobdry_len equ $ - msg_nobdry
msg_ok_exact: db 'exact: yes', 10
msg_ok_exact_len equ $ - msg_ok_exact
msg_notexact: db 'check exact failed: the image is not the kernel', 10
msg_notexact_len equ $ - msg_notexact
msg_proc_failed: db 'FAILED ', 0
msg_proc_end: db 'end: every obligation discharged', 10
msg_proc_end_len equ $ - msg_proc_end
msg_norelease: db 'release: no mark is set', 10
msg_norelease_len equ $ - msg_norelease
msg_claimrel: db 'release: an open claim refers to a value inside the block', 10
msg_claimrel_len equ $ - msg_claimrel
msg_rebound: db 'release: a value named before the mark was rebound inside the block', 10
msg_rebound_len equ $ - msg_rebound
msg_proc_run: db '==== run ', 0
msg_proc_run_end: db ' ====', 10, 0
msg_square:    db 'power needs a square matrix', 10
msg_notsq:     db 'this needs a square matrix', 10
msg_notsq_len  equ $ - msg_notsq
msg_noproj:    db 'projector: the columns are dependent, so A^T A has no inverse', 10
msg_noproj_len equ $ - msg_noproj
msg_notorthc:  db 'check orthogonal failed: two of the columns are not orthogonal', 10
msg_notorthc_len equ $ - msg_notorthc
msg_square_len equ $ - msg_square
msg_space:     db 'the declared space does not match the value', 10
msg_space_len  equ $ - msg_space
msg_noret:     db 'return without gosub', 10
msg_noret_len  equ $ - msg_noret
msg_deep:      db 'gosub: too deep', 10
msg_deep_len   equ $ - msg_deep
msg_rank:      db '  rank ', 0
msg_nullity:   db '  nullity ', 0
msg_colon:     db ' : Q^', 0
msg_arrow:     db ' -> Q^', 0
msg_bytes:     db ' bytes', 10
msg_bytes_len  equ $ - msg_bytes
msg_ok_zero:   db 'zero: yes', 10
msg_ok_zero_len equ $ - msg_ok_zero
msg_ok_ind:    db 'independent: yes', 10
msg_ok_ind_len equ $ - msg_ok_ind
msg_ok_orth:   db 'orthogonal: yes', 10
msg_ok_orth_len equ $ - msg_ok_orth
msg_ok_proj:   db 'projection: yes', 10
msg_ok_proj_len equ $ - msg_ok_proj
msg_ok_inj:    db 'injective: yes', 10
msg_ok_inj_len equ $ - msg_ok_inj
msg_ok_sur:    db 'surjective: yes', 10
msg_ok_sur_len equ $ - msg_ok_sur
msg_ok_iso:    db 'isomorphism: yes', 10
msg_ok_iso_len equ $ - msg_ok_iso
kw_space:      db 'space', 0
kw_vector:     db 'vector', 0
kw_map:        db 'map', 0
kw_let:        db 'let', 0
kw_show:       db 'show', 0
kw_check:      db 'check', 0
kw_apply:      db 'apply', 0
kw_compose:    db 'compose', 0
kw_add:        db 'add', 0
kw_sub:        db 'sub', 0
kw_tensor:     db 'tensor', 0
kw_power:      db 'power', 0
kw_transpose:  db 'transpose', 0
kw_scale:      db 'scale', 0
kw_kernel:     db 'kernel', 0
kw_image:      db 'image', 0
kw_left:       db 'left', 0
kw_right:      db 'right', 0
kw_inverse:    db 'inverse', 0
kw_leftinverse: db 'leftinverse', 0
kw_rightinverse: db 'rightinverse', 0
kw_solve:      db 'solve', 0
kw_rref:       db 'rref', 0
kw_iterate:    db 'iterate', 0
kw_identity:   db 'identity', 0
kw_augment:    db 'augment', 0
kw_stack:      db 'stack', 0
kw_directsum:  db 'directsum', 0
kw_trace:      db 'trace', 0
kw_det:        db 'det', 0
kw_charpoly:   db 'charpoly', 0
kw_evaluate:   db 'evaluate', 0
kw_orthogonalize: db 'orthogonalize', 0
kw_projector:  db 'projector', 0
kw_entry:      db 'entry', 0
kw_load:       db 'load', 0
kw_save:       db 'save', 0
kw_matrix:     db 'matrix', 0
kw_total:      db 'total', 0
kw_refute:     db 'refute', 0
kw_nullvector: db 'nullvector', 0
kw_cowitness:  db 'cowitness', 0
kw_complement: db 'complement', 0
kw_block:      db 'block', 0
kw_polymul:    db 'polymul', 0
kw_polyadd:    db 'polyadd', 0
kw_polysub:    db 'polysub', 0
kw_polyquo:    db 'polyquo', 0
kw_polyrem:    db 'polyrem', 0
kw_vec:        db 'vec', 0
kw_diagonal:   db 'diagonal', 0
kw_nonnegative: db 'nonnegative', 0
kw_quotient:   db 'quotient', 0
kw_homology:   db 'homology', 0
kw_exact:      db 'exact', 0
kw_blockdet:   db 'blockdet', 0
kw_blocktrace: db 'blocktrace', 0
kw_diag:       db 'diag', 0
kw_unvec:      db 'unvec', 0
kw_blockmul:   db 'blockmul', 0
kw_arena:      db 'arena', 0
kw_mark:       db 'mark', 0
kw_release:    db 'release', 0
kw_on:         db 'on', 0
kw_off:        db 'off', 0
kw_claim:      db 'claim', 0
kw_established: db 'established', 0
kw_equal:      db 'equal', 0
kw_noninjective: db 'noninjective', 0
kw_nonsurjective: db 'nonsurjective', 0
kw_solvable:   db 'solvable', 0
kw_unsolvable: db 'unsolvable', 0
kw_boundary:   db 'boundary', 0
kw_notboundary: db 'notboundary', 0
kw_cost:       db 'cost', 0
kw_minpoly:    db 'minpoly', 0
kw_companion:  db 'companion', 0
kw_polygcd:    db 'polygcd', 0
kw_polyderiv:  db 'polyderiv', 0
kw_rows:       db 'rows', 0
kw_cols:       db 'cols', 0
kw_say:        db 'say', 0
kw_process:    db 'process', 0
kw_chapter:    db 'chapter', 0
kw_use:        db 'use', 0
kw_push:       db 'push', 0
kw_pop:        db 'pop', 0
kw_library:    db 'library', 0
kw_record:     db 'record', 0
kw_value:      db 'value', 0
kw_nonzero_c:  db 'nonzero', 0
kw_rank:       db 'rank', 0
kw_nullity:    db 'nullity', 0
kw_zero:       db 'zero', 0
kw_independent: db 'independent', 0
kw_orthogonal: db 'orthogonal', 0
kw_projection: db 'projection', 0
kw_injective:  db 'injective', 0
kw_surjective: db 'surjective', 0
kw_isomorphism: db 'isomorphism', 0
kw_colon:      db ':', 0
kw_arrow:      db '->', 0
; --- the imperative / OS layer ---
kw_extern:     db 'extern', 0
kw_blob:       db 'blob', 0
kw_set:        db 'set', 0
kw_poke:       db 'poke', 0
kw_label:      db 'label', 0
kw_goto:       db 'goto', 0
kw_gosub:      db 'gosub', 0
kw_return:     db 'return', 0
kw_when:       db 'when', 0
kw_wide:       db 'wide', 0
kw_nonzero:    db 'nonzero', 0
kw_negative:   db 'negative', 0
kw_call:       db 'call', 0
kw_vcall:      db 'vcall', 0
kw_peek:       db 'peek', 0
kw_alloc:      db 'alloc', 0
kw_arg:        db 'arg', 0
kw_const:      db 'const', 0
kw_mul:        db 'mul', 0
kw_shl:        db 'shl', 0
kw_shr:        db 'shr', 0
kw_band:       db 'band', 0
kw_bor:        db 'bor', 0
msg_extern:    db 'extern: DLL or function not found', 10
msg_extern_len equ $ - msg_extern
wemit:         dw 'e', 'm', 'i', 't', 0

section .bss
hstdout:   resq 1
outbuf:    resb 65536
outlen:    resq 1
srcptr:    resq 1
srclen:    resq 1
selfptr:   resq 1               ; this executable's own image, read from disk
selflen:   resq 1
arena:     resq 1
arena_end: resq 1
tokens:    resq MAXTOK*3        ; ptr, len, type (0 word, 1 '[', 2 ']', 3 newline)
ntok:      resq 1
symbols:   resq MAXSYM*4        ; name ptr, name len, kind (1 space, 2 value, 3 machine word, 4 label), payload
nsym:      resq 1
cur:       resq 1               ; current token index
lineno:    resq 1
pivots:    resq MAXDIM          ; pivot columns of the last elimination
retstack:  resq MAXRET          ; gosub return points (token indices)
retsp:     resq 1
bn_zero:   resq 1               ; the shared constants 0 and 1
bn_one:    resq 1
bn_ten:    resq 1
q_zero:    resq 1
q_one:     resq 1
argbuf:    resb 1024
callargs:  resq 16               ; up to 8 integer arguments for a foreign call
titleptr:  resq 1               ; UTF-16 argument from the command line, or 0 (the program reads it with `arg`)
wpath:     resq 1               ; UTF-16 path of the .pmp program
wargc:     resd 1               ; argument count from CommandLineToArgvW
wbuf:      resw 32768           ; this executable's path
namebuf1:  resb 256             ; scratch for a DLL name
namebuf2:  resb 256             ; scratch for a function name
savedh:    resq 1               ; stdout handle saved across a save
proch:     resq 1               ; the process-log file handle, or 0
procpathw: resw 1040            ; the process log path, wide, built next to the program
arena_mark: resq 1             ; arena position at the last `arena mark`
mark_nsym:  resq 1             ; symbol count at the last mark
marked:     resq 1             ; 1 when a mark is set
arena_base: resq 1             ; the arena at the start of the run (a chapter releases back to it)
orig_title: resq 1             ; the command-line argument, restored by a chapter without one
chapargw:   resw 1040          ; a chapter's argument, wide
nchapters:  resq 1
chap_argtok: resq 1            ; token index of the chapter's argument, or -1
top_proch:  resq 1             ; the one program's own Process log, kept while a chapter's is open
traceoff:   resq 1             ; 1 while `trace off` is in force
tokline:    resq MAXTOK        ; for each newline token, the number of the line it ends
nlseen:     resq 1             ; newline tokens seen while tokenizing

section .text

; ============================================================ output
; ============================================================ twenty-second cut: Linux
; The algebra never touches the operating system; the interpreter reaches it through sixteen kernel32/shell32 entry
; points (files, stdout, the arena, the command line, the clock, the loader) and, for `extern`, whatever the program
; names. Assembled with -DLINUX (nasm -f elf64), those entry points are the routines below over raw Linux syscalls,
; keeping the Win64 calling convention the rest of the interpreter uses (rcx rdx r8 r9, stack args, rbx rbp rsi rdi
; r12-r15 preserved). `extern` on Linux resolves the names the shipped programs use -- ws2_32 (sockets), Sleep,
; CreateDirectoryA, ShellExecuteA (fork + execve) -- and refuses the rest. Times in the Process are UTC on Linux.
%ifdef LINUX
section .data
lin_selfexe:   db '/proc/self/exe', 0
lin_ws2:       db 'ws2_32.dll', 0
lin_k32:       db 'kernel32.dll', 0
lin_sh32:      db 'shell32.dll', 0
lin_names:     db 'WSAStartup', 0, 'socket', 0, 'connect', 0, 'send', 0, 'recv', 0, 'closesocket', 0, 'htons', 0, 'inet_addr', 0
               db 'Sleep', 0, 'CreateDirectoryA', 0, 'ShellExecuteA', 0, 'CloseHandle', 0, 0
lin_procs:     dq lin_WSAStartup, lin_socket, lin_connect, lin_send, lin_recv, lin_closesocket, lin_htons, lin_inet_addr
               dq lin_Sleep, lin_CreateDirectoryA, lin_ShellExecuteA, CloseHandle
section .bss
lin_argc:      resq 1
lin_argv:      resq 1
lin_wargv:     resq 65
lin_wpool:     resw 65536
lin_path:      resb 8192
lin_exe:       resb 4096
lin_stat:      resb 160
lin_ts:        resq 2
lin_xargv:     resq 66
lin_xbuf:      resb 8192
section .text
global _start
_start:
    mov rax, [rsp]
    mov [lin_argc], rax
    lea rax, [rsp+8]
    mov [lin_argv], rax
    sub rsp, 8                  ; as if called: rsp = 8 mod 16, the way Windows enters `start`
    jmp start

; ---- UTF-16 <-> UTF-8 into static buffers (rsi = source, rdi = destination; both NUL-terminated)
lin_w2u:                        ; UTF-16 at rsi -> UTF-8 at rdi
    push rbx
.l:
    movzx eax, word [rsi]
    add rsi, 2
    test eax, eax
    jz .d
    cmp eax, 0xD800
    jb .put
    cmp eax, 0xDBFF
    ja .put
    movzx ecx, word [rsi]
    cmp ecx, 0xDC00
    jb .put
    cmp ecx, 0xDFFF
    ja .put
    add rsi, 2
    sub eax, 0xD800
    shl eax, 10
    sub ecx, 0xDC00
    add eax, ecx
    add eax, 0x10000
.put:
    cmp eax, 0x80
    jb .one
    cmp eax, 0x800
    jb .two
    cmp eax, 0x10000
    jb .three
    mov ecx, eax
    shr ecx, 18
    or cl, 0xF0
    mov [rdi], cl
    mov ecx, eax
    shr ecx, 12
    and cl, 0x3F
    or cl, 0x80
    mov [rdi+1], cl
    mov ecx, eax
    shr ecx, 6
    and cl, 0x3F
    or cl, 0x80
    mov [rdi+2], cl
    and al, 0x3F
    or al, 0x80
    mov [rdi+3], al
    add rdi, 4
    jmp .l
.three:
    mov ecx, eax
    shr ecx, 12
    or cl, 0xE0
    mov [rdi], cl
    mov ecx, eax
    shr ecx, 6
    and cl, 0x3F
    or cl, 0x80
    mov [rdi+1], cl
    and al, 0x3F
    or al, 0x80
    mov [rdi+2], al
    add rdi, 3
    jmp .l
.two:
    mov ecx, eax
    shr ecx, 6
    or cl, 0xC0
    mov [rdi], cl
    and al, 0x3F
    or al, 0x80
    mov [rdi+1], al
    add rdi, 2
    jmp .l
.one:
    mov [rdi], al
    inc rdi
    jmp .l
.d:
    mov byte [rdi], 0
    pop rbx
    ret

lin_u2w:                        ; UTF-8 at rsi -> UTF-16 at rdi; -> rdi past the terminator
.l:
    movzx eax, byte [rsi]
    inc rsi
    test eax, eax
    jz .d
    cmp eax, 0x80
    jb .put
    cmp eax, 0xE0
    jb .two
    cmp eax, 0xF0
    jb .three
    and eax, 7
    shl eax, 18
    movzx ecx, byte [rsi]
    and ecx, 0x3F
    shl ecx, 12
    or eax, ecx
    movzx ecx, byte [rsi+1]
    and ecx, 0x3F
    shl ecx, 6
    or eax, ecx
    movzx ecx, byte [rsi+2]
    and ecx, 0x3F
    or eax, ecx
    add rsi, 3
    sub eax, 0x10000
    mov ecx, eax
    shr ecx, 10
    add ecx, 0xD800
    mov [rdi], cx
    and eax, 0x3FF
    add eax, 0xDC00
    mov [rdi+2], ax
    add rdi, 4
    jmp .l
.three:
    and eax, 15
    shl eax, 12
    movzx ecx, byte [rsi]
    and ecx, 0x3F
    shl ecx, 6
    or eax, ecx
    movzx ecx, byte [rsi+1]
    and ecx, 0x3F
    or eax, ecx
    add rsi, 2
    jmp .put
.two:
    and eax, 0x1F
    shl eax, 6
    movzx ecx, byte [rsi]
    and ecx, 0x3F
    or eax, ecx
    inc rsi
.put:
    mov [rdi], ax
    add rdi, 2
    jmp .l
.d:
    mov word [rdi], 0
    add rdi, 2
    ret

; ---- the sixteen entry points
GetStdHandle:                   ; -10, -11, -12 -> 0, 1, 2
    mov rax, rcx
    neg rax
    sub rax, 10
    ret

WriteFile:                      ; (h, buf, len, &written, overlapped) -> 1 / 0
    push rdi
    push rsi
    push r9
    mov rdi, rcx
    mov rsi, rdx
    mov rdx, r8
    mov eax, 1
    syscall
    pop r9
    test rax, rax
    js .fail
    mov [r9], eax
    mov eax, 1
    jmp .out
.fail:
    mov dword [r9], 0
    xor eax, eax
.out:
    pop rsi
    pop rdi
    ret

ReadFile:                       ; (h, buf, len, &read, overlapped) -> 1 / 0
    push rdi
    push rsi
    push r9
    mov rdi, rcx
    mov rsi, rdx
    mov rdx, r8
    xor eax, eax
    syscall
    pop r9
    test rax, rax
    js .fail
    mov [r9], eax
    mov eax, 1
    jmp .out
.fail:
    mov dword [r9], 0
    xor eax, eax
.out:
    pop rsi
    pop rdi
    ret

ExitProcess:                    ; (code)
    mov edi, ecx
    mov eax, 231
    syscall

VirtualAlloc:                   ; (addr, size, type, protect) -> mmap or 0
    push rdi
    push rsi
    xor edi, edi
    mov rsi, rdx
    mov edx, 3                  ; PROT_READ | PROT_WRITE
    mov r10d, 0x22              ; MAP_PRIVATE | MAP_ANONYMOUS
    mov r8, -1
    xor r9d, r9d
    mov eax, 9
    syscall
    test rax, rax
    jns .ok
    xor eax, eax
.ok:
    pop rsi
    pop rdi
    ret

lin_open:                       ; rdi = path, esi = access, edx = disposition -> rax = fd or -1
    push rdi
    push rsi
    mov r10d, 0                 ; O_RDONLY
    test esi, 0x40000000        ; GENERIC_WRITE
    jz .append
    mov r10d, 0x241             ; O_WRONLY | O_CREAT | O_TRUNC
    jmp .go
.append:
    test esi, 4                 ; FILE_APPEND_DATA
    jz .go
    mov r10d, 0x441             ; O_WRONLY | O_CREAT | O_APPEND
.go:
    mov rsi, r10
    mov edx, 0o644
    mov eax, 2
    syscall
    test rax, rax
    jns .ok
    mov rax, -1
.ok:
    pop rsi
    pop rdi
    ret

CreateFileA:                    ; (path, access, share, sa, disposition, flags, template) -> fd or -1
    push rdi
    push rsi
    mov rdi, rcx
    mov esi, edx
    mov edx, [rsp+16+40]
    call lin_open
    pop rsi
    pop rdi
    ret

CreateFileW:                    ; the same, the path in UTF-16
    push rdi
    push rsi
    push rdx
    mov rsi, rcx
    lea rdi, [lin_path]
    call lin_w2u
    pop rdx
    lea rdi, [lin_path]
    mov esi, edx
    mov edx, [rsp+16+40]
    call lin_open
    pop rsi
    pop rdi
    ret

GetFileSizeEx:                  ; (h, &size) -> 1
    push rdi
    push rsi
    push rdx
    mov rdi, rcx
    lea rsi, [lin_stat]
    mov eax, 5                  ; fstat
    syscall
    pop rdx
    mov rax, [lin_stat+48]      ; st_size
    mov [rdx], rax
    mov eax, 1
    pop rsi
    pop rdi
    ret

CloseHandle:                    ; (h) -> 1
    push rdi
    mov rdi, rcx
    mov eax, 3
    syscall
    mov eax, 1
    pop rdi
    ret

GetLocalTime:                   ; (&SYSTEMTIME): UTC from the realtime clock, the civil date from the day count
    push rbx
    push rdi
    push rsi
    push r12
    mov rbx, rcx
    xor edi, edi
    lea rsi, [lin_ts]
    mov eax, 228                ; clock_gettime(CLOCK_REALTIME)
    syscall
    mov rax, [lin_ts]           ; seconds
    xor edx, edx
    mov rcx, 86400
    div rcx                     ; rax = days, rdx = seconds of the day
    mov r12, rdx
    ; day of week: 1970-01-01 was a Thursday (4)
    lea rcx, [rax+4]
    push rax
    mov rax, rcx
    xor edx, edx
    mov rcx, 7
    div rcx
    mov [rbx+4], dx
    pop rax
    ; civil from days (proleptic Gregorian)
    add rax, 719468             ; z
    xor edx, edx
    mov rcx, 146097
    div rcx                     ; rax = era, rdx = doe
    mov r8, rax                 ; era
    mov r9, rdx                 ; doe
    ; yoe = (doe - doe/1460 + doe/36524 - doe/146096) / 365
    mov rax, r9
    xor edx, edx
    mov rcx, 1460
    div rcx
    mov r10, r9
    sub r10, rax
    mov rax, r9
    xor edx, edx
    mov rcx, 36524
    div rcx
    add r10, rax
    mov rax, r9
    xor edx, edx
    mov rcx, 146096
    div rcx
    sub r10, rax
    mov rax, r10
    xor edx, edx
    mov rcx, 365
    div rcx
    mov r10, rax                ; yoe
    ; doy = doe - (365 yoe + yoe/4 - yoe/100)
    mov rax, r10
    imul rax, 365
    mov rcx, r10
    shr rcx, 2
    add rax, rcx
    mov rcx, r10
    push rax
    mov rax, rcx
    xor edx, edx
    mov rcx, 100
    div rcx
    mov rcx, rax
    pop rax
    sub rax, rcx
    mov r11, r9
    sub r11, rax                ; doy
    ; mp = (5 doy + 2) / 153 ; d = doy - (153 mp + 2)/5 + 1 ; m = mp < 10 ? mp + 3 : mp - 9
    lea rax, [r11*4+r11]
    add rax, 2
    xor edx, edx
    mov rcx, 153
    div rcx
    mov rdi, rax                ; mp
    imul rax, 153
    add rax, 2
    xor edx, edx
    mov rcx, 5
    div rcx
    mov rcx, r11
    sub rcx, rax
    inc rcx
    mov [rbx+6], cx             ; day
    mov rax, rdi
    cmp rax, 10
    jb .m1
    sub rax, 9
    jmp .m2
.m1:
    add rax, 3
.m2:
    mov [rbx+2], ax             ; month
    ; y = yoe + era*400 (+1 when month <= 2)
    mov rcx, r8
    imul rcx, 400
    add rcx, r10
    cmp ax, 2
    ja .y
    inc rcx
.y:
    mov [rbx], cx               ; year
    mov rax, r12
    xor edx, edx
    mov rcx, 3600
    div rcx
    mov [rbx+8], ax             ; hour
    mov rax, rdx
    xor edx, edx
    mov rcx, 60
    div rcx
    mov [rbx+10], ax            ; minute
    mov [rbx+12], dx            ; second
    mov rax, [lin_ts+8]
    xor edx, edx
    mov rcx, 1000000
    div rcx
    mov [rbx+14], ax            ; milliseconds
    pop r12
    pop rsi
    pop rdi
    pop rbx
    ret

GetModuleFileNameW:             ; (module, buf, capacity) -> the path of this executable, UTF-16
    push rdi
    push rsi
    push rdx
    lea rdi, [lin_selfexe]
    lea rsi, [lin_exe]
    mov edx, 4095
    mov eax, 89                 ; readlink
    syscall
    test rax, rax
    js .none
    mov byte [lin_exe+rax], 0
    jmp .conv
.none:
    mov byte [lin_exe], 0
.conv:
    pop rdi
    lea rsi, [lin_exe]
    call lin_u2w
    mov eax, 1
    pop rsi
    pop rdi
    ret

GetCommandLineW:
    lea rax, [lin_argc]
    ret

CommandLineToArgvW:             ; (cmdline, &argc) -> the argv as UTF-16 strings, from the Linux argv
    push rbx
    push rdi
    push rsi
    push r12
    mov rbx, rdx
    mov r12, [lin_argc]
    cmp r12, 64
    jle .n
    mov r12, 64
.n:
    mov [rbx], r12d
    lea rdi, [lin_wpool]
    xor ecx, ecx
.l:
    cmp rcx, r12
    jge .d
    mov rax, [lin_argv]
    mov rsi, [rax+rcx*8]
    lea rax, [lin_wargv]
    mov [rax+rcx*8], rdi
    push rcx
    call lin_u2w
    pop rcx
    inc rcx
    jmp .l
.d:
    lea rax, [lin_wargv]
    pop r12
    pop rsi
    pop rdi
    pop rbx
    ret

lin_streq:                      ; rcx = a, rdx = b -> eax 1/0
.l:
    mov al, [rcx]
    cmp al, [rdx]
    jne .no
    test al, al
    jz .yes
    inc rcx
    inc rdx
    jmp .l
.yes:
    mov eax, 1
    ret
.no:
    xor eax, eax
    ret

LoadLibraryA:                   ; the three libraries the shipped programs name
    push rbx
    mov rbx, rcx
    lea rdx, [lin_ws2]
    call lin_streq
    test eax, eax
    jnz .one
    mov rcx, rbx
    lea rdx, [lin_k32]
    call lin_streq
    test eax, eax
    jnz .two
    mov rcx, rbx
    lea rdx, [lin_sh32]
    call lin_streq
    test eax, eax
    jnz .three
    xor eax, eax
    pop rbx
    ret
.one:
    mov eax, 1
    pop rbx
    ret
.two:
    mov eax, 2
    pop rbx
    ret
.three:
    mov eax, 3
    pop rbx
    ret

GetProcAddress:                 ; (module, name) -> the emulation, or 0
    push rbx
    push r12
    mov rbx, rdx
    lea r12, [lin_names]
    xor r8d, r8d
.l:
    cmp byte [r12], 0
    je .none
    mov rcx, r12
    mov rdx, rbx
    push r8
    call lin_streq
    pop r8
    test eax, eax
    jnz .hit
.skip:
    inc r12
    cmp byte [r12-1], 0
    jne .skip
    inc r8
    jmp .l
.hit:
    lea rax, [lin_procs]
    mov rax, [rax+r8*8]
    pop r12
    pop rbx
    ret
.none:
    mov rdx, rbx
    call lin_GetProcAddress2
    pop r12
    pop rbx
    ret

; ---- the emulated imports (Win64 convention in, Linux syscalls inside)
lin_WSAStartup:
    xor eax, eax
    ret

lin_socket:                     ; (af, type, protocol) -> fd or -1
    push rdi
    push rsi
    mov edi, ecx
    mov esi, edx
    mov edx, r8d
    mov eax, 41
    syscall
    test rax, rax
    jns .ok
    mov rax, -1
.ok:
    pop rsi
    pop rdi
    ret

lin_connect:                    ; (s, addr, len) -> 0 or nonzero
    push rdi
    push rsi
    mov rdi, rcx
    mov rsi, rdx
    mov edx, r8d
    mov eax, 42
    syscall
    pop rsi
    pop rdi
    ret

lin_send:                       ; (s, buf, len, flags) -> n or negative
    push rdi
    push rsi
    mov rdi, rcx
    mov rsi, rdx
    mov rdx, r8
    mov r10d, 0x4000            ; MSG_NOSIGNAL
    xor r8d, r8d
    xor r9d, r9d
    mov eax, 44
    syscall
    pop rsi
    pop rdi
    ret

lin_recv:                       ; (s, buf, len, flags) -> n or negative
    push rdi
    push rsi
    mov rdi, rcx
    mov rsi, rdx
    mov rdx, r8
    xor r10d, r10d
    xor r8d, r8d
    xor r9d, r9d
    mov eax, 45
    syscall
    pop rsi
    pop rdi
    ret

lin_closesocket:
    jmp CloseHandle

lin_htons:
    mov eax, ecx
    xchg al, ah
    movzx eax, ax
    ret

lin_inet_addr:                  ; "a.b.c.d" -> the four bytes in order
    xor eax, eax
    xor r8d, r8d                ; result
    xor r9d, r9d                ; shift
.oct:
    xor edx, edx
.dig:
    movzx r10d, byte [rcx]
    sub r10d, '0'
    cmp r10d, 9
    ja .end
    imul edx, 10
    add edx, r10d
    inc rcx
    jmp .dig
.end:
    mov r10d, r9d
    xchg ecx, r10d
    shl edx, cl
    xchg ecx, r10d
    or r8d, edx
    add r9d, 8
    cmp byte [rcx], '.'
    jne .d
    inc rcx
    cmp r9d, 32
    jb .oct
.d:
    mov eax, r8d
    ret

lin_Sleep:                      ; (ms)
    push rdi
    push rsi
    mov eax, ecx
    xor edx, edx
    mov ecx, 1000
    div ecx
    mov [lin_ts], rax
    imul rdx, 1000000
    mov [lin_ts+8], rdx
    lea rdi, [lin_ts]
    xor esi, esi
    mov eax, 35                 ; nanosleep
    syscall
    pop rsi
    pop rdi
    ret

lin_CreateDirectoryA:           ; (path, sa) -> 1 / 0
    push rdi
    push rsi
    mov rdi, rcx
    mov esi, 0o755
    mov eax, 83                 ; mkdir
    syscall
    test rax, rax
    jnz .no
    mov eax, 1
    jmp .out
.no:
    xor eax, eax
.out:
    pop rsi
    pop rdi
    ret

lin_ShellExecuteA:              ; (hwnd, verb, file, params, dir, show): fork, then execve(file, [file params...], envp)
    push rbx
    push rdi
    push rsi
    push r12
    mov rbx, r8                 ; file
    mov r12, r9                 ; params
    ; split the parameters on spaces into lin_xbuf / lin_xargv
    lea rax, [lin_xargv]
    mov [rax], rbx
    lea rdi, [lin_xbuf]
    mov rsi, r12
    mov ecx, 1
.sp:
    cmp byte [rsi], ' '
    jne .tok
    inc rsi
    jmp .sp
.tok:
    cmp byte [rsi], 0
    je .done
    cmp ecx, 64
    jge .done
    lea rax, [lin_xargv]
    mov [rax+rcx*8], rdi
    inc ecx
.cp:
    mov al, [rsi]
    test al, al
    jz .tokend
    cmp al, ' '
    je .tokend
    mov [rdi], al
    inc rdi
    inc rsi
    jmp .cp
.tokend:
    mov byte [rdi], 0
    inc rdi
    jmp .sp
.done:
    lea rax, [lin_xargv]
    mov qword [rax+rcx*8], 0
    mov eax, 57                 ; fork
    syscall
    test rax, rax
    jnz .parent
    mov rdi, rbx
    lea rsi, [lin_xargv]
    mov rdx, [lin_argv]
    mov rax, [lin_argc]
    lea rdx, [rdx+rax*8+8]      ; envp follows argv's NULL
    mov eax, 59                 ; execve
    syscall
    mov edi, 127
    mov eax, 231
    syscall
.parent:
    mov eax, 42                 ; > 32: success, as ShellExecute reports it
    pop r12
    pop rsi
    pop rdi
    pop rbx
    ret

; ---- twenty-fourth cut: processes, directories and the clock, so the tools written in the language run here too
;      CreateProcessA (fork + execve of the command line split on spaces, stdout/stderr from STARTUPINFO's handles),
;      WaitForSingleObject (wait4), GetExitCodeProcess, GetFileAttributesA (stat), GetTickCount64, GetCurrentDirectoryA,
;      DeleteFileA (unlink), FindFirstFileA / FindNextFileA / FindClose (getdents64 filtered by the pattern's suffix)
section .data
lin_names2:    db 'CreateProcessA', 0, 'WaitForSingleObject', 0, 'GetExitCodeProcess', 0, 'GetFileAttributesA', 0
               db 'GetTickCount64', 0, 'GetCurrentDirectoryA', 0, 'DeleteFileA', 0, 'FindFirstFileA', 0, 'FindNextFileA', 0
               db 'FindClose', 0, 'GetLocalTime', 0, 'GetSystemTime', 0, 'CreateFileA', 0, 'WriteFile', 0, 'ReadFile', 0
               db 'GetStdHandle', 0, 'GetFileSizeEx', 0, 0
lin_procs2:    dq lin_CreateProcessA, lin_WaitForSingleObject, lin_GetExitCodeProcess, lin_GetFileAttributesA
               dq lin_GetTickCount64, lin_GetCurrentDirectoryA, lin_DeleteFileA, lin_FindFirstFileA, lin_FindNextFileA
               dq lin_FindClose, GetLocalTime, GetLocalTime, CreateFileA, WriteFile, ReadFile, GetStdHandle, GetFileSizeEx
section .bss
lin_lastpid:   resq 1
lin_laststat:  resq 1
lin_dirbuf:    resb 65536
lin_dirfill:   resq 1
lin_dirpos:    resq 1
lin_dirfd:     resq 1
lin_suffix:    resb 256
lin_prefix:    resb 256
lin_dirpath:   resb 4096
lin_cargv:     resq 66
lin_cbuf:      resb 8192
section .text
lin_GetProcAddress2:            ; rdx = name -> rax = the emulation or 0 (the second table)
    push rbx
    push r12
    mov rbx, rdx
    lea r12, [lin_names2]
    xor r8d, r8d
.l:
    cmp byte [r12], 0
    je .none
    mov rcx, r12
    mov rdx, rbx
    push r8
    call lin_streq
    pop r8
    test eax, eax
    jnz .hit
.skip:
    inc r12
    cmp byte [r12-1], 0
    jne .skip
    inc r8
    jmp .l
.hit:
    lea rax, [lin_procs2]
    mov rax, [rax+r8*8]
    pop r12
    pop rbx
    ret
.none:
    xor eax, eax
    pop r12
    pop rbx
    ret

; CreateProcessA(app, cmdline, psa, tsa, inherit, flags, env, dir, si, pi) -> 1 / 0; pi.hProcess = the pid
lin_CreateProcessA:
    push rbx
    push rdi
    push rsi
    push r12
    push r13
    mov rsi, rdx                ; the command line
    mov r12, [rsp+48+64]        ; si: stack argument 9 (five pushes and the return address above the caller's frame)
    mov r13, [rsp+48+72]        ; pi: stack argument 10
    lea rdi, [lin_cbuf]
    xor ecx, ecx
.sp:
    cmp byte [rsi], ' '
    jne .tok
    inc rsi
    jmp .sp
.tok:
    cmp byte [rsi], 0
    je .split
    cmp ecx, 64
    jge .split
    lea rax, [lin_cargv]
    mov [rax+rcx*8], rdi
    inc ecx
.cp:
    mov al, [rsi]
    test al, al
    jz .tokend
    cmp al, ' '
    je .tokend
    mov [rdi], al
    inc rdi
    inc rsi
    jmp .cp
.tokend:
    mov byte [rdi], 0
    inc rdi
    jmp .sp
.split:
    lea rax, [lin_cargv]
    mov qword [rax+rcx*8], 0
    mov eax, 57                 ; fork
    syscall
    test rax, rax
    jnz .parent
    test dword [r12+60], 0x100  ; STARTF_USESTDHANDLES: stdout and stderr from si
    jz .exec
    mov rdi, [r12+88]
    mov esi, 1
    mov eax, 33                 ; dup2
    syscall
    mov rdi, [r12+96]
    mov esi, 2
    mov eax, 33
    syscall
.exec:
    lea rax, [lin_cargv]
    mov rdi, [rax]
    mov rsi, rax
    mov rdx, [lin_argv]
    mov rax, [lin_argc]
    lea rdx, [rdx+rax*8+8]
    mov eax, 59                 ; execve
    syscall
    mov edi, 127
    mov eax, 231
    syscall
.parent:
    js .fail
    mov [r13], rax              ; hProcess = pid
    mov qword [r13+8], 0
    mov eax, 1
    jmp .out
.fail:
    xor eax, eax
.out:
    pop r13
    pop r12
    pop rsi
    pop rdi
    pop rbx
    ret

lin_WaitForSingleObject:        ; (pid, ms) -> 0; the status kept for GetExitCodeProcess
    push rdi
    push rsi
    mov rdi, rcx
    lea rsi, [lin_laststat]
    xor edx, edx
    xor r10d, r10d
    mov eax, 61                 ; wait4
    syscall
    mov [lin_lastpid], rax
    xor eax, eax
    pop rsi
    pop rdi
    ret

lin_GetExitCodeProcess:         ; (pid, &code) -> 1; the exit status of the last waited process
    mov eax, [lin_laststat]
    shr eax, 8
    and eax, 0xFF
    mov [rdx], eax
    mov eax, 1
    ret

lin_GetFileAttributesA:         ; (path) -> 0x80 when it exists, else 0xFFFFFFFF
    push rdi
    push rsi
    mov rdi, rcx
    lea rsi, [lin_stat]
    mov eax, 4                  ; stat
    syscall
    test rax, rax
    jnz .no
    mov eax, 0x80
    jmp .out
.no:
    mov eax, 0xFFFFFFFF
.out:
    pop rsi
    pop rdi
    ret

lin_GetTickCount64:             ; milliseconds of the monotonic clock
    push rdi
    push rsi
    mov edi, 1                  ; CLOCK_MONOTONIC
    lea rsi, [lin_ts]
    mov eax, 228
    syscall
    mov rax, [lin_ts]
    imul rax, 1000
    mov r8, rax
    mov rax, [lin_ts+8]
    xor edx, edx
    mov rcx, 1000000
    div rcx
    add rax, r8
    pop rsi
    pop rdi
    ret

lin_GetCurrentDirectoryA:       ; (n, buf) -> length
    push rdi
    push rsi
    mov rdi, rdx
    mov rsi, rcx
    mov eax, 79                 ; getcwd
    syscall
    test rax, rax
    js .z
    dec rax
    jmp .out
.z:
    xor eax, eax
.out:
    pop rsi
    pop rdi
    ret

lin_DeleteFileA:                ; (path) -> 1 / 0
    push rdi
    mov rdi, rcx
    mov eax, 87                 ; unlink
    syscall
    test rax, rax
    jnz .no
    mov eax, 1
    pop rdi
    ret
.no:
    xor eax, eax
    pop rdi
    ret

; FindFirstFileA(pattern "dir/*.ext" or "*.ext", &data) -> 1 (a handle) or -1; cFileName at data+44
lin_FindFirstFileA:
    push rbx
    push rdi
    push rsi
    push r12
    mov rbx, rcx
    mov r12, rdx
    lea rdi, [lin_dirpath]
    mov rsi, rbx
    xor ecx, ecx
    mov r8, -1
.scan:
    mov al, [rsi+rcx]
    test al, al
    jz .scanned
    cmp al, '/'
    jne .n1
    mov r8, rcx
.n1:
    inc rcx
    jmp .scan
.scanned:
    cmp r8, -1
    jne .hasdir
    mov byte [rdi], '.'
    mov byte [rdi+1], 0
    mov rsi, rbx
    jmp .suffix
.hasdir:
    xor ecx, ecx
.cpd:
    cmp rcx, r8
    jge .cpdd
    mov al, [rsi+rcx]
    mov [rdi+rcx], al
    inc rcx
    jmp .cpd
.cpdd:
    mov byte [rdi+rcx], 0
    lea rsi, [rsi+r8+1]
.suffix:
    lea rdi, [lin_suffix]
    mov byte [rdi], 0
    lea r9, [lin_prefix]        ; the name part before the star
    xor ecx, ecx
.fs:
    mov al, [rsi]
    test al, al
    jz .pfxend
    inc rsi
    cmp al, '*'
    je .pfxend
    mov [r9+rcx], al
    inc rcx
    jmp .fs
.pfxend:
    mov byte [r9+rcx], 0
    test al, al
    jz .open
    xor ecx, ecx
.cps:
    mov al, [rsi+rcx]
    mov [rdi+rcx], al
    test al, al
    jz .open
    inc rcx
    jmp .cps
.open:
    lea rdi, [lin_dirpath]
    mov esi, 0x10000            ; O_RDONLY | O_DIRECTORY
    xor edx, edx
    mov eax, 2
    syscall
    test rax, rax
    js .fail
    mov [lin_dirfd], rax
    mov qword [lin_dirfill], 0
    mov qword [lin_dirpos], 0
    xor ecx, ecx
    mov rdx, r12
    call lin_FindNextFileA
    test eax, eax
    jz .fail
    mov eax, 1
    jmp .out
.fail:
    mov rax, -1
.out:
    pop r12
    pop rsi
    pop rdi
    pop rbx
    ret

lin_FindNextFileA:              ; (handle, &data) -> 1 with the next matching name at data+44, else 0
    push rbx
    push rdi
    push rsi
    push r12
    mov r12, rdx
.next:
    mov rax, [lin_dirpos]
    cmp rax, [lin_dirfill]
    jb .have
    mov rdi, [lin_dirfd]
    lea rsi, [lin_dirbuf]
    mov edx, 65536
    mov eax, 217                ; getdents64
    syscall
    test rax, rax
    jle .none
    mov [lin_dirfill], rax
    mov qword [lin_dirpos], 0
.have:
    lea rbx, [lin_dirbuf]
    add rbx, [lin_dirpos]       ; d_ino 8, d_off 8, d_reclen 2, d_type 1, d_name
    movzx eax, word [rbx+16]
    add [lin_dirpos], rax
    lea rsi, [rbx+19]
    mov rcx, rsi
    call zlen
    mov r8, rax
    lea rcx, [lin_suffix]
    call zlen
    cmp r8, rax
    jl .next
    mov rdi, rsi
    add rdi, r8
    sub rdi, rax
    lea rcx, [lin_suffix]
    mov rdx, rdi
    call lin_streq
    test eax, eax
    jz .next
    lea rcx, [lin_prefix]       ; and the prefix before the star
    call zlen
    mov r9, rax
    mov rcx, rsi
    call zlen
    cmp rax, r9
    jl .next
    lea rcx, [lin_prefix]
    mov rdx, rsi
    mov r8, r9
    call mem_eq
    test eax, eax
    jz .next
    cmp byte [rsi], '.'
    je .next
    lea rdi, [r12+44]
    xor ecx, ecx
.cp:
    mov al, [rsi+rcx]
    mov [rdi+rcx], al
    test al, al
    jz .found
    inc rcx
    cmp rcx, 259
    jb .cp
    mov byte [rdi+259], 0
.found:
    mov dword [r12], 0x80
    mov eax, 1
    jmp .out
.none:
    xor eax, eax
.out:
    pop r12
    pop rsi
    pop rdi
    pop rbx
    ret

lin_FindClose:
    push rdi
    mov rdi, [lin_dirfd]
    mov eax, 3
    syscall
    mov eax, 1
    pop rdi
    ret
%endif
emit_flush:                     ; safe from any stack alignment: WriteFile gets a 16-aligned frame
    push rbp
    mov rbp, rsp
    push rbx
    and rsp, -16
    sub rsp, 48
    mov rcx, [hstdout]
    lea rdx, [outbuf]
    mov r8d, [outlen]
    lea r9, [rsp+40]
    mov qword [rsp+32], 0
    test r8d, r8d
    jz .skip
    call WriteFile
.skip:
    mov qword [outlen], 0
    lea rsp, [rbp-8]
    pop rbx
    pop rbp
    ret

emit_char:                      ; cl = byte
    mov rax, [outlen]
    cmp rax, 65000
    jb .ok
    push rcx
    call emit_flush
    pop rcx
    mov rax, [outlen]
.ok:
    lea rdx, [outbuf]
    mov [rdx+rax], cl
    inc qword [outlen]
    ret

emit_str:                       ; rcx = ptr, rdx = len
    push rbx
    push rsi
    mov rsi, rcx
    mov rbx, rdx
.loop:
    test rbx, rbx
    jz .done
    movzx ecx, byte [rsi]
    call emit_char
    inc rsi
    dec rbx
    jmp .loop
.done:
    pop rsi
    pop rbx
    ret

emit_cstr:                      ; rcx = NUL-terminated
    push rbx
    mov rbx, rcx
.loop:
    movzx ecx, byte [rbx]
    test cl, cl
    jz .done
    call emit_char
    inc rbx
    jmp .loop
.done:
    pop rbx
    ret

emit_int:                       ; rcx = signed 64-bit
    push rbx
    push rsi
    sub rsp, 32
    mov rax, rcx
    test rax, rax
    jns .pos
    neg rax
    push rax
    mov cl, '-'
    call emit_char
    pop rax
.pos:
    lea rsi, [rsp+31]
    mov byte [rsi], 0
    xor ebx, ebx
.digits:
    xor edx, edx
    mov rcx, 10
    div rcx
    add dl, '0'
    dec rsi
    mov [rsi], dl
    inc ebx
    test rax, rax
    jnz .digits
.out:
    movzx ecx, byte [rsi]
    call emit_char
    inc rsi
    dec ebx
    jnz .out
    add rsp, 32
    pop rsi
    pop rbx
    ret

emit_nl:
    mov cl, 10
    jmp emit_char

; ============================================================ errors
; fail(rcx = msg, rdx = len): print "line N: msg", exit 1
fail:                           ; never returns, so the stack is simply re-aligned before the calls
    mov rbx, rcx
    mov r12, rdx
    and rsp, -16
    sub rsp, 32
    call emit_flush
    lea rcx, [msg_line]
    call emit_cstr
    mov rcx, [lineno]
    call emit_int
    mov cl, ':'
    call emit_char
    mov cl, ' '
    call emit_char
    mov rcx, rbx
    mov rdx, r12
    call emit_str
    call emit_flush
    mov rcx, rbx
    mov rdx, r12
    call trace_fail
    mov ecx, 1
    call ExitProcess

section .data
msg_line: db 'line ', 0
section .text

overflow:
    lea rcx, [msg_overflow]
    mov edx, msg_overflow_len
    jmp fail
shape_error:
    lea rcx, [msg_shape]
    mov edx, msg_shape_len
    jmp fail
syntax_error:
    lea rcx, [msg_syntax]
    mov edx, msg_syntax_len
    jmp fail
unknown_error:
    lea rcx, [msg_unknown]
    mov edx, msg_unknown_len
    jmp fail


; ============================================================ memory
alloc:                          ; rcx = bytes -> rax (zeroed by VirtualAlloc)
    mov rax, [arena]
    add rcx, 15
    and rcx, -16
    lea rdx, [rax+rcx]
    cmp rdx, [arena_end]
    ja .oom
    mov [arena], rdx
    ret
.oom:
    lea rcx, [msg_arena]
    mov edx, msg_arena_len
    jmp fail


; ============================================================ integers of any size
; A bignum: [0] sign (0 or 1), [8] n = limbs in use, [16..] limbs, little-endian, 64 bits each.
; Zero is n = 0 with sign 0. The top limb of a nonzero number is nonzero. A bignum is never changed after it
; is made: every operation allocates its result, so any bignum may be shared.

bn_alloc:                       ; rcx = limbs -> rax : all limbs zero, n = limbs, sign 0
    cmp rcx, [bnmax]            ; exact cost accounting: the largest integer allocated, in limbs
    jbe .bnmax_ok
    mov [bnmax], rcx
.bnmax_ok:
    push rbx
    mov rbx, rcx
    lea rcx, [rcx*8+16]
    call alloc
    mov qword [rax], 0
    mov [rax+8], rbx
    pop rbx
    ret

bn_trim:                        ; rcx = b -> rax = b, leading zero limbs dropped, zero given sign 0
    mov rax, rcx
    mov rdx, [rax+8]
.l:
    test rdx, rdx
    jz .zero
    cmp qword [rax+8+rdx*8], 0
    jne .done
    dec rdx
    jmp .l
.zero:
    mov qword [rax], 0
.done:
    mov [rax+8], rdx
    ret

bn_from_i64:                    ; rcx = v -> rax
    push rbx
    mov rbx, rcx
    mov ecx, 1
    call bn_alloc
    test rbx, rbx
    jns .pos
    neg rbx
    mov qword [rax], 1
.pos:
    mov [rax+16], rbx
    mov rcx, rax
    call bn_trim
    pop rbx
    ret

bn_neg:                         ; rcx = a -> rax = -a (a copy)
    push rbx
    push rsi
    mov rsi, rcx
    mov rbx, [rsi+8]
    mov rcx, rbx
    call bn_alloc
    xor ecx, ecx
.l:
    cmp rcx, rbx
    jge .copied
    mov rdx, [rsi+16+rcx*8]
    mov [rax+16+rcx*8], rdx
    inc rcx
    jmp .l
.copied:
    test rbx, rbx
    jz .out
    mov rdx, [rsi]
    xor edx, 1
    mov [rax], rdx
.out:
    pop rsi
    pop rbx
    ret

bn_is_one:                      ; rcx = a -> eax = 1 when a = +1
    xor eax, eax
    cmp qword [rcx+8], 1
    jne .no
    cmp qword [rcx+16], 1
    jne .no
    cmp qword [rcx], 0
    jne .no
    mov eax, 1
.no:
    ret

bn_cmp_mag:                     ; rcx = a, rdx = b -> rax = -1 / 0 / 1 comparing |a| with |b|
    push rbx
    mov r8, [rcx+8]
    mov r9, [rdx+8]
    mov rbx, r8
    cmp r9, rbx
    cmova rbx, r9
.l:
    test rbx, rbx
    jz .eq
    dec rbx
    xor eax, eax
    cmp rbx, r8
    jae .a0
    mov rax, [rcx+16+rbx*8]
.a0:
    xor r10d, r10d
    cmp rbx, r9
    jae .b0
    mov r10, [rdx+16+rbx*8]
.b0:
    cmp rax, r10
    ja .gt
    jb .lt
    jmp .l
.eq:
    xor eax, eax
    pop rbx
    ret
.gt:
    mov eax, 1
    pop rbx
    ret
.lt:
    mov rax, -1
    pop rbx
    ret

bn_add_mag:                     ; rcx = a, rdx = b -> rax = |a| + |b|, sign 0
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    mov rdi, rdx
    mov r12, [rsi+8]
    mov r13, [rdi+8]
    mov rcx, r12
    cmp r13, rcx
    cmova rcx, r13
    inc rcx
    mov rbx, rcx
    call bn_alloc
    mov r8, rax
    xor r9d, r9d                ; i
    xor r10d, r10d              ; carry
.l:
    cmp r9, rbx
    jge .done
    xor eax, eax
    cmp r9, r12
    jae .a0
    mov rax, [rsi+16+r9*8]
.a0:
    xor edx, edx
    cmp r9, r13
    jae .b0
    mov rdx, [rdi+16+r9*8]
.b0:
    add rax, r10
    setc r10b
    add rax, rdx
    adc r10b, 0
    movzx r10d, r10b
    mov [r8+16+r9*8], rax
    inc r9
    jmp .l
.done:
    mov rcx, r8
    call bn_trim
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

bn_sub_mag:                     ; rcx = a, rdx = b with |a| >= |b| -> rax = |a| - |b|, sign 0
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    mov rdi, rdx
    mov r12, [rsi+8]
    mov r13, [rdi+8]
    mov rcx, r12
    mov rbx, r12
    call bn_alloc
    mov r8, rax
    xor r9d, r9d
    xor r10d, r10d              ; borrow
.l:
    cmp r9, rbx
    jge .done
    mov rax, [rsi+16+r9*8]
    xor edx, edx
    cmp r9, r13
    jae .b0
    mov rdx, [rdi+16+r9*8]
.b0:
    sub rax, r10
    setc r10b
    sub rax, rdx
    adc r10b, 0
    movzx r10d, r10b
    mov [r8+16+r9*8], rax
    inc r9
    jmp .l
.done:
    mov rcx, r8
    call bn_trim
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

bn_add:                         ; rcx = a, rdx = b -> rax = a + b
    xor r8d, r8d
    jmp bn_addsub
bn_sub:                         ; rcx = a, rdx = b -> rax = a - b
    mov r8d, 1
bn_addsub:                      ; r8 = 0 add, 1 subtract
    push rbx
    push rsi
    push rdi
    push r12
    mov rsi, rcx
    mov rdi, rdx
    mov rbx, [rdi]
    xor rbx, r8                 ; the sign of b as used
    cmp qword [rdi+8], 0
    jne .bnz
    xor ebx, ebx
.bnz:
    mov r12, [rsi]
    cmp r12, rbx
    jne .diff
    mov rcx, rsi
    mov rdx, rdi
    call bn_add_mag
    mov [rax], r12
    jmp .fix
.diff:
    mov rcx, rsi
    mov rdx, rdi
    call bn_cmp_mag
    test rax, rax
    js .bbig
    mov rcx, rsi
    mov rdx, rdi
    call bn_sub_mag
    mov [rax], r12
    jmp .fix
.bbig:
    mov rcx, rdi
    mov rdx, rsi
    call bn_sub_mag
    mov [rax], rbx
.fix:
    mov rcx, rax
    call bn_trim
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

bn_mul:                         ; rcx = a, rdx = b -> rax = a b
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    mov rsi, rcx
    mov rdi, rdx
    mov r12, [rsi+8]
    mov r13, [rdi+8]
    lea rcx, [r12+r13]
    call bn_alloc
    mov r14, rax
    xor r15d, r15d              ; i
.i:
    cmp r15, r12
    jge .done
    xor ebx, ebx                ; j
    xor r8d, r8d                ; carry
.j:
    cmp rbx, r13
    jge .jend
    mov rax, [rsi+16+r15*8]
    mul qword [rdi+16+rbx*8]
    lea r9, [r15+rbx]
    add rax, [r14+16+r9*8]
    adc rdx, 0
    add rax, r8
    adc rdx, 0
    mov [r14+16+r9*8], rax
    mov r8, rdx
    inc rbx
    jmp .j
.jend:
    lea r9, [r15+r13]
    mov [r14+16+r9*8], r8
    inc r15
    jmp .i
.done:
    mov rax, [rsi]
    xor rax, [rdi]
    mov [r14], rax
    mov rcx, r14
    call bn_trim
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; bn_divmod(rcx = a, rdx = b) -> rax = quotient, rdx = remainder; truncating (the remainder has a's sign).
; Shift-and-subtract over the bits of a; b = 0 stops the program.
bn_divmod:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    mov rsi, rcx
    mov rdi, rdx
    cmp qword [rdi+8], 0
    je .divzero
    mov r12, [rsi+8]            ; na
    mov r13, [rdi+8]            ; nb
    mov rcx, r12
    call bn_alloc
    mov r14, rax                ; q, na limbs
    lea rcx, [r13+1]
    call bn_alloc
    mov rbx, rax                ; r, nb+1 limbs, kept at that length during the loop
    test r12, r12
    jz .done
    mov rax, [rsi+8+r12*8]      ; top limb of a
    bsr rax, rax
    mov r15, r12
    shl r15, 6
    sub r15, 64
    add r15, rax                ; index of the top set bit of a
.bit:
    test r15, r15
    js .done
    mov rcx, [rbx+8]
    xor edx, edx
    xor r8d, r8d
.shl:                           ; r <<= 1
    cmp r8, rcx
    jge .shld
    mov rax, [rbx+16+r8*8]
    mov r9, rax
    shr r9, 63
    shl rax, 1
    or rax, rdx
    mov [rbx+16+r8*8], rax
    mov rdx, r9
    inc r8
    jmp .shl
.shld:
    mov rax, r15
    mov rcx, r15
    shr rax, 6
    and ecx, 63
    mov rdx, [rsi+16+rax*8]
    shr rdx, cl
    and edx, 1
    or [rbx+16], rdx            ; bring in the next bit of a
    mov rcx, rbx
    mov rdx, rdi
    call bn_cmp_mag
    test rax, rax
    js .next
    mov rcx, [rbx+8]
    xor r8d, r8d
    xor r10d, r10d
.sub:                           ; r -= b
    cmp r8, rcx
    jge .subd
    mov rax, [rbx+16+r8*8]
    xor edx, edx
    cmp r8, r13
    jae .z
    mov rdx, [rdi+16+r8*8]
.z:
    sub rax, r10
    setc r10b
    sub rax, rdx
    adc r10b, 0
    movzx r10d, r10b
    mov [rbx+16+r8*8], rax
    inc r8
    jmp .sub
.subd:
    mov rax, r15
    mov rcx, r15
    shr rax, 6
    and ecx, 63
    mov rdx, 1
    shl rdx, cl
    or [r14+16+rax*8], rdx      ; the quotient bit
.next:
    dec r15
    jmp .bit
.done:
    mov rax, [rsi]
    xor rax, [rdi]
    mov [r14], rax
    mov rax, [rsi]
    mov [rbx], rax
    mov rcx, r14
    call bn_trim
    mov rcx, rbx
    call bn_trim
    mov rdx, rax
    mov rax, r14
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.divzero:
    lea rcx, [msg_divzero]
    mov edx, msg_divzero_len
    jmp fail

bn_divmod_small:                ; rcx = a, rdx = d (64-bit, nonzero) -> rax = |a| / d (sign 0), rdx = |a| mod d
    push rbx
    push rsi
    push r12
    mov rsi, rcx
    mov rbx, rdx
    mov r12, [rsi+8]
    mov rcx, r12
    call bn_alloc
    mov r8, rax
    xor edx, edx
    mov rcx, r12
.l:
    test rcx, rcx
    jz .done
    dec rcx
    mov rax, [rsi+16+rcx*8]
    div rbx
    mov [r8+16+rcx*8], rax
    jmp .l
.done:
    push rdx
    mov rcx, r8
    call bn_trim
    pop rdx
    pop r12
    pop rsi
    pop rbx
    ret

bn_gcd:                         ; rcx = a, rdx = b -> rax = gcd(|a|, |b|), sign 0
    push rsi
    push rdi
    mov rsi, rcx
    mov rdi, rdx
.l:
    cmp qword [rdi+8], 0
    je .done
    mov rcx, rsi
    mov rdx, rdi
    call bn_divmod
    mov rsi, rdi
    mov rdi, rdx
    jmp .l
.done:
    mov rax, rsi
    cmp qword [rsi], 0
    je .out
    mov rcx, rsi
    call bn_neg
.out:
    pop rdi
    pop rsi
    ret

bn_from_dec:                    ; rcx = digits, rdx = count -> rax (no sign); a non-digit is a syntax error
    push rbx
    push rsi
    push rdi
    push r12
    mov rsi, rcx
    mov rdi, rdx
    test rdi, rdi
    jz syntax_error
    mov rax, rdx
    xor edx, edx
    mov ecx, 19
    div rcx
    lea rcx, [rax+2]
    mov r12, rcx                ; limbs of capacity (10^19 < 2^64)
    call bn_alloc
    mov rbx, rax
    xor r8d, r8d
.d:
    cmp r8, rdi
    jge .done
    movzx ecx, byte [rsi+r8]
    sub ecx, '0'
    cmp ecx, 9
    ja syntax_error
    mov r9, rcx                 ; carry = the digit
    xor r10d, r10d
.k:                             ; number = number * 10 + digit
    cmp r10, r12
    jge .kd
    mov rax, [rbx+16+r10*8]
    mov ecx, 10
    mul rcx
    add rax, r9
    adc rdx, 0
    mov [rbx+16+r10*8], rax
    mov r9, rdx
    inc r10
    jmp .k
.kd:
    inc r8
    jmp .d
.done:
    mov rcx, rbx
    call bn_trim
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

emit_pad18:                     ; rcx = value below 10^18, printed with leading zeros to 18 digits
    push rbx
    push rsi
    sub rsp, 32
    mov rax, rcx
    lea rsi, [rsp+18]
    mov ebx, 18
.d:
    xor edx, edx
    mov ecx, 10
    div rcx
    add dl, '0'
    dec rsi
    mov [rsi], dl
    dec ebx
    jnz .d
    mov rcx, rsi
    mov edx, 18
    call emit_str
    add rsp, 32
    pop rsi
    pop rbx
    ret

bn_emit:                        ; rcx = b : print it in decimal
    push rbx
    push rsi
    push r12
    push r13
    mov rsi, rcx
    cmp qword [rsi], 0
    je .nosign
    mov cl, '-'
    call emit_char
.nosign:
    cmp qword [rsi+8], 0
    jne .nz
    mov cl, '0'
    call emit_char
    jmp .out
.nz:
    mov rax, [rsi+8]
    shl rax, 6                  ; bits
    xor edx, edx
    mov ecx, 59                 ; 10^18 > 2^59, so bits/59 + 2 chunks of 18 digits suffice
    div rcx
    lea rcx, [rax+2]
    shl rcx, 3
    call alloc
    mov rbx, rax
    xor r12d, r12d
    mov r13, rsi
.chunk:
    cmp qword [r13+8], 0
    je .print
    mov rcx, r13
    mov rdx, 1000000000000000000
    call bn_divmod_small
    mov [rbx+r12*8], rdx
    inc r12
    mov r13, rax
    jmp .chunk
.print:
    dec r12
    mov rcx, [rbx+r12*8]
    call emit_int
.rest:
    test r12, r12
    jz .out
    dec r12
    mov rcx, [rbx+r12*8]
    call emit_pad18
    jmp .rest
.out:
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; ============================================================ the rationals
; A rational: [0] numerator, [8] denominator; the denominator is positive and coprime with the numerator,
; zero is 0/1. Like bignums they are never changed once made.

q_pair:                         ; rcx = num, rdx = den -> rax, no normalisation
    push rcx
    push rdx
    mov ecx, 16
    call alloc
    pop rdx
    pop rcx
    mov [rax], rcx
    mov [rax+8], rdx
    ret

q_make:                         ; rcx = num, rdx = den -> rax normalised; a zero denominator stops the program
    push rbx
    push rsi
    push rdi
    mov rsi, rcx
    mov rdi, rdx
    cmp qword [rdi+8], 0
    je .divzero
    cmp qword [rdi], 0
    je .pos
    mov rcx, rsi
    call bn_neg
    mov rsi, rax
    mov rcx, rdi
    call bn_neg
    mov rdi, rax
.pos:
    cmp qword [rsi+8], 0
    jne .nz
    mov rsi, [bn_zero]
    mov rdi, [bn_one]
    jmp .pair
.nz:
    mov rcx, rsi
    mov rdx, rdi
    call bn_gcd
    mov rbx, rax
    mov rcx, rbx
    call bn_is_one
    test eax, eax
    jnz .pair
    mov rcx, rsi
    mov rdx, rbx
    call bn_divmod
    mov rsi, rax
    mov rcx, rdi
    mov rdx, rbx
    call bn_divmod
    mov rdi, rax
.pair:
    mov rcx, rsi
    mov rdx, rdi
    call q_pair
    pop rdi
    pop rsi
    pop rbx
    ret
.divzero:
    lea rcx, [msg_divzero]
    mov edx, msg_divzero_len
    jmp fail

q_add:                          ; rcx = a, rdx = b -> rax = a + b
    xor r8d, r8d
    jmp q_addsub
q_sub:                          ; rcx = a, rdx = b -> rax = a - b
    mov r8d, 1
q_addsub:
    inc qword [qops]            ; exact cost accounting: rational operations
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    mov rdi, rdx
    mov r13, r8
    mov rcx, [rsi]
    mov rdx, [rdi+8]
    call bn_mul                 ; a.n b.d
    mov rbx, rax
    mov rcx, [rdi]
    mov rdx, [rsi+8]
    call bn_mul                 ; b.n a.d
    mov rcx, rbx
    mov rdx, rax
    mov r8, r13
    call bn_addsub
    mov rbx, rax
    mov rcx, [rsi+8]
    mov rdx, [rdi+8]
    call bn_mul                 ; a.d b.d
    mov rcx, rbx
    mov rdx, rax
    call q_make
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

q_mul:                          ; rcx = a, rdx = b -> rax = a b
    inc qword [qops]            ; exact cost accounting: rational operations
    push rbx
    push rsi
    push rdi
    mov rsi, rcx
    mov rdi, rdx
    mov rcx, [rsi]
    mov rdx, [rdi]
    call bn_mul
    mov rbx, rax
    mov rcx, [rsi+8]
    mov rdx, [rdi+8]
    call bn_mul
    mov rcx, rbx
    mov rdx, rax
    call q_make
    pop rdi
    pop rsi
    pop rbx
    ret

q_div:                          ; rcx = a, rdx = b -> rax = a / b; b = 0 stops the program
    inc qword [qops]            ; exact cost accounting: rational operations
    push rbx
    push rsi
    push rdi
    mov rsi, rcx
    mov rdi, rdx
    mov rcx, [rsi]
    mov rdx, [rdi+8]
    call bn_mul
    mov rbx, rax
    mov rcx, [rsi+8]
    mov rdx, [rdi]
    call bn_mul
    mov rcx, rbx
    mov rdx, rax
    call q_make
    pop rdi
    pop rsi
    pop rbx
    ret

q_neg:                          ; rcx = a -> rax = -a
    push rbx
    mov rbx, rcx
    mov rcx, [rbx]
    call bn_neg
    mov rcx, rax
    mov rdx, [rbx+8]
    call q_pair
    pop rbx
    ret

q_is_zero:                      ; rcx = a -> eax 1/0
    mov rax, [rcx]
    xor ecx, ecx
    cmp qword [rax+8], 0
    sete cl
    mov eax, ecx
    ret

q_from_i64:                     ; rcx = v -> rax
    call bn_from_i64
    mov rcx, rax
    mov rdx, [bn_one]
    jmp q_make

q_to_i64:                       ; rcx = a -> rax : the value as a machine word, or the Menschenwerk error
    mov rax, [rcx]
    mov rdx, [rcx+8]
    push rcx
    mov rcx, rdx
    call bn_is_one
    pop rcx
    test eax, eax
    jz .no
    mov rax, [rcx]
    cmp qword [rax+8], 0
    je .zero
    cmp qword [rax+8], 1
    jne .no
    mov rdx, [rax+16]
    cmp qword [rax], 0
    jne .neg
    mov rcx, 0x7fffffffffffffff
    cmp rdx, rcx
    ja .no
    mov rax, rdx
    ret
.neg:
    mov rcx, 0x8000000000000000
    cmp rdx, rcx
    ja .no
    mov rax, rdx
    neg rax
    ret
.zero:
    xor eax, eax
    ret
.no:
    lea rcx, [msg_word]
    mov edx, msg_word_len
    jmp fail

q_emit:                         ; rcx = a : print "n" or "n/d"
    push rbx
    mov rbx, rcx
    mov rcx, [rbx]
    call bn_emit
    mov rcx, [rbx+8]
    call bn_is_one
    test eax, eax
    jnz .out
    mov cl, '/'
    call emit_char
    mov rcx, [rbx+8]
    call bn_emit
.out:
    pop rbx
    ret

; q_parse(rcx = bytes, rdx = length) -> rax : "-3", "12", "1/2", "-22/7"
; parse_decimal_mag(rcx = ptr, rdx = len) -> rax = numerator, rdx = denominator (both bignums, magnitude only):
; "12" -> 12/1, "0.5" -> 5/10, "250.00" -> 25000/100, all by integer arithmetic. A second '.' or a non-digit
; is a syntax error. There is no floating-point number anywhere in this; a decimal is a ratio of integers.
parse_decimal_mag:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    sub rsp, 16
    mov rsi, rcx
    lea rdi, [rcx+rdx]
    cmp rsi, rdi
    je .bad
    mov r12, [bn_zero]          ; numerator
    mov r13, [bn_one]           ; denominator
    xor r14d, r14d              ; has a dot been seen?
.loop:
    cmp rsi, rdi
    jge .done
    movzx eax, byte [rsi]
    cmp al, '.'
    je .dot
    sub al, '0'
    cmp al, 9
    ja .bad
    movzx eax, al
    mov rcx, rax
    call bn_from_i64
    mov [rsp], rax             ; the digit, as a bignum
    mov rcx, r12
    mov rdx, [bn_ten]
    call bn_mul
    mov rcx, rax
    mov rdx, [rsp]
    call bn_add
    mov r12, rax               ; num = num*10 + digit
    test r14d, r14d
    jz .nofrac
    mov rcx, r13
    mov rdx, [bn_ten]
    call bn_mul
    mov r13, rax               ; den *= 10 for a fractional digit
.nofrac:
    inc rsi
    jmp .loop
.dot:
    test r14d, r14d
    jnz .bad
    mov r14d, 1
    inc rsi
    jmp .loop
.done:
    mov rax, r12
    mov rdx, r13
    add rsp, 16
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.bad:
    add rsp, 16
    jmp syntax_error

; q_parse(rcx = ptr, rdx = len) -> rax : an exact rational. A literal is a decimal, or a fraction of two
; decimals: "-3", "12", "1/2", "-22/7", "0.5", "250.00", "-3.14", even "1.5/0.5". Every part is read with
; integer arithmetic; a decimal point denotes a power of ten in the denominator, never a floating-point number.
q_parse:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    mov rsi, rcx
    mov rdi, rdx
    test rdi, rdi
    jz syntax_error
    xor r12d, r12d             ; sign
    cmp byte [rsi], '-'
    jne .findslash
    mov r12d, 1
    inc rsi
    dec rdi
    test rdi, rdi
    jz syntax_error
.findslash:
    mov rbx, -1
    xor ecx, ecx
.sl:
    cmp rcx, rdi
    jge .haveslash
    cmp byte [rsi+rcx], '/'
    jne .sln
    mov rbx, rcx
    jmp .haveslash
.sln:
    inc rcx
    jmp .sl
.haveslash:
    cmp rbx, -1
    jne .fraction
    mov rcx, rsi
    mov rdx, rdi
    call parse_decimal_mag     ; rax = num, rdx = den
    jmp .sign
.fraction:
    mov rcx, rsi
    mov rdx, rbx
    call parse_decimal_mag     ; left = num/den
    mov r13, rax
    mov r14, rdx
    lea rcx, [rsi+rbx+1]
    mov rdx, rdi
    sub rdx, rbx
    dec rdx
    test rdx, rdx
    jz syntax_error
    call parse_decimal_mag     ; right = num (rax) / den (rdx)
    mov rbx, rax               ; right numerator
    mov rcx, r13               ; left numerator
    call bn_mul                ; num = leftnum * rightden
    mov r13, rax
    mov rcx, r14               ; left denominator
    mov rdx, rbx               ; right numerator
    call bn_mul                ; den = leftden * rightnum
    mov rdx, rax
    mov rax, r13
.sign:
    test r12d, r12d
    jz .make
    push rdx
    mov rcx, rax
    call bn_neg
    pop rdx
.make:
    mov rcx, rax
    call q_make
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; init_constants: the shared 0 and 1, made once
init_constants:
    push rbx
    xor ecx, ecx
    call bn_alloc
    mov [bn_zero], rax
    mov ecx, 1
    call bn_from_i64
    mov [bn_one], rax
    mov ecx, 10
    call bn_from_i64
    mov [bn_ten], rax
    mov rcx, [bn_zero]
    mov rdx, [bn_one]
    call q_pair
    mov [q_zero], rax
    mov rcx, [bn_one]
    mov rdx, [bn_one]
    call q_pair
    mov [q_one], rax
    pop rbx
    ret

; ---- seventeenth cut: per-entry compaction of the temporaries of a matrix product ----
; bn_copy(rcx = b) -> rax = a fresh copy of the integer
bn_copy:
    push rbx
    push rsi
    push r12
    mov rsi, rcx
    mov rcx, [rsi+8]
    call bn_alloc
    mov rbx, rax
    mov rcx, [rsi]
    mov [rbx], rcx
    mov r12, [rsi+8]
    xor ecx, ecx
.l:
    cmp rcx, r12
    jge .done
    mov rax, [rsi+16+rcx*8]
    mov [rbx+16+rcx*8], rax
    inc rcx
    jmp .l
.done:
    mov rax, rbx
    pop r12
    pop rsi
    pop rbx
    ret

; q_compact(rcx = q, rdx = mark) -> rax : the rational q, moved down to the arena position `mark` (a fresh copy of
; its two integers and its pair, contiguous), with everything allocated since the mark released and zeroed. A q
; that lies below the mark is left where it is and the temporaries above the mark are released. The result of a
; dot product is thus the only thing a product keeps of the temporaries it made.
q_compact:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    mov rbx, rcx
    mov r12, rdx
    cmp rbx, r12
    jb .old
    mov r13, [arena]            ; the copy starts here
    mov rcx, [rbx]
    call bn_copy
    mov r14, rax
    mov rcx, [rbx+8]
    call bn_copy
    mov rcx, r14
    mov rdx, rax
    call q_pair
    mov rbx, rax                ; the copy's pair, at the top
    mov rcx, [arena]
    sub rcx, r13                ; bytes to move
    mov r14, rcx
    mov rsi, r13
    mov rdi, r12
    shr rcx, 3
    rep movsq                   ; down to the mark (forward copy: the destination is below the source)
    mov rax, r13
    sub rax, r12                ; delta
    sub rbx, rax
    sub [rbx], rax
    sub [rbx+8], rax
    lea rdi, [r12+r14]          ; the new top
    mov rcx, [arena]
    sub rcx, rdi
    shr rcx, 3
    xor eax, eax
    rep stosq                   ; the vacated memory is zero again (allocations assume fresh memory is zero)
    lea rax, [r12+r14]
    mov [arena], rax
    mov rax, rbx
    jmp .out
.old:
    mov rdi, r12
    mov rcx, [arena]
    sub rcx, rdi
    shr rcx, 3
    xor eax, eax
    rep stosq
    mov [arena], r12
    mov rax, rbx
.out:
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; ============================================================ matrices over Q
; matrix: [0] rows, [8] cols, [16..] cells row-major, each cell a pointer to a rational

cell:                           ; rcx = M, rdx = i, r8 = j -> rax = address of the cell
    mov rax, rdx
    imul rax, [rcx+8]
    add rax, r8
    lea rax, [rcx+16+rax*8]
    ret

mat_new:                        ; rcx = rows, rdx = cols -> rax, every cell 0
    push rbx
    push r12
    push r13
    mov r12, rcx
    mov r13, rdx
    mov rax, rcx
    imul rax, rdx
    jo overflow
    mov rbx, rax
    lea rcx, [rax*8+16]
    call alloc
    mov [rax], r12
    mov [rax+8], r13
    mov rdx, [q_zero]
    xor ecx, ecx
.f:
    cmp rcx, rbx
    jge .d
    mov [rax+16+rcx*8], rdx
    inc rcx
    jmp .f
.d:
    pop r13
    pop r12
    pop rbx
    ret

; mat_mul(rcx = A, rdx = B) -> rax = A B
mat_mul:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 16
    mov rsi, rcx
    mov rdi, rdx
    mov rax, [rsi+8]
    cmp rax, [rdi]
    jne shape_error
    mov rcx, [rsi]
    mov rdx, [rdi+8]
    call mat_new
    mov r12, rax
    xor r13d, r13d              ; i
.i:
    cmp r13, [rsi]
    jge .done
    xor r14d, r14d              ; j
.j:
    cmp r14, [rdi+8]
    jge .in
    mov rbx, [q_zero]           ; the sum
    mov rax, [arena]
    mov [rsp+8], rax            ; the mark: the temporaries of this entry go above it
    xor r15d, r15d              ; k
.k:
    cmp r15, [rsi+8]
    jge .st
    mov rcx, rsi
    mov rdx, r13
    mov r8, r15
    call cell
    mov rax, [rax]
    mov [rsp], rax              ; A[i][k]
    mov rcx, rdi
    mov rdx, r15
    mov r8, r14
    call cell
    mov rdx, [rax]              ; B[k][j]
    mov rcx, [rsp]
    call q_mul
    mov rcx, rbx
    mov rdx, rax
    call q_add
    mov rbx, rax
    inc r15
    jmp .k
.st:
    mov rcx, rbx
    mov rdx, [rsp+8]
    call q_compact
    mov rbx, rax
    mov rcx, r12
    mov rdx, r13
    mov r8, r14
    call cell
    mov [rax], rbx
    inc r14
    jmp .j
.in:
    inc r13
    jmp .i
.done:
    mov rax, r12
    add rsp, 16
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_addsub(rcx = A, rdx = B, r8 = 1 add / -1 subtract) -> rax
mat_addsub:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    mov rsi, rcx
    mov rdi, rdx
    mov r13, r8
    mov rax, [rsi]
    cmp rax, [rdi]
    jne shape_error
    mov rax, [rsi+8]
    cmp rax, [rdi+8]
    jne shape_error
    mov rcx, [rsi]
    mov rdx, [rsi+8]
    call mat_new
    mov r12, rax
    mov rbx, [rsi]
    imul rbx, [rsi+8]
    xor r14d, r14d
.l:
    cmp r14, rbx
    jge .done
    mov rcx, [rsi+16+r14*8]
    mov rdx, [rdi+16+r14*8]
    test r13, r13
    js .sub
    call q_add
    jmp .put
.sub:
    call q_sub
.put:
    mov [r12+16+r14*8], rax
    inc r14
    jmp .l
.done:
    mov rax, r12
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_scale(rcx = k (a rational), rdx = A) -> rax = k A
mat_scale:
    push rbx
    push rsi
    push r12
    push r13
    push r14
    mov r13, rcx
    mov rsi, rdx
    mov rcx, [rsi]
    mov rdx, [rsi+8]
    call mat_new
    mov r12, rax
    mov rbx, [rsi]
    imul rbx, [rsi+8]
    xor r14d, r14d
.l:
    cmp r14, rbx
    jge .done
    mov rcx, r13
    mov rdx, [rsi+16+r14*8]
    call q_mul
    mov [r12+16+r14*8], rax
    inc r14
    jmp .l
.done:
    mov rax, r12
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_transpose(rcx = A) -> rax = A^T
mat_transpose:
    push rbx
    push rsi
    push r12
    push r13
    push r14
    mov rsi, rcx
    mov rcx, [rsi+8]
    mov rdx, [rsi]
    call mat_new
    mov r12, rax
    xor r13d, r13d
.rows:
    cmp r13, [rsi]
    jge .done
    xor r14d, r14d
.cols:
    cmp r14, [rsi+8]
    jge .next
    mov rax, r13
    imul rax, [rsi+8]
    add rax, r14
    mov rbx, [rsi+16+rax*8]
    mov rax, r14
    imul rax, [r12+8]
    add rax, r13
    mov [r12+16+rax*8], rbx
    inc r14
    jmp .cols
.next:
    inc r13
    jmp .rows
.done:
    mov rax, r12
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_kron(rcx = A, rdx = B) -> rax = A (x) B
mat_kron:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 32
    mov rsi, rcx
    mov rdi, rdx
    mov rcx, [rsi]
    imul rcx, [rdi]
    jo overflow
    mov rdx, [rsi+8]
    imul rdx, [rdi+8]
    jo overflow
    call mat_new
    mov r12, rax
    xor r13d, r13d              ; i over A rows
.ai:
    cmp r13, [rsi]
    jge .done
    xor r14d, r14d              ; j over A cols
.aj:
    cmp r14, [rsi+8]
    jge .ai_next
    mov rax, r13
    imul rax, [rsi+8]
    add rax, r14
    mov rbx, [rsi+16+rax*8]     ; a = A[i][j]
    xor r15d, r15d              ; k over B rows
.bk:
    cmp r15, [rdi]
    jge .aj_next
    mov qword [rsp], 0          ; l over B cols
.bl:
    mov rax, [rsp]
    cmp rax, [rdi+8]
    jge .bk_next
    mov rax, r15
    imul rax, [rdi+8]
    add rax, [rsp]
    mov rdx, [rdi+16+rax*8]     ; b = B[k][l]
    mov rcx, rbx
    call q_mul
    ; row = i*Brows + k, col = j*Bcols + l
    mov rcx, r13
    imul rcx, [rdi]
    add rcx, r15
    imul rcx, [r12+8]
    mov rdx, r14
    imul rdx, [rdi+8]
    add rdx, [rsp]
    add rcx, rdx
    mov [r12+16+rcx*8], rax
    inc qword [rsp]
    jmp .bl
.bk_next:
    inc r15
    jmp .bk
.aj_next:
    inc r14
    jmp .aj
.ai_next:
    inc r13
    jmp .ai
.done:
    mov rax, r12
    add rsp, 32
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_identity(rcx = n) -> rax
mat_identity:
    push rbx
    push r12
    mov rbx, rcx
    mov rdx, rcx
    call mat_new
    mov r12, rax
    mov rdx, [q_one]
    xor ecx, ecx
.loop:
    cmp rcx, rbx
    jge .done
    mov rax, rcx
    imul rax, rbx
    add rax, rcx
    mov [r12+16+rax*8], rdx
    inc rcx
    jmp .loop
.done:
    mov rax, r12
    pop r12
    pop rbx
    ret

; mat_power(rcx = A, rdx = k) -> rax = A^k by squaring
mat_power:
    push rbx
    push rsi
    push r12
    push r13
    mov rsi, rcx
    mov r13, rdx
    mov rax, [rsi]
    cmp rax, [rsi+8]
    je .sq
    lea rcx, [msg_square]
    mov edx, msg_square_len
    jmp fail
.sq:
    mov rcx, [rsi]
    call mat_identity
    mov r12, rax                ; result
.loop:
    test r13, r13
    jle .done
    test r13, 1
    jz .even
    mov rcx, r12
    mov rdx, rsi
    call mat_mul
    mov r12, rax
.even:
    shr r13, 1
    jz .done
    mov rcx, rsi
    mov rdx, rsi
    call mat_mul
    mov rsi, rax
    jmp .loop
.done:
    mov rax, r12
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_copy(rcx = A) -> rax : a new matrix with the same cells
mat_copy:
    push rsi
    push r12
    push rbx
    mov rsi, rcx
    mov rcx, [rsi]
    mov rdx, [rsi+8]
    call mat_new
    mov r12, rax
    mov rbx, [rsi]
    imul rbx, [rsi+8]
    xor ecx, ecx
.loop:
    cmp rcx, rbx
    jge .done
    mov rax, [rsi+16+rcx*8]
    mov [r12+16+rcx*8], rax
    inc rcx
    jmp .loop
.done:
    mov rax, r12
    pop rbx
    pop r12
    pop rsi
    ret

; mat_is_zero(rcx = A) -> eax 1/0
mat_is_zero:
    push rbx
    push rsi
    mov rsi, rcx
    mov rbx, [rsi]
    imul rbx, [rsi+8]
.loop:
    test rbx, rbx
    jz .yes
    dec rbx
    mov rcx, [rsi+16+rbx*8]
    call q_is_zero
    test eax, eax
    jnz .loop
    xor eax, eax
    pop rsi
    pop rbx
    ret
.yes:
    mov eax, 1
    pop rsi
    pop rbx
    ret

; mat_augment(rcx = A, rdx = B) -> rax = [A | B]
mat_augment:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    mov rsi, rcx
    mov rdi, rdx
    mov rax, [rsi]
    cmp rax, [rdi]
    jne shape_error
    mov rcx, [rsi]
    mov rdx, [rsi+8]
    add rdx, [rdi+8]
    call mat_new
    mov r12, rax
    xor r13d, r13d              ; row
.r:
    cmp r13, [rsi]
    jge .done
    xor r14d, r14d              ; col of A
.a:
    cmp r14, [rsi+8]
    jge .b0
    mov rcx, rsi
    mov rdx, r13
    mov r8, r14
    call cell
    mov rbx, [rax]
    mov rcx, r12
    mov rdx, r13
    mov r8, r14
    call cell
    mov [rax], rbx
    inc r14
    jmp .a
.b0:
    xor r14d, r14d              ; col of B
.b:
    cmp r14, [rdi+8]
    jge .next
    mov rcx, rdi
    mov rdx, r13
    mov r8, r14
    call cell
    mov rbx, [rax]
    mov rcx, r12
    mov rdx, r13
    mov r8, r14
    add r8, [rsi+8]
    call cell
    mov [rax], rbx
    inc r14
    jmp .b
.next:
    inc r13
    jmp .r
.done:
    mov rax, r12
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_rref(rcx = M) -> rax = rank; M is reduced in place (Gauss-Jordan over Q, deciding zero exactly at every
; pivot); pivots[0..rank-1] receive the pivot columns
mat_rref:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 32
    mov rsi, rcx
    mov r12, [rsi]              ; rows
    mov r13, [rsi+8]            ; cols
    xor r14d, r14d              ; r = next pivot row
    xor r15d, r15d              ; c = current column
.col:
    cmp r15, r13
    jge .done
    cmp r14, r12
    jge .done
    mov rbx, r14
.find:                          ; a row p >= r with M[p][c] != 0
    cmp rbx, r12
    jge .nextcol
    mov rcx, rsi
    mov rdx, rbx
    mov r8, r15
    call cell
    mov rcx, [rax]
    call q_is_zero
    test eax, eax
    jz .found
    inc rbx
    jmp .find
.nextcol:
    inc r15
    jmp .col
.found:
    cmp rbx, r14
    je .noswap
    xor edi, edi
.swap:                          ; rows p and r
    cmp rdi, r13
    jge .noswap
    mov rcx, rsi
    mov rdx, rbx
    mov r8, rdi
    call cell
    mov [rsp], rax
    mov rcx, rsi
    mov rdx, r14
    mov r8, rdi
    call cell
    mov rcx, [rsp]
    mov rdx, [rcx]
    mov r8, [rax]
    mov [rcx], r8
    mov [rax], rdx
    inc rdi
    jmp .swap
.noswap:
    mov rcx, rsi
    mov rdx, r14
    mov r8, r15
    call cell
    mov rax, [rax]
    mov [rsp+8], rax            ; the pivot
    mov rdi, r15
.norm:                          ; row r /= pivot
    cmp rdi, r13
    jge .normd
    mov rcx, rsi
    mov rdx, r14
    mov r8, rdi
    call cell
    mov [rsp+16], rax
    mov rcx, [rax]
    mov rdx, [rsp+8]
    call q_div
    mov rcx, [rsp+16]
    mov [rcx], rax
    inc rdi
    jmp .norm
.normd:
    xor ebx, ebx                ; i
.elim:                          ; every other row: row i -= M[i][c] * row r
    cmp rbx, r12
    jge .elimd
    cmp rbx, r14
    je .elimnext
    mov rcx, rsi
    mov rdx, rbx
    mov r8, r15
    call cell
    mov rax, [rax]
    mov [rsp+8], rax            ; f = M[i][c]
    mov rcx, rax
    call q_is_zero
    test eax, eax
    jnz .elimnext
    mov rdi, r15
.ej:
    cmp rdi, r13
    jge .elimnext
    mov rcx, rsi
    mov rdx, r14
    mov r8, rdi
    call cell
    mov rcx, [rax]
    mov rdx, [rsp+8]
    call q_mul                  ; f M[r][j]
    mov [rsp+24], rax
    mov rcx, rsi
    mov rdx, rbx
    mov r8, rdi
    call cell
    mov [rsp+16], rax
    mov rcx, [rax]
    mov rdx, [rsp+24]
    call q_sub
    mov rcx, [rsp+16]
    mov [rcx], rax
    inc rdi
    jmp .ej
.elimnext:
    inc rbx
    jmp .elim
.elimd:
    lea rax, [pivots]
    mov [rax+r14*8], r15
    inc r14
    inc r15
    jmp .col
.done:
    mov rax, r14
    add rsp, 32
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_rank(rcx = A) -> rax, on a copy
mat_rank:
    call mat_copy
    mov rcx, rax
    jmp mat_rref

; mat_rref_copy(rcx = A) -> rax = the reduced form of a copy, rdx = its rank
mat_rref_copy:
    push rbx
    call mat_copy
    mov rbx, rax
    mov rcx, rax
    call mat_rref
    mov rdx, rax
    mov rax, rbx
    pop rbx
    ret

; mat_kernel(rcx = A) -> rax : a basis of the kernel, one column per free variable (n x nullity)
mat_kernel:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 16
    mov rsi, rcx
    call mat_rref_copy
    mov rdi, rax                ; R
    mov r12, rdx                ; rank
    mov r13, [rsi+8]            ; n
    mov rcx, r13
    mov rdx, r13
    sub rdx, r12
    call mat_new
    mov r14, rax                ; K : n x (n - rank)
    xor r15d, r15d              ; f = candidate free column
    xor ebx, ebx                ; column of K being filled
.f:
    cmp r15, r13
    jge .done
    xor ecx, ecx
.p:                             ; is f a pivot column?
    cmp rcx, r12
    jge .free
    lea rax, [pivots]
    cmp [rax+rcx*8], r15
    je .nextf
    inc rcx
    jmp .p
.free:
    mov rcx, r14
    mov rdx, r15
    mov r8, rbx
    call cell
    mov rdx, [q_one]
    mov [rax], rdx              ; K[f][col] = 1
    mov qword [rsp], 0          ; i over pivot rows
.i:
    mov rcx, [rsp]
    cmp rcx, r12
    jge .idone
    mov rcx, rdi
    mov rdx, [rsp]
    mov r8, r15
    call cell
    mov rcx, [rax]
    call q_neg
    mov [rsp+8], rax            ; -R[i][f]
    lea rax, [pivots]
    mov rcx, [rsp]
    mov rdx, [rax+rcx*8]        ; pivot column of row i
    mov rcx, r14
    mov r8, rbx
    call cell
    mov rdx, [rsp+8]
    mov [rax], rdx
    inc qword [rsp]
    jmp .i
.idone:
    inc rbx
.nextf:
    inc r15
    jmp .f
.done:
    mov rax, r14
    add rsp, 16
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_image(rcx = A) -> rax : the pivot columns of A, a basis of the image (m x rank)
mat_image:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    mov rsi, rcx
    call mat_rref_copy
    mov r12, rdx                ; rank
    mov rcx, [rsi]
    mov rdx, r12
    call mat_new
    mov r14, rax
    xor r15d, r15d              ; k over pivots
.k:
    cmp r15, r12
    jge .done
    lea rax, [pivots]
    mov rdi, [rax+r15*8]        ; column c of A
    xor ebx, ebx                ; i over rows
.i:
    cmp rbx, [rsi]
    jge .nextk
    mov rcx, rsi
    mov rdx, rbx
    mov r8, rdi
    call cell
    mov r13, [rax]
    mov rcx, r14
    mov rdx, rbx
    mov r8, r15
    call cell
    mov [rax], r13
    inc rbx
    jmp .i
.nextk:
    inc r15
    jmp .k
.done:
    mov rax, r14
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_leftinverse(rcx = A, m x n) -> rax = L (n x m) with L A = 1, or 0 when the rank is below n.
; Row-reduce [A | 1]: the row operations E with E A = [1 ; 0] are on the right; the top n rows of E are L.
mat_leftinverse:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    mov rsi, rcx
    mov rcx, [rsi]
    call mat_identity
    mov rcx, rsi
    mov rdx, rax
    call mat_augment
    mov rdi, rax                ; [A | 1], m x (n + m)
    mov rcx, rdi
    call mat_rref
    mov r12, rax                ; pivots found over all n + m columns
    ; rank of A = pivots with column < n
    xor ebx, ebx
    xor r13d, r13d
.count:
    cmp rbx, r12
    jge .counted
    lea rax, [pivots]
    mov rax, [rax+rbx*8]
    cmp rax, [rsi+8]
    jge .counted
    inc r13
    inc rbx
    jmp .count
.counted:
    cmp r13, [rsi+8]
    jne .none
    mov rcx, [rsi+8]            ; n
    mov rdx, [rsi]              ; m
    call mat_new
    mov r14, rax
    xor r15d, r15d              ; i < n
.i:
    cmp r15, [rsi+8]
    jge .done
    xor ebx, ebx                ; j < m
.j:
    cmp rbx, [rsi]
    jge .nexti
    mov rcx, rdi
    mov rdx, r15
    mov r8, rbx
    add r8, [rsi+8]
    call cell
    mov r13, [rax]
    mov rcx, r14
    mov rdx, r15
    mov r8, rbx
    call cell
    mov [rax], r13
    inc rbx
    jmp .j
.nexti:
    inc r15
    jmp .i
.done:
    mov rax, r14
    jmp .out
.none:
    xor eax, eax
.out:
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_rightinverse(rcx = A) -> rax = R with A R = 1, or 0 : the transpose of the left inverse of A^T
mat_rightinverse:
    call mat_transpose
    mov rcx, rax
    call mat_leftinverse
    test rax, rax
    jz .none
    mov rcx, rax
    jmp mat_transpose
.none:
    ret

; mat_solve(rcx = A, rdx = b) -> rax = x with A x = b (free variables 0), or 0 when b is not in the image
mat_solve:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    mov rsi, rcx
    cmp qword [rdx+8], 1
    jne shape_error
    call mat_augment
    mov rdi, rax                ; [A | b]
    mov rcx, rdi
    call mat_rref
    mov r12, rax
    ; a pivot in the last column means b is not in the image
    xor ebx, ebx
.chk:
    cmp rbx, r12
    jge .ok
    lea rax, [pivots]
    mov rax, [rax+rbx*8]
    cmp rax, [rsi+8]
    je .none
    inc rbx
    jmp .chk
.ok:
    mov rcx, [rsi+8]
    mov edx, 1
    call mat_new
    mov r14, rax
    xor ebx, ebx
.x:
    cmp rbx, r12
    jge .done
    mov rcx, rdi
    mov rdx, rbx
    mov r8, [rsi+8]
    call cell
    mov r13, [rax]              ; the reduced right-hand side of row k
    lea rax, [pivots]
    mov rdx, [rax+rbx*8]
    mov rcx, r14
    xor r8d, r8d
    call cell
    mov [rax], r13
    inc rbx
    jmp .x
.done:
    mov rax, r14
    jmp .out
.none:
    xor eax, eax
.out:
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; ============================================================ printing values
print_mat:                      ; rcx = matrix; a column vector prints as one row; no columns prints []
    push rbx
    push rsi
    push r12
    push r13
    mov rsi, rcx
    cmp qword [rsi+8], 0
    je .empty
    cmp qword [rsi+8], 1
    jne .matrix
    mov cl, '['
    call emit_char
    xor ebx, ebx
.vec:
    cmp rbx, [rsi]
    jge .vec_end
    test rbx, rbx
    jz .v_first
    mov cl, ' '
    call emit_char
.v_first:
    mov rcx, [rsi+16+rbx*8]
    call q_emit
    inc rbx
    jmp .vec
.vec_end:
    mov cl, ']'
    call emit_char
    call emit_nl
    jmp .done
.empty:
    mov cl, '['
    call emit_char
    mov cl, ']'
    call emit_char
    call emit_nl
    jmp .done
.matrix:
    xor r12d, r12d
.row:
    cmp r12, [rsi]
    jge .done
    mov cl, '['
    call emit_char
    xor r13d, r13d
.col:
    cmp r13, [rsi+8]
    jge .row_end
    test r13, r13
    jz .c_first
    mov cl, ' '
    call emit_char
.c_first:
    mov rax, r12
    imul rax, [rsi+8]
    add rax, r13
    mov rcx, [rsi+16+rax*8]
    call q_emit
    inc r13
    jmp .col
.row_end:
    mov cl, ']'
    call emit_char
    call emit_nl
    inc r12
    jmp .row
.done:
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; ============================================================ fourth cut: more of the algebra, all over Q
; mat_trace(rcx = A) -> rax = the trace as a rational
mat_trace:
    push rbx
    push rsi
    push r12
    mov rsi, rcx
    mov rax, [rsi]
    cmp rax, [rsi+8]
    jne .notsq
    mov rbx, [q_zero]
    xor r12d, r12d
.l:
    cmp r12, [rsi]
    jge .done
    mov rcx, rsi
    mov rdx, r12
    mov r8, r12
    call cell
    mov rcx, rbx
    mov rdx, [rax]
    call q_add
    mov rbx, rax
    inc r12
    jmp .l
.done:
    mov rax, rbx
    pop r12
    pop rsi
    pop rbx
    ret
.notsq:
    lea rcx, [msg_notsq]
    mov edx, msg_notsq_len
    jmp fail

; scalar_mat(rcx = rational) -> rax = a 1x1 matrix holding it
scalar_mat:
    push rbx
    mov rbx, rcx
    mov ecx, 1
    mov edx, 1
    call mat_new
    mov [rax+16], rbx
    pop rbx
    ret

; mat_det(rcx = A) -> rax = the determinant as a rational: forward elimination on a copy, the product of the
; pivots, the sign flipped at every row swap; a column without a pivot gives 0
mat_det:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 32
    mov rax, [rcx]
    cmp rax, [rcx+8]
    jne .notsq
    call mat_copy
    mov rsi, rax
    mov r12, [rsi]              ; n
    mov r13, [q_one]            ; det
    xor r15d, r15d              ; c
.col:
    cmp r15, r12
    jge .done
    mov rbx, r15
.find:
    cmp rbx, r12
    jge .zero
    mov rcx, rsi
    mov rdx, rbx
    mov r8, r15
    call cell
    mov rcx, [rax]
    call q_is_zero
    test eax, eax
    jz .found
    inc rbx
    jmp .find
.found:
    cmp rbx, r15
    je .noswap
    xor edi, edi
.swap:
    cmp rdi, r12
    jge .swapped
    mov rcx, rsi
    mov rdx, rbx
    mov r8, rdi
    call cell
    mov [rsp], rax
    mov rcx, rsi
    mov rdx, r15
    mov r8, rdi
    call cell
    mov rcx, [rsp]
    mov rdx, [rcx]
    mov r8, [rax]
    mov [rcx], r8
    mov [rax], rdx
    inc rdi
    jmp .swap
.swapped:
    mov rcx, r13
    call q_neg
    mov r13, rax
.noswap:
    mov rcx, rsi
    mov rdx, r15
    mov r8, r15
    call cell
    mov rax, [rax]
    mov [rsp+8], rax            ; pivot
    mov rcx, r13
    mov rdx, rax
    call q_mul
    mov r13, rax
    lea rbx, [r15+1]            ; i below the pivot
.elim:
    cmp rbx, r12
    jge .nextcol
    mov rcx, rsi
    mov rdx, rbx
    mov r8, r15
    call cell
    mov rcx, [rax]
    mov rdx, [rsp+8]
    call q_div
    mov [rsp+16], rax           ; f = M[i][c] / pivot
    mov rdi, r15
.ej:
    cmp rdi, r12
    jge .nexti
    mov rcx, rsi
    mov rdx, r15
    mov r8, rdi
    call cell
    mov rcx, [rax]
    mov rdx, [rsp+16]
    call q_mul
    mov [rsp+24], rax
    mov rcx, rsi
    mov rdx, rbx
    mov r8, rdi
    call cell
    mov r14, rax
    mov rcx, [rax]
    mov rdx, [rsp+24]
    call q_sub
    mov [r14], rax
    inc rdi
    jmp .ej
.nexti:
    inc rbx
    jmp .elim
.nextcol:
    inc r15
    jmp .col
.zero:
    mov r13, [q_zero]
.done:
    mov rax, r13
    add rsp, 32
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.notsq:
    lea rcx, [msg_notsq]
    mov edx, msg_notsq_len
    jmp fail

; mat_charpoly(rcx = A) -> rax = the coefficients of det(x - A), highest first, as a column of n + 1 entries
; (Faddeev-LeVerrier: M_k = A M_(k-1) + c_(n-k+1) 1, c_(n-k) = -tr(A M_k) / k, exact over Q)
mat_charpoly:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 16
    mov rsi, rcx
    mov rax, [rsi]
    cmp rax, [rsi+8]
    jne .notsq
    mov r12, [rsi]              ; n
    lea rcx, [r12+1]
    mov edx, 1
    call mat_new
    mov r13, rax                ; c, index 0 = c_n ... index n = c_0
    mov rax, [q_one]
    mov [r13+16], rax
    mov rcx, r12
    mov rdx, r12
    call mat_new
    mov r14, rax                ; M = 0
    mov r15d, 1                 ; k
.k:
    cmp r15, r12
    jg .done
    mov rcx, rsi
    mov rdx, r14
    call mat_mul                ; A M
    mov rdi, rax
    mov rcx, r12
    call mat_identity
    lea rdx, [r15-1]
    mov rcx, [r13+16+rdx*8]     ; c_(n-k+1) is at index k-1
    mov rdx, rax
    call mat_scale
    mov rcx, rdi
    mov rdx, rax
    mov r8, 1
    call mat_addsub
    mov r14, rax                ; M_k
    mov rcx, rsi
    mov rdx, r14
    call mat_mul
    mov rcx, rax
    call mat_trace
    mov rcx, rax
    call q_neg
    mov [rsp], rax
    mov rcx, r15
    call q_from_i64
    mov rcx, [rsp]
    mov rdx, rax
    call q_div                  ; -tr(A M_k) / k
    mov [r13+16+r15*8], rax     ; c_(n-k) at index k
    inc r15
    jmp .k
.done:
    mov rax, r13
    add rsp, 16
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.notsq:
    lea rcx, [msg_notsq]
    mov edx, msg_notsq_len
    jmp fail

; mat_polyeval(rcx = c (a column, highest first), rdx = A square) -> rax = p(A) by Horner
mat_polyeval:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    mov rdi, rdx
    mov rax, [rdi]
    cmp rax, [rdi+8]
    jne .notsq
    cmp qword [rsi+8], 1
    jne shape_error
    mov rcx, [rdi]
    call mat_identity
    mov r13, rax                ; the identity, reused
    mov rcx, [rsi+16]
    mov rdx, r13
    call mat_scale
    mov r12, rax                ; P = c_top 1
    mov ebx, 1
.l:
    cmp rbx, [rsi]
    jge .done
    mov rcx, r12
    mov rdx, rdi
    call mat_mul
    mov r12, rax
    mov rcx, [rsi+16+rbx*8]
    mov rdx, r13
    call mat_scale
    mov rcx, r12
    mov rdx, rax
    mov r8, 1
    call mat_addsub
    mov r12, rax
    inc rbx
    jmp .l
.done:
    mov rax, r12
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.notsq:
    lea rcx, [msg_notsq]
    mov edx, msg_notsq_len
    jmp fail

; col_dot(rcx = M, rdx = i, r8 = j) -> rax = the inner product of columns i and j
col_dot:
    push rbx
    push rsi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 16
    mov rsi, rcx
    mov r12, rdx
    mov r13, r8
    mov rbx, [q_zero]
    xor r14d, r14d
.l:
    cmp r14, [rsi]
    jge .done
    mov rcx, rsi
    mov rdx, r14
    mov r8, r12
    call cell
    mov rax, [rax]
    mov [rsp], rax
    mov rcx, rsi
    mov rdx, r14
    mov r8, r13
    call cell
    mov rdx, [rax]
    mov rcx, [rsp]
    call q_mul
    mov rcx, rbx
    mov rdx, rax
    call q_add
    mov rbx, rax
    inc r14
    jmp .l
.done:
    mov rax, rbx
    add rsp, 16
    pop r15
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_orthogonalize(rcx = A) -> rax : Gram-Schmidt on the columns without any root: u_k = a_k - sum <a_k,u_j>/<u_j,u_j> u_j.
; The columns come out pairwise orthogonal, not normalised (normalising would need square roots, which leave Q).
; A dependent column comes out as the zero column.
mat_orthogonalize:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 32
    call mat_copy
    mov rsi, rax                ; U, worked in place column by column
    xor r12d, r12d              ; k
.k:
    cmp r12, [rsi+8]
    jge .done
    xor r13d, r13d              ; j < k
.j:
    cmp r13, r12
    jge .nextk
    mov rcx, rsi
    mov rdx, r13
    mov r8, r13
    call col_dot
    mov [rsp], rax              ; <u_j,u_j>
    mov rcx, rax
    call q_is_zero
    test eax, eax
    jnz .nextj
    mov rcx, rsi
    mov rdx, r12
    mov r8, r13
    call col_dot                ; <u_k,u_j>  (u_k as reduced so far; the same as <a_k,u_j> by orthogonality)
    mov rcx, rax
    mov rdx, [rsp]
    call q_div
    mov [rsp+8], rax            ; coef
    xor r14d, r14d              ; row
.r:
    cmp r14, [rsi]
    jge .nextj
    mov rcx, rsi
    mov rdx, r14
    mov r8, r13
    call cell
    mov rcx, [rax]
    mov rdx, [rsp+8]
    call q_mul
    mov [rsp+16], rax
    mov rcx, rsi
    mov rdx, r14
    mov r8, r12
    call cell
    mov r15, rax
    mov rcx, [rax]
    mov rdx, [rsp+16]
    call q_sub
    mov [r15], rax
    inc r14
    jmp .r
.nextj:
    inc r13
    jmp .j
.nextk:
    inc r12
    jmp .k
.done:
    mov rax, rsi
    add rsp, 32
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_projector(rcx = A) -> rax = A (A^T A)^-1 A^T, the orthogonal projection onto the image; 0 when the columns
; are dependent (A^T A singular)
mat_projector:
    push rbx
    push rsi
    push r12
    mov rsi, rcx
    call mat_transpose
    mov rbx, rax                ; A^T
    mov rcx, rbx
    mov rdx, rsi
    call mat_mul                ; A^T A
    mov rcx, rax
    call mat_leftinverse
    test rax, rax
    jz .none
    mov rcx, rsi
    mov rdx, rax
    call mat_mul                ; A (A^T A)^-1
    mov rcx, rax
    mov rdx, rbx
    call mat_mul
.none:
    pop r12
    pop rsi
    pop rbx
    ret

; mat_stack(rcx = A, rdx = B) -> rax = [A ; B]
mat_stack:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    mov rdi, rdx
    mov rax, [rsi+8]
    cmp rax, [rdi+8]
    jne shape_error
    mov rcx, [rsi]
    add rcx, [rdi]
    mov rdx, [rsi+8]
    call mat_new
    mov r12, rax
    mov rbx, [rsi]
    imul rbx, [rsi+8]
    xor r13d, r13d
.a:
    cmp r13, rbx
    jge .b0
    mov rax, [rsi+16+r13*8]
    mov [r12+16+r13*8], rax
    inc r13
    jmp .a
.b0:
    mov rcx, [rdi]
    imul rcx, [rdi+8]
    xor r13d, r13d
.b:
    cmp r13, rcx
    jge .done
    mov rax, [rdi+16+r13*8]
    lea rdx, [rbx+r13]
    mov [r12+16+rdx*8], rax
    inc r13
    jmp .b
.done:
    mov rax, r12
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_directsum(rcx = A, rdx = B) -> rax = the block diagonal [A 0 ; 0 B]
mat_directsum:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    mov rsi, rcx
    mov rdi, rdx
    mov rcx, [rsi]
    add rcx, [rdi]
    mov rdx, [rsi+8]
    add rdx, [rdi+8]
    call mat_new
    mov r12, rax
    xor r13d, r13d              ; row of A
.ar:
    cmp r13, [rsi]
    jge .b
    xor r14d, r14d
.ac:
    cmp r14, [rsi+8]
    jge .arn
    mov rcx, rsi
    mov rdx, r13
    mov r8, r14
    call cell
    mov rbx, [rax]
    mov rcx, r12
    mov rdx, r13
    mov r8, r14
    call cell
    mov [rax], rbx
    inc r14
    jmp .ac
.arn:
    inc r13
    jmp .ar
.b:
    xor r13d, r13d              ; row of B
.br:
    cmp r13, [rdi]
    jge .done
    xor r14d, r14d
.bc:
    cmp r14, [rdi+8]
    jge .brn
    mov rcx, rdi
    mov rdx, r13
    mov r8, r14
    call cell
    mov rbx, [rax]
    mov rcx, r12
    mov rdx, r13
    add rdx, [rsi]
    mov r8, r14
    add r8, [rsi+8]
    call cell
    mov [rax], rbx
    inc r14
    jmp .bc
.brn:
    inc r13
    jmp .br
.done:
    mov rax, r12
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_offdiag_zero(rcx = M square) -> eax 1 when every entry off the diagonal is zero
mat_offdiag_zero:
    push rbx
    push rsi
    push r12
    push r13
    mov rsi, rcx
    xor r12d, r12d
.i:
    cmp r12, [rsi]
    jge .yes
    xor r13d, r13d
.j:
    cmp r13, [rsi+8]
    jge .ni
    cmp r12, r13
    je .nj
    mov rcx, rsi
    mov rdx, r12
    mov r8, r13
    call cell
    mov rcx, [rax]
    call q_is_zero
    test eax, eax
    jz .no
.nj:
    inc r13
    jmp .j
.ni:
    inc r12
    jmp .i
.yes:
    mov eax, 1
    jmp .out
.no:
    xor eax, eax
.out:
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_refute(rcx = A [m x n], rdx = b [m x 1]) -> rax = y [m x 1] with y^T A = 0 and y^T b != 0, or 0 when the
; system A x = b is solvable (then no such certificate exists, by the Fredholm alternative). Constructive:
; row-reduce [A | b | I_m]; a pivot in the b column (index n) means that reduced row is [0..0 | 1 | y], so the
; last m entries y satisfy y A = 0 and y b = 1. This is the exact certificate of impossibility.
mat_refute:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 16
    mov rsi, rcx               ; A
    mov rdi, rdx               ; b
    mov rcx, rsi
    mov rdx, rdi
    call mat_augment           ; [A | b]
    mov r12, rax
    mov rcx, [rsi]
    call mat_identity          ; I_m
    mov rcx, r12
    mov rdx, rax
    call mat_augment           ; M = [A | b | I]
    mov r13, rax
    mov rcx, r13
    call mat_rref
    mov r14, rax               ; rank
    mov r15, [rsi+8]           ; n = cols A = the b column index
    xor ebx, ebx
.find:
    cmp rbx, r14
    jge .none
    lea rax, [pivots]
    mov rax, [rax+rbx*8]
    cmp rax, r15
    je .found
    inc rbx
    jmp .find
.found:
    mov rcx, [rsi]             ; m
    mov edx, 1
    call mat_new
    mov r12, rax               ; y
    xor r14d, r14d             ; k
.copy:
    cmp r14, [rsi]
    jge .done
    mov rcx, r13
    mov rdx, rbx
    mov r8, r15
    add r8, 1
    add r8, r14                ; column n+1+k
    call cell
    mov r9, [rax]
    mov [rsp], r9
    mov rcx, r12
    mov rdx, r14
    xor r8d, r8d
    call cell
    mov r9, [rsp]
    mov [rax], r9
    inc r14
    jmp .copy
.done:
    mov rax, r12
    jmp .out
.none:
    xor eax, eax
.out:
    add rsp, 16
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; int_scalar(rcx = int64) -> rax = a 1x1 value holding it as a rational
int_scalar:
    call q_from_i64
    mov rcx, rax
    jmp scalar_mat

; mat_firstcol(rcx = M, cols >= 1) -> rax = column 0 of M, as rows x 1
mat_firstcol:
    push rbx
    push rsi
    push r12
    push r13
    mov rsi, rcx
    mov rcx, [rsi]
    mov edx, 1
    call mat_new
    mov r12, rax
    xor r13d, r13d
.l:
    cmp r13, [rsi]
    jge .done
    mov rcx, rsi
    mov rdx, r13
    xor r8d, r8d
    call cell
    mov rbx, [rax]
    mov rcx, r12
    mov rdx, r13
    xor r8d, r8d
    call cell
    mov [rax], rbx
    inc r13
    jmp .l
.done:
    mov rax, r12
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_nullvector(rcx = A) -> rax = a nonzero v with A v = 0 (the first kernel basis vector), or 0 when A is
; injective (nullity 0). This is the constructive disproof of injectivity, dual to refute.
mat_nullvector:
    call mat_kernel
    cmp qword [rax+8], 0
    je .none
    mov rcx, rax
    jmp mat_firstcol
.none:
    xor eax, eax
    ret

; mat_cowitness(rcx = A) -> rax = a nonzero y with y^T A = 0 (a null vector of A^T), or 0 when A is surjective
; (rank = dim codomain). This is the constructive disproof of surjectivity: a covector vanishing on the image.
mat_cowitness:
    call mat_transpose
    mov rcx, rax
    call mat_kernel
    cmp qword [rax+8], 0
    je .none
    mov rcx, rax
    jmp mat_firstcol
.none:
    xor eax, eax
    ret

; mat_complement(rcx = A [m x n]) -> rax = S [n x rank]: the standard basis vectors e_{p} at A's pivot columns p.
; The columns of S are a basis of a complement to ker A in V, i.e. coset representatives for V/ker A: every coset
; has exactly one representative in span(S), and [kernel A | S] is a basis of V.
mat_complement:
    push rbx
    push rsi
    push r12
    push r13
    push r14
    mov rsi, rcx
    call mat_rref_copy         ; fills pivots[]; rdx = rank
    mov r12, rdx
    mov rcx, [rsi+8]           ; n
    mov rdx, r12
    call mat_new
    mov r13, rax               ; S (n x rank), all zero
    xor ebx, ebx
.l:
    cmp rbx, r12
    jge .done
    lea rax, [pivots]
    mov r14, [rax+rbx*8]       ; the pivot's column index in A
    mov rcx, r13
    mov rdx, r14
    mov r8, rbx
    call cell
    mov rdx, [q_one]
    mov [rax], rdx
    inc rbx
    jmp .l
.done:
    mov rax, r13
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_block(rcx = M, rdx = ptr to 4 qwords r1, r2, c1, c2, 0-based inclusive) -> rax = the submatrix
mat_block:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 16
    mov rsi, rcx
    mov r12, [rdx]
    mov r13, [rdx+8]
    mov r14, [rdx+16]
    mov r15, [rdx+24]
    test r12, r12
    js shape_error
    cmp r13, r12
    jl shape_error
    cmp r13, [rsi]
    jge shape_error
    test r14, r14
    js shape_error
    cmp r15, r14
    jl shape_error
    cmp r15, [rsi+8]
    jge shape_error
    mov rcx, r13
    sub rcx, r12
    inc rcx
    mov rdx, r15
    sub rdx, r14
    inc rdx
    call mat_new
    mov rbx, rax
    mov rdi, r12               ; i
.i:
    cmp rdi, r13
    jg .done
    mov rax, r14
    mov [rsp], rax             ; j
.j:
    mov rax, [rsp]
    cmp rax, r15
    jg .nexti
    mov rcx, rsi
    mov rdx, rdi
    mov r8, [rsp]
    call cell
    mov r9, [rax]
    mov [rsp+8], r9
    mov rcx, rbx
    mov rdx, rdi
    sub rdx, r12
    mov r8, [rsp]
    sub r8, r14
    call cell
    mov r9, [rsp+8]
    mov [rax], r9
    inc qword [rsp]
    jmp .j
.nexti:
    inc rdi
    jmp .i
.done:
    mov rax, rbx
    add rsp, 16
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; ============================================================ fifth cut: files of exact numbers
; The most in-need Windows task for a mathematician who does the books: read a file of numbers exactly, decide
; whether they reconcile to zero, and write results back without a single float ever touching them. A data file
; is whitespace-separated rationals; a decimal point in it is refused exactly as a decimal point in the source
; is (q_parse rejects it). load reads it, save writes it, total sums a column.

is_ws:                          ; cl = byte -> eax = 1 for space, tab, CR or LF
    xor eax, eax
    cmp cl, ' '
    je .y
    cmp cl, 9
    je .y
    cmp cl, 13
    je .y
    cmp cl, 10
    je .y
    ret
.y:
    mov eax, 1
    ret

is_ws_nl:                       ; cl = byte -> eax = 1 for space, tab or CR (not LF: LF ends a row)
    xor eax, eax
    cmp cl, ' '
    je .y
    cmp cl, 9
    je .y
    cmp cl, 13
    je .y
    ret
.y:
    mov eax, 1
    ret

win_close:                      ; rcx = handle; aligned so no movaps in CloseHandle faults
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 32
    call CloseHandle
    mov rsp, rbp
    pop rbp
    ret

; read_file_a(rcx = C string path) -> rax = bytes (arena), rdx = length; rax = 0 when it cannot be opened
read_file_a:
    push rbp
    mov rbp, rsp
    push rbx
    push rsi
    and rsp, -16
    sub rsp, 96
    mov edx, 0x80000000         ; GENERIC_READ
    mov r8d, 1                  ; FILE_SHARE_READ
    xor r9d, r9d
    mov qword [rsp+32], 3       ; OPEN_EXISTING
    mov qword [rsp+40], 0x80    ; FILE_ATTRIBUTE_NORMAL
    mov qword [rsp+48], 0
    call CreateFileA
    cmp rax, -1
    je .none
    mov rbx, rax
    mov rcx, rbx
    lea rdx, [rsp+64]
    call GetFileSizeEx          ; the buffer is sized by the file, not a fixed 64 MB
    mov rcx, [rsp+64]
    inc rcx
    call alloc
    mov rsi, rax
    mov rcx, rbx
    mov rdx, rsi
    mov r8, [rsp+64]
    lea r9, [rsp+56]
    mov qword [rsp+32], 0
    mov qword [rsp+56], 0
    call ReadFile
    mov rcx, rbx
    call CloseHandle
    mov rax, rsi
    mov edx, [rsp+56]
    jmp .out
.none:
    xor eax, eax
    xor edx, edx
.out:
    lea rsp, [rbp-16]
    pop rsi
    pop rbx
    pop rbp
    ret

; open_write_a(rcx = C string path) -> rax = handle or -1
open_write_a:
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 80
    mov edx, 0x40000000         ; GENERIC_WRITE
    xor r8d, r8d
    xor r9d, r9d
    mov qword [rsp+32], 2       ; CREATE_ALWAYS
    mov qword [rsp+40], 0x80
    mov qword [rsp+48], 0
    call CreateFileA
    mov rsp, rbp
    pop rbp
    ret

; open_write_w(rcx = UTF-16 path) -> rax = handle or -1
open_write_w:
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 80
    mov edx, 0x40000000
    xor r8d, r8d
    xor r9d, r9d
    mov qword [rsp+32], 2
    mov qword [rsp+40], 0x80
    mov qword [rsp+48], 0
    call CreateFileW
    mov rsp, rbp
    pop rbp
    ret

; parse_vec(rcx = ptr, rdx = len) -> rax = an n x 1 matrix of the file's whitespace-separated rationals
parse_vec:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    mov rsi, rcx
    lea rdi, [rcx+rdx]
    mov rbx, rsi
    xor r12d, r12d              ; count
.c_ws:
    cmp rbx, rdi
    jge .c_done
    movzx ecx, byte [rbx]
    call is_ws
    test eax, eax
    jz .c_tok0
    inc rbx
    jmp .c_ws
.c_tok0:
    inc r12
.c_tok:
    inc rbx
    cmp rbx, rdi
    jge .c_ws
    movzx ecx, byte [rbx]
    call is_ws
    test eax, eax
    jz .c_tok
    jmp .c_ws
.c_done:
    mov rcx, r12
    mov edx, 1
    call mat_new
    mov r13, rax
    mov rbx, rsi
    xor r14d, r14d              ; index
.f_ws:
    cmp rbx, rdi
    jge .f_done
    movzx ecx, byte [rbx]
    call is_ws
    test eax, eax
    jz .f_tok0
    inc rbx
    jmp .f_ws
.f_tok0:
    mov r12, rbx               ; token start
.f_tok:
    inc rbx
    cmp rbx, rdi
    jge .f_emit
    movzx ecx, byte [rbx]
    call is_ws
    test eax, eax
    jz .f_tok
.f_emit:
    mov rcx, r12
    mov rdx, rbx
    sub rdx, r12
    call q_parse
    mov [r13+16+r14*8], rax
    inc r14
    jmp .f_ws
.f_done:
    mov rax, r13
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; parse_mat(rcx = ptr, rdx = len) -> rax = a matrix, one row per non-empty line, entries whitespace-separated;
; every row must have the same number of entries
parse_mat:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 32
    mov rsi, rcx
    lea rdi, [rcx+rdx]
    mov rbx, rsi
    xor r13d, r13d             ; rows
    mov r14, -1                ; first row's column count
.p1line:
    cmp rbx, rdi
    jge .p1done
    movzx ecx, byte [rbx]
    call is_ws_nl
    test eax, eax
    jz .p1chk
    inc rbx
    jmp .p1line
.p1chk:
    movzx ecx, byte [rbx]
    cmp cl, 10
    jne .p1row
    inc rbx
    jmp .p1line
.p1row:
    xor r15d, r15d             ; columns in this row
.p1tok:
.p1t:
    inc rbx
    cmp rbx, rdi
    jge .p1te
    movzx ecx, byte [rbx]
    call is_ws
    test eax, eax
    jz .p1t
.p1te:
    inc r15
.p1s:
    cmp rbx, rdi
    jge .p1lineend
    movzx ecx, byte [rbx]
    call is_ws_nl
    test eax, eax
    jz .p1maybe
    inc rbx
    jmp .p1s
.p1maybe:
    movzx ecx, byte [rbx]
    cmp cl, 10
    jne .p1tok
.p1lineend:
    cmp r14, -1
    jne .p1cmp
    mov r14, r15
    jmp .p1rowinc
.p1cmp:
    cmp r15, r14
    jne shape_error
.p1rowinc:
    inc r13
    cmp rbx, rdi
    jge .p1done
    movzx ecx, byte [rbx]
    cmp cl, 10
    jne .p1line
    inc rbx
    jmp .p1line
.p1done:
    test r13, r13
    jz .empty
    mov rcx, r13
    mov rdx, r14
    call mat_new
    mov r12, rax
    mov rbx, rsi
    xor r13d, r13d             ; row index
.p2line:
    cmp rbx, rdi
    jge .p2done
    movzx ecx, byte [rbx]
    call is_ws_nl
    test eax, eax
    jz .p2chk
    inc rbx
    jmp .p2line
.p2chk:
    movzx ecx, byte [rbx]
    cmp cl, 10
    jne .p2row
    inc rbx
    jmp .p2line
.p2row:
    xor r15d, r15d             ; column index
.p2tok:
    mov [rsp], rbx             ; token start
.p2t:
    inc rbx
    cmp rbx, rdi
    jge .p2te
    movzx ecx, byte [rbx]
    call is_ws
    test eax, eax
    jz .p2t
.p2te:
    mov rcx, [rsp]
    mov rdx, rbx
    sub rdx, [rsp]
    call q_parse
    mov [rsp+8], rax
    mov rcx, r12
    mov rdx, r13
    mov r8, r15
    call cell
    mov rdx, [rsp+8]
    mov [rax], rdx
    inc r15
.p2s:
    cmp rbx, rdi
    jge .p2lineend
    movzx ecx, byte [rbx]
    call is_ws_nl
    test eax, eax
    jz .p2maybe
    inc rbx
    jmp .p2s
.p2maybe:
    movzx ecx, byte [rbx]
    cmp cl, 10
    jne .p2tok
.p2lineend:
    inc r13
    cmp rbx, rdi
    jge .p2done
    movzx ecx, byte [rbx]
    cmp cl, 10
    jne .p2line
    inc rbx
    jmp .p2line
.p2done:
    mov rax, r12
    jmp .out
.empty:
    xor ecx, ecx
    xor edx, edx
    call mat_new
.out:
    add rsp, 32
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_total(rcx = A) -> rax = the sum of every entry, as a rational
mat_total:
    push rbx
    push rsi
    push r12
    push r13
    mov rsi, rcx
    mov rbx, [q_zero]
    mov r12, [rsi]
    imul r12, [rsi+8]
    xor r13d, r13d
.l:
    cmp r13, r12
    jge .done
    mov rcx, rbx
    mov rdx, [rsi+16+r13*8]
    call q_add
    mov rbx, rax
    inc r13
    jmp .l
.done:
    mov rax, rbx
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; emit_value_plain(rcx = matrix): rows of space-separated numbers, one row per line; a column vector is one
; number per line, so save then load round-trips
emit_value_plain:
    push rbx
    push rsi
    push r12
    push r13
    mov rsi, rcx
    xor r12d, r12d
.row:
    cmp r12, [rsi]
    jge .done
    xor r13d, r13d
.col:
    cmp r13, [rsi+8]
    jge .rowend
    test r13, r13
    jz .first
    mov cl, ' '
    call emit_char
.first:
    mov rcx, rsi
    mov rdx, r12
    mov r8, r13
    call cell
    mov rcx, [rax]
    call q_emit
    inc r13
    jmp .col
.rowend:
    call emit_nl
    inc r12
    jmp .row
.done:
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; ---- statements ----
; load NAME PATH  /  load matrix NAME PATH  /  load NAME arg : a value from a file of exact numbers
st_load:
    push rbx
    push r12
    xor r12d, r12d             ; 0 vector, 1 matrix
    mov rcx, [cur]
    lea rdx, [kw_matrix]
    call tok_is
    test eax, eax
    jz .name
    inc qword [cur]
    mov r12d, 1
.name:
    call expect_word
    mov rbx, rax
    mov rcx, [cur]
    lea rdx, [kw_arg]
    call tok_is
    test eax, eax
    jz .file
    inc qword [cur]
    mov qword [load_tok], -1
    mov rcx, [titleptr]
    test rcx, rcx
    jz .fail
    call read_file_w
    jmp .parse
.file:
    call expect_word
    mov [load_tok], rax
    mov rcx, rax
    call tok_ptr
    mov rcx, [rax]
    mov rdx, [rax+8]
    lea r8, [procpathw]
    mov r9, 1030
    call utf8_to_wide
    lea rcx, [procpathw]
    mov word [rcx+rax*2], 0
    call read_file_w
.parse:
    test rax, rax
    jz .fail
    push rax                   ; the input's bytes are hashed for the certificate before they are parsed
    push rdx
    mov rcx, rax
    mov r8, [load_tok]
    cmp r8, -1                 ; the argument: named by the chapter line when there is one
    jne .chaparg
    mov r8, [chap_argtok]
.chaparg:
    call note_input
    pop rdx
    pop rax
    mov rcx, rax
    test r12, r12
    jz .vec
    call parse_mat
    jmp .store
.vec:
    call parse_vec
.store:
    mov rcx, rbx
    mov edx, 2
    mov r8, rax
    call sym_set
    pop r12
    pop rbx
    ret
.fail:
    lea rcx, [msg_loadfail]
    mov edx, msg_loadfail_len
    jmp fail

; save NAME PATH  /  save NAME arg : write a value as a file of exact numbers
st_save:
    push rbx
    push r12
    call expect_word
    mov rcx, rax
    call value_at
    mov rbx, rax
    mov rcx, [cur]
    lea rdx, [kw_arg]
    call tok_is
    test eax, eax
    jz .file
    inc qword [cur]
    mov rcx, [titleptr]
    call open_write_w
    jmp .have
.file:
    call expect_word
    mov rcx, rax
    lea rdx, [namebuf1]
    call token_to_cstr
    lea rcx, [namebuf1]
    call open_write_a
.have:
    cmp rax, -1
    je .fail
    mov r12, rax
    call emit_flush            ; the stdout buffer must not spill into the file
    mov rax, [hstdout]
    mov [savedh], rax
    mov rax, r12
    mov [hstdout], rax
    mov qword [outlen], 0
    mov rcx, rbx
    call emit_value_plain
    call emit_flush
    mov rax, [savedh]
    mov [hstdout], rax
    mov rcx, r12
    call win_close
    pop r12
    pop rbx
    ret
.fail:
    lea rcx, [msg_nowrite]
    mov edx, msg_nowrite_len
    jmp fail

; ============================================================ seventh cut: The Process, written as it happens
; A proof is a construction plus a checked verification; The Process is the append-only record of the search
; that produced it -- the attempts, the abandoned branches, the negatives -- saved to disk as the work happens,
; so nothing is discarded (after Terrence Tao: the negatives and the paths are part of the mathematics).

; say STRING : print a literal string (UTF-8 from the source) to stdout, then a newline
st_say:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    jne syntax_error
    mov rcx, [rax]
    mov rdx, [rax+8]
    call emit_str
    call emit_nl
    inc qword [cur]
    ret

; process STRING : open (create) the process log at that path; records are appended to it as they happen
st_process_cwd:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    jne syntax_error
    mov rcx, [cur]
    lea rdx, [namebuf1]
    call token_to_cstr
    lea rcx, [namebuf1]
    call open_write_a
    cmp rax, -1
    je .fail
    mov [proch], rax
    inc qword [cur]
    ret
.fail:
    lea rcx, [msg_nowrite]
    mov edx, msg_nowrite_len
    jmp fail

; record STRING  |  record value NAME : append a line to the process log; each record is written immediately
st_record:
    cmp qword [proch], 0
    je .noproc
    call emit_flush            ; do not let pending stdout spill into the log
    mov rax, [hstdout]
    mov [savedh], rax
    mov rax, [proch]
    mov [hstdout], rax
    mov qword [outlen], 0
    mov rcx, [cur]
    lea rdx, [kw_value]
    call tok_is
    test eax, eax
    jnz .value
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    jne .syntax
    mov rcx, [rax]
    mov rdx, [rax+8]
    call emit_str
    call emit_nl
    inc qword [cur]
    jmp .flush
.value:
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rcx, rax
    call emit_value_plain
.flush:
    inc qword [records_made]
    call emit_flush
    mov rax, [savedh]
    mov [hstdout], rax
    ret
.syntax:
    mov rax, [savedh]
    mov [hstdout], rax
    jmp syntax_error
.noproc:
    lea rcx, [msg_noproc]
    mov edx, msg_noproc_len
    jmp fail

; ============================================================ eleventh cut: polynomials, vec, sign
; Polynomials are coefficient columns, highest degree first (the convention of charpoly and evaluate).

; poly_trim(rcx = p) -> rax = p with leading zero coefficients dropped (a column of length >= 1; 0 stays [0])
poly_trim:
    push rbx
    push rsi
    push r12
    mov rsi, rcx
    xor ebx, ebx                ; first nonzero index
.scan:
    mov rax, [rsi]
    dec rax
    cmp rbx, rax
    jge .done                   ; keep at least the last coefficient
    mov rcx, [rsi+16+rbx*8]
    call q_is_zero
    test eax, eax
    jz .done
    inc rbx
    jmp .scan
.done:
    mov rcx, [rsi]
    sub rcx, rbx                ; new length
    mov r12, rcx
    mov edx, 1
    call mat_new
    xor ecx, ecx
.copy:
    cmp rcx, r12
    jge .out
    lea rdx, [rbx+rcx]
    mov rdx, [rsi+16+rdx*8]
    mov [rax+16+rcx*8], rdx
    inc rcx
    jmp .copy
.out:
    pop r12
    pop rsi
    pop rbx
    ret

; mat_polymul(rcx = p, rdx = q) -> rax = p q (columns, highest first)
mat_polymul:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    sub rsp, 16
    mov rsi, rcx
    mov rdi, rdx
    cmp qword [rsi+8], 1
    jne shape_error
    cmp qword [rdi+8], 1
    jne shape_error
    mov rcx, [rsi]
    add rcx, [rdi]
    dec rcx                     ; deg p + deg q + 1 coefficients
    mov edx, 1
    call mat_new
    mov r12, rax
    xor r13d, r13d              ; i over p
.i:
    cmp r13, [rsi]
    jge .done
    xor r14d, r14d              ; j over q
.j:
    cmp r14, [rdi]
    jge .nexti
    mov rcx, [rsi+16+r13*8]
    mov rdx, [rdi+16+r14*8]
    call q_mul
    mov [rsp], rax
    lea rbx, [r13+r14]
    mov rcx, [r12+16+rbx*8]
    mov rdx, [rsp]
    call q_add
    mov [r12+16+rbx*8], rax
    inc r14
    jmp .j
.nexti:
    inc r13
    jmp .i
.done:
    mov rcx, r12
    call poly_trim
    add rsp, 16
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_polydivmod(rcx = p, rdx = d) -> rax = quotient, rdx = remainder (both trimmed); d = 0 stops the program.
; Long division over Q, exact at every step.
mat_polydivmod:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 32
    mov rdi, rdx                ; keep d before the first call clobbers rdx
    call poly_trim
    mov rsi, rax                ; p (trimmed)
    mov rcx, rdi
    call poly_trim
    mov rdi, rax                ; d (trimmed)
    mov rcx, [rdi+16]
    call q_is_zero
    test eax, eax
    jnz .divzero
    mov rcx, rsi
    call mat_copy
    mov r12, rax                ; r = working remainder (a copy of p)
    mov rax, [rsi]
    sub rax, [rdi]
    inc rax                     ; quotient length = len p - len d + 1
    cmp rax, 1
    jge .haveq
    mov eax, 1
.haveq:
    mov rcx, rax
    mov edx, 1
    call mat_new
    mov r13, rax                ; q
    mov rax, [rsi]
    cmp rax, [rdi]
    jl .done                    ; deg p < deg d: quotient 0, remainder p
    xor r14d, r14d              ; k = position of the current leading term of r
.step:
    mov rax, [r12]
    sub rax, [rdi]
    cmp r14, rax
    jg .done                    ; no more terms of degree >= deg d
    mov rcx, [r12+16+r14*8]
    mov rdx, [rdi+16]
    call q_div                  ; coefficient c = r[k] / d[0]
    mov [rsp], rax
    mov [r13+16+r14*8], rax     ; q[k] = c
    xor r15d, r15d              ; j over d
.sub:
    cmp r15, [rdi]
    jge .next
    mov rcx, [rsp]
    mov rdx, [rdi+16+r15*8]
    call q_mul                  ; c d[j]
    mov [rsp+8], rax
    lea rbx, [r14+r15]
    mov rcx, [r12+16+rbx*8]
    mov rdx, [rsp+8]
    call q_sub                  ; r[k+j] -= c d[j]
    lea rbx, [r14+r15]
    mov [r12+16+rbx*8], rax
    inc r15
    jmp .sub
.next:
    inc r14
    jmp .step
.done:
    mov rcx, r12
    call poly_trim
    mov rdx, rax                ; remainder (trimmed; the cancelled high terms are exact zeros)
    mov [rsp+16], rdx
    mov rcx, r13
    call poly_trim
    mov rdx, [rsp+16]
    add rsp, 32
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.divzero:
    lea rcx, [msg_divzero]
    mov edx, msg_divzero_len
    jmp fail

; mat_vec(rcx = M) -> rax = the entries of M stacked column by column, as a (rows*cols) x 1 column
mat_vec:
    push rbx
    push rsi
    push r12
    push r13
    push r14
    mov rsi, rcx
    mov rcx, [rsi]
    imul rcx, [rsi+8]
    mov edx, 1
    call mat_new
    mov r12, rax
    xor r13d, r13d              ; column j
    xor ebx, ebx                ; output index
.j:
    cmp r13, [rsi+8]
    jge .done
    xor r14d, r14d              ; row i
.i:
    cmp r14, [rsi]
    jge .nextj
    mov rcx, rsi
    mov rdx, r14
    mov r8, r13
    call cell
    mov rax, [rax]
    mov [r12+16+rbx*8], rax
    inc rbx
    inc r14
    jmp .i
.nextj:
    inc r13
    jmp .j
.done:
    mov rax, r12
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_diagonal(rcx = v, a column) -> rax = the diagonal matrix with v on the diagonal
mat_diagonal:
    push rbx
    push rsi
    push r12
    mov rsi, rcx
    cmp qword [rsi+8], 1
    jne shape_error
    mov rcx, [rsi]
    mov rdx, rcx
    call mat_new
    mov r12, rax
    xor ebx, ebx
.l:
    cmp rbx, [rsi]
    jge .done
    mov rcx, r12
    mov rdx, rbx
    mov r8, rbx
    call cell
    mov rdx, [rsi+16+rbx*8]
    mov [rax], rdx
    inc rbx
    jmp .l
.done:
    mov rax, r12
    pop r12
    pop rsi
    pop rbx
    ret

; mat_nonnegative(rcx = M) -> eax = 1 when every entry is >= 0 (the sign of a rational is the sign of its
; numerator, the denominator being positive; an exact decision, no ordering of approximations)
mat_nonnegative:
    push rbx
    push rsi
    mov rsi, rcx
    mov rbx, [rsi]
    imul rbx, [rsi+8]
.l:
    test rbx, rbx
    jz .yes
    dec rbx
    mov rax, [rsi+16+rbx*8]     ; the rational
    mov rax, [rax]              ; its numerator
    cmp qword [rax], 0          ; sign word: 1 means negative
    jne .no
    jmp .l
.yes:
    mov eax, 1
    pop rsi
    pop rbx
    ret
.no:
    xor eax, eax
    pop rsi
    pop rbx
    ret

; mat_polyaddsub(rcx = p, rdx = q, r8 = 1 add / -1 subtract) -> rax : the shorter is padded with leading zeros
mat_polyaddsub:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    mov rsi, rcx
    mov rdi, rdx
    mov r15, r8
    mov r12, [rsi]
    mov r13, [rdi]
    mov rcx, r12
    cmp r13, rcx
    cmovg rcx, r13              ; n = max length
    mov r14, rcx
    mov edx, 1
    call mat_new
    mov rbx, rax
    xor ecx, ecx                ; i from 0 to n-1 (highest first); p[i - (n - lenp)] when in range
.l:
    cmp rcx, r14
    jge .done
    push rcx
    ; a = p entry aligned at the right end
    mov rax, r14
    sub rax, r12                ; offset for p
    mov rdx, rcx
    sub rdx, rax
    mov r8, [q_zero]
    js .noa
    mov r8, [rsi+16+rdx*8]
.noa:
    mov rax, r14
    sub rax, r13                ; offset for q
    mov rdx, rcx
    sub rdx, rax
    mov r9, [q_zero]
    js .nob
    mov r9, [rdi+16+rdx*8]
.nob:
    mov rcx, r8
    mov rdx, r9
    test r15, r15
    js .sub
    call q_add
    jmp .put
.sub:
    call q_sub
.put:
    pop rcx
    mov [rbx+16+rcx*8], rax
    inc rcx
    jmp .l
.done:
    mov rcx, rbx
    call poly_trim
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; ============================================================ twelfth cut: quotients, homology, exactness, blocks
; A homology class is a quotient of a kernel by an image; the language builds it as the columns of the kernel that
; are independent modulo the image, so every class carries an explicit representative and every representative can
; be tested (solve: it is a boundary, the chain is produced; refute: it is not, the cocycle is produced).

; mat_copycols(rcx = M, rdx = c0, r8 = n) -> rax = the n columns of M starting at column c0 (n may be 0)
mat_copycols:
    push rbx
    mov rbx, rcx
    test r8, r8
    jz .empty
    lea rax, [callargs]
    mov qword [rax], 0
    mov rcx, [rbx]
    dec rcx
    mov [rax+8], rcx
    mov [rax+16], rdx
    lea rcx, [rdx+r8-1]
    mov [rax+24], rcx
    mov rcx, rbx
    mov rdx, rax
    call mat_block
    pop rbx
    ret
.empty:
    mov rcx, [rbx]
    xor edx, edx
    call mat_new
    pop rbx
    ret

; mat_quotient(rcx = K, rdx = B) -> rax = representatives of span K modulo span B: the columns of K that the
; elimination of [B | K] keeps as pivots after B's own pivots; 0 when span B is not inside span K.
mat_quotient:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    mov rdi, rdx
    mov rax, [rsi]
    cmp rax, [rdi]
    jne shape_error
    mov rcx, rdi
    call mat_rank
    mov r12, rax                ; rank B
    mov rcx, rsi
    call mat_rank
    mov r13, rax                ; rank K
    mov rcx, rdi
    mov rdx, rsi
    call mat_augment
    mov rcx, rax
    call mat_image
    mov rbx, rax                ; pivot columns of [B | K]
    mov rax, [rbx+8]
    cmp rax, r13
    jne .notinside
    mov rcx, rbx
    mov rdx, r12
    mov r8, r13
    sub r8, r12
    call mat_copycols
    jmp .out
.notinside:
    xor eax, eax
.out:
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_homology(rcx = d1 : C_k -> C_{k-1}, rdx = d2 : C_{k+1} -> C_k) -> rax = representatives of ker d1 / im d2,
; or 0 when d1 d2 is not zero (then this is not a chain complex)
mat_homology:
    push rbx
    push rsi
    push rdi
    mov rsi, rcx
    mov rdi, rdx
    mov rax, [rsi+8]
    cmp rax, [rdi]
    jne shape_error
    call mat_mul
    mov rcx, rax
    call mat_is_zero
    test eax, eax
    jz .notzero
    mov rcx, rsi
    call mat_kernel
    mov rbx, rax
    mov rcx, rdi
    call mat_image
    mov rdx, rax
    mov rcx, rbx
    call mat_quotient
    jmp .out
.notzero:
    xor eax, eax
.out:
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_exact(rcx = A, rdx = B) -> eax = 1 when A B = 0 and rank B = nullity A, i.e. im B = ker A
mat_exact:
    push rbx
    push rsi
    push rdi
    mov rsi, rcx
    mov rdi, rdx
    mov rax, [rsi+8]
    cmp rax, [rdi]
    jne shape_error
    call mat_mul
    mov rcx, rax
    call mat_is_zero
    test eax, eax
    jz .no
    mov rcx, rdi
    call mat_rank
    mov rbx, rax
    mov rcx, rsi
    call mat_rank
    mov rcx, [rsi+8]
    sub rcx, rax
    cmp rcx, rbx
    jne .no
    mov eax, 1
    jmp .out
.no:
    xor eax, eax
.out:
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_blockdet(rcx = M, rdx = k) -> rax = the (rows/k) x (cols/k) matrix of the determinants of the k x k blocks.
; With the complex numbers as 2x2 blocks, this is the matrix of squared moduli |z|^2 = det [[a -b][b a]]; with a
; number field as its regular representation, the field norm.
mat_blockdet:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 8
    mov rsi, rcx
    mov r12, rdx
    test r12, r12
    jle shape_error
    mov rax, [rsi]
    xor edx, edx
    div r12
    test rdx, rdx
    jnz shape_error
    mov r13, rax                ; block rows
    mov rax, [rsi+8]
    xor edx, edx
    div r12
    test rdx, rdx
    jnz shape_error
    mov r14, rax                ; block cols
    mov rcx, r13
    mov rdx, r14
    call mat_new
    mov rbx, rax
    xor edi, edi
.i:
    cmp rdi, r13
    jge .done
    xor r15d, r15d
.j:
    cmp r15, r14
    jge .nexti
    lea rax, [callargs]
    mov rcx, rdi
    imul rcx, r12
    mov [rax], rcx
    add rcx, r12
    dec rcx
    mov [rax+8], rcx
    mov rcx, r15
    imul rcx, r12
    mov [rax+16], rcx
    add rcx, r12
    dec rcx
    mov [rax+24], rcx
    mov rcx, rsi
    mov rdx, rax
    call mat_block
    mov rcx, rax
    call mat_det
    mov [rsp], rax
    mov rcx, rbx
    mov rdx, rdi
    mov r8, r15
    call cell
    mov rdx, [rsp]
    mov [rax], rdx
    inc r15
    jmp .j
.nexti:
    inc rdi
    jmp .i
.done:
    mov rax, rbx
    add rsp, 8
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_blocktrace(rcx = M square, rdx = k) -> rax = the sum of the k x k diagonal blocks (the trace over the
; block algebra: for complex numbers as 2x2 blocks, the complex trace as a block)
mat_blocktrace:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    mov r12, rdx
    test r12, r12
    jle shape_error
    mov rax, [rsi]
    cmp rax, [rsi+8]
    jne shape_error
    xor edx, edx
    div r12
    test rdx, rdx
    jnz shape_error
    mov r13, rax                ; number of blocks
    mov rcx, r12
    mov rdx, r12
    call mat_new
    mov rbx, rax                ; accumulator
    xor edi, edi
.i:
    cmp rdi, r13
    jge .done
    lea rax, [callargs]
    mov rcx, rdi
    imul rcx, r12
    mov [rax], rcx
    mov [rax+16], rcx
    add rcx, r12
    dec rcx
    mov [rax+8], rcx
    mov [rax+24], rcx
    mov rcx, rsi
    mov rdx, rax
    call mat_block
    mov rcx, rbx
    mov rdx, rax
    mov r8, 1
    call mat_addsub
    mov rbx, rax
    inc rdi
    jmp .i
.done:
    mov rax, rbx
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; mat_diagvec(rcx = M) -> rax = the diagonal entries of M as a column of length min(rows, cols)
mat_diagvec:
    push rbx
    push rsi
    push r12
    push r13
    mov rsi, rcx
    mov rcx, [rsi]
    cmp rcx, [rsi+8]
    jle .n
    mov rcx, [rsi+8]
.n:
    mov r13, rcx
    mov edx, 1
    call mat_new
    mov r12, rax
    xor ebx, ebx
.l:
    cmp rbx, r13
    jge .done
    mov rcx, rsi
    mov rdx, rbx
    mov r8, rbx
    call cell
    mov rax, [rax]
    mov [r12+16+rbx*8], rax
    inc rbx
    jmp .l
.done:
    mov rax, r12
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; mat_unvec(rcx = v (a column), rdx = m) -> rax = the m x (len/m) matrix whose columns are the consecutive
; pieces of v (the inverse of vec)
mat_unvec:
    push rbx
    push rsi
    push r12
    push r13
    push r14
    mov rsi, rcx
    mov r12, rdx
    cmp qword [rsi+8], 1
    jne shape_error
    test r12, r12
    jle shape_error
    mov rax, [rsi]
    xor edx, edx
    div r12
    test rdx, rdx
    jnz shape_error
    mov r13, rax                ; columns
    mov rcx, r12
    mov rdx, r13
    call mat_new
    mov r14, rax
    xor ebx, ebx                ; running index into v
.j:
    cmp rbx, [rsi]
    jge .done
    mov rax, rbx
    xor edx, edx
    div r12                     ; rax = column, rdx = row
    mov r8, rax
    mov rcx, r14
    call cell
    mov rdx, [rsi+16+rbx*8]
    mov [rax], rdx
    inc rbx
    jmp .j
.done:
    mov rax, r14
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; ---- The Process as the execution generates it ----
; While a process log is open, every statement the interpreter executes is appended to it as "N: <source line>"
; before it runs; a failure appends "FAILED line N: <message>"; a normal end appends the closing line. So the log is
; the actual sequence of operations, the obligations actually discharged, and the one that failed if one did --
; not a narration. `record` lines remain the author's annotations inside that sequence.
proc_begin:                     ; flush stdout, then point the emitter at the process log
    call emit_flush
    mov rax, [hstdout]
    mov [savedh], rax
    mov rax, [proch]
    mov [hstdout], rax
    mov qword [outlen], 0
    ret
proc_end:                       ; flush the log, point the emitter back at stdout
    call emit_flush
    mov rax, [savedh]
    mov [hstdout], rax
    ret

trace_line:                     ; append "N: <the source text of the current line>"
    cmp qword [proch], 0
    je .ret
    cmp qword [traceoff], 0
    jne .ret
    push rbx
    push r12
    call proc_begin
    mov rcx, [lineno]
    call emit_int
    mov cl, ':'
    call emit_char
    mov cl, ' '
    call emit_char
    mov rcx, [cur]
    call tok_ptr
    mov rbx, [rax]              ; start of the first token
    mov r12, [cur]
.f:
    cmp r12, [ntok]
    jge .eof
    mov rcx, r12
    call tok_ptr
    cmp qword [rax+16], 3
    je .nl
    inc r12
    jmp .f
.nl:
    mov rdx, [rax]              ; the newline's position
    jmp .w
.eof:
    mov rdx, [srcptr]
    add rdx, [srclen]
.w:
    sub rdx, rbx
    mov rcx, rbx
    call emit_str
    call emit_nl
    call proc_end
    pop r12
    pop rbx
.ret:
    ret

trace_end:                      ; the program ran to its end: every obligation was discharged
    call top_log                ; the one program: its own log takes the certificate
    cmp qword [proch], 0
    je .ret
    call proc_begin
    call cert_lines
    lea rcx, [msg_proc_end]
    mov edx, msg_proc_end_len
    call emit_str
    call proc_end
.ret:
    ret

trace_fail:                     ; rcx = msg, rdx = len : append "FAILED line N: msg" (called from fail)
    call top_log
    cmp qword [proch], 0
    je .ret
    push rbx
    push r12
    mov rbx, rcx
    mov r12, rdx
    call proc_begin
    call cert_lines
    lea rcx, [msg_proc_failed]
    call emit_cstr
    lea rcx, [msg_line]
    call emit_cstr
    mov rcx, [lineno]
    call emit_int
    mov cl, ':'
    call emit_char
    mov cl, ' '
    call emit_char
    mov rcx, rbx
    mov rdx, r12
    call emit_str
    call proc_end
    pop r12
    pop rbx
.ret:
    ret

; ============================================================ twelfth cut (continued): blockwise products, the Process next to the proof

; mat_blockmul(rcx = A, rdx = B, r8 = k) -> rax = the blockwise product: block (i,j) of the result is A_ij B_ij for
; the k x k blocks. With a number field as k x k blocks this is the entrywise product of two matrices over the
; field; with B = the blockwise conjugate of A it gives the squared moduli |a_ij|^2 as blocks.
mat_blockmul:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 40
    mov rsi, rcx
    mov rdi, rdx
    mov r12, r8
    test r12, r12
    jle shape_error
    mov rax, [rsi]
    cmp rax, [rdi]
    jne shape_error
    mov rax, [rsi+8]
    cmp rax, [rdi+8]
    jne shape_error
    mov rax, [rsi]
    xor edx, edx
    div r12
    test rdx, rdx
    jnz shape_error
    mov r13, rax                ; block rows
    mov rax, [rsi+8]
    xor edx, edx
    div r12
    test rdx, rdx
    jnz shape_error
    mov r14, rax                ; block cols
    mov rcx, [rsi]
    mov rdx, [rsi+8]
    call mat_new
    mov rbx, rax
    mov qword [rsp], 0          ; i
.i:
    mov rax, [rsp]
    cmp rax, r13
    jge .done
    mov qword [rsp+8], 0        ; j
.j:
    mov rax, [rsp+8]
    cmp rax, r14
    jge .nexti
    lea rax, [callargs]
    mov rcx, [rsp]
    imul rcx, r12
    mov [rax], rcx
    add rcx, r12
    dec rcx
    mov [rax+8], rcx
    mov rcx, [rsp+8]
    imul rcx, r12
    mov [rax+16], rcx
    add rcx, r12
    dec rcx
    mov [rax+24], rcx
    mov rcx, rsi
    mov rdx, rax
    call mat_block
    mov r15, rax
    lea rdx, [callargs]
    mov rcx, rdi
    call mat_block
    mov rcx, r15
    mov rdx, rax
    call mat_mul
    mov r15, rax                ; the k x k product
    mov qword [rsp+16], 0       ; r
.r:
    mov rax, [rsp+16]
    cmp rax, r12
    jge .nextj
    mov qword [rsp+24], 0       ; c
.c:
    mov rax, [rsp+24]
    cmp rax, r12
    jge .nextr
    mov rcx, r15
    mov rdx, [rsp+16]
    mov r8, [rsp+24]
    call cell
    mov rax, [rax]
    mov [rsp+32], rax
    mov rdx, [rsp]
    imul rdx, r12
    add rdx, [rsp+16]
    mov r8, [rsp+8]
    imul r8, r12
    add r8, [rsp+24]
    mov rcx, rbx
    call cell
    mov rdx, [rsp+32]
    mov [rax], rdx
    inc qword [rsp+24]
    jmp .c
.nextr:
    inc qword [rsp+16]
    jmp .r
.nextj:
    inc qword [rsp+8]
    jmp .j
.nexti:
    inc qword [rsp]
    jmp .i
.done:
    mov rax, rbx
    add rsp, 40
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; process STRING : open (create) the process log. A relative path is taken relative to the directory of the program
; file (or of the executable, when the program is embedded), so the Process lives next to the proof whatever the
; working directory is; an absolute path (X:..., \..., /...) is used as written.
st_process:
    push rbx
    push rsi
    push r12
    push r13
    push r14
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    jne syntax_error
    mov r12, [rax]              ; the name's bytes
    mov r13, [rax+8]            ; its length
    lea rbx, [procpathw]        ; the wide path being built
    xor r14d, r14d              ; words written
    test r13, r13
    jz .rel
    cmp byte [r12], '\'
    je .append
    cmp byte [r12], '/'
    je .append
    cmp r13, 2
    jb .rel
    cmp byte [r12+1], ':'
    je .append
.rel:
    mov rsi, [wpath]            ; the program's path, or 0 when embedded
    test rsi, rsi
    jnz .scan
    lea rsi, [wbuf]             ; then the executable's own path
.scan:                          ; find the last separator
    xor ecx, ecx                ; index
    mov rdx, -1                 ; last separator index (64-bit: edx would zero-extend)
.s:
    movzx eax, word [rsi+rcx*2]
    test eax, eax
    jz .copy
    cmp eax, '\'
    je .sep
    cmp eax, '/'
    jne .next
.sep:
    mov rdx, rcx
.next:
    inc rcx
    cmp rcx, 1000
    jb .s
.copy:                          ; copy words 0 .. last separator inclusive
    test rdx, rdx
    js .append
    xor ecx, ecx
.cp:
    movzx eax, word [rsi+rcx*2]
    mov [rbx+r14*2], ax
    inc r14
    inc rcx
    cmp rcx, rdx
    jle .cp
.append:                        ; the name, UTF-8 to UTF-16
    mov rcx, r12
    mov rdx, r13
    lea r8, [rbx+r14*2]
    mov r9, 1030
    sub r9, r14
    call utf8_to_wide
    add r14, rax
.term:
    mov word [rbx+r14*2], 0
    mov rcx, rbx
    call open_append_w
    cmp rax, -1
    je .fail
    mov [proch], rax
    call proc_run_header
    inc qword [cur]
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret
.fail:
    lea rcx, [msg_nowrite]
    mov edx, msg_nowrite_len
    jmp fail

; ============================================================ thirteenth cut: the log appends across runs, trace on/off, arena blocks
; The Process log is opened for appending and every run starts with a header line, so successive attempts stay in
; the same file in order; `trace off` / `trace on` silence and resume the statement trace (for a mechanical inner
; loop whose attempts are recorded by `record` instead); `arena mark` / `arena release` bound the memory of a loop
; body: everything allocated and every name bound after the mark is dropped at the release, and a name from before
; the mark that was rebound to a value inside the block is a checked error (a machine word may be rebound freely).

; open_append_w(rcx = UTF-16 path) -> rax = handle or -1 : OPEN_ALWAYS with FILE_APPEND_DATA, every write lands at the end
open_append_w:
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 80
    mov edx, 0x00100004         ; FILE_APPEND_DATA | SYNCHRONIZE
    mov r8d, 1                  ; FILE_SHARE_READ: the log may be read while the program runs
    xor r9d, r9d
    mov qword [rsp+32], 4       ; OPEN_ALWAYS
    mov qword [rsp+40], 0x80
    mov qword [rsp+48], 0
    call CreateFileW
    mov rsp, rbp
    pop rbp
    ret

emit_2d:                        ; rcx = 0..99 : two digits
    push rcx
    cmp rcx, 10
    jae .two
    mov cl, '0'
    call emit_char
.two:
    pop rcx
    jmp emit_int

; proc_run_header: append "==== run YYYY-MM-DD HH:MM:SS  <program path> ====" to the log just opened
proc_run_header:
    push rbx
    push rsi
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 64
    lea rcx, [rsp+32]           ; SYSTEMTIME: year, month, dayofweek, day, hour, minute, second, ms (words)
    call GetLocalTime
    call proc_begin
    lea rcx, [msg_proc_run]
    call emit_cstr
    movzx ecx, word [rsp+32]
    call emit_int
    mov cl, '-'
    call emit_char
    movzx ecx, word [rsp+34]
    call emit_2d
    mov cl, '-'
    call emit_char
    movzx ecx, word [rsp+38]
    call emit_2d
    mov cl, ' '
    call emit_char
    movzx ecx, word [rsp+40]
    call emit_2d
    mov cl, ':'
    call emit_char
    movzx ecx, word [rsp+42]
    call emit_2d
    mov cl, ':'
    call emit_char
    movzx ecx, word [rsp+44]
    call emit_2d
    mov cl, ' '
    call emit_char
    mov cl, ' '
    call emit_char
    mov rsi, [wpath]
    test rsi, rsi
    jnz .path
    lea rsi, [wbuf]
.path:
    movzx eax, word [rsi]
    test eax, eax
    jz .end
    mov cl, al
    call emit_char
    add rsi, 2
    jmp .path
.end:
    lea rcx, [msg_proc_run_end]
    call emit_cstr
    call proc_end
    mov rsp, rbp
    pop rbp
    pop rsi
    pop rbx
    ret

; trace on | trace off
st_trace:
    mov rcx, [cur]
    lea rdx, [kw_on]
    call tok_is
    test eax, eax
    jnz .on
    mov rcx, [cur]
    lea rdx, [kw_off]
    call tok_is
    test eax, eax
    jnz .off
    jmp syntax_error
.on:
    mov qword [traceoff], 0
    inc qword [cur]
    ret
.off:
    mov qword [traceoff], 1
    inc qword [cur]
    ret

; arena mark | arena release
st_arena:
    mov rcx, [cur]
    lea rdx, [kw_mark]
    call tok_is
    test eax, eax
    jnz .mark
    mov rcx, [cur]
    lea rdx, [kw_release]
    call tok_is
    test eax, eax
    jnz .release
    jmp syntax_error
.mark:
    mov rax, [arena]
    mov [arena_mark], rax
    mov rax, [nsym]
    mov [mark_nsym], rax
    mov qword [marked], 1
    inc qword [cur]
    ret
.release:
    cmp qword [marked], 0
    je .nomark
    push rbx
    push rdi
    push r12
    lea rbx, [symbols]
    xor r12d, r12d
.chk:                           ; no value from before the mark may point into the block's memory
    cmp r12, [mark_nsym]
    jge .claims
    cmp qword [rbx+16], 2
    jne .nx
    mov rax, [rbx+24]
    cmp rax, [arena_mark]
    jae .rebound
.nx:
    add rbx, 32
    inc r12
    jmp .chk
.claims:                        ; nor may an open claim refer to a value inside the block
    xor r12d, r12d
.cl:
    cmp r12, [nclaims]
    jge .ok
    lea rax, [claim_a]
    mov rax, [rax+r12*8]
    cmp rax, [arena_mark]
    jae .claimrel
    lea rax, [claim_b]
    mov rax, [rax+r12*8]
    test rax, rax
    jz .cnext
    cmp rax, [arena_mark]
    jae .claimrel
.cnext:
    inc r12
    jmp .cl
.ok:
    mov rax, [mark_nsym]
    mov [nsym], rax
    mov rdi, [arena_mark]       ; zero the block's memory (allocations are assumed fresh)
    mov rcx, [arena]
    sub rcx, rdi
    shr rcx, 3
    xor eax, eax
    rep stosq
    mov rax, [arena_mark]
    mov [arena], rax
    pop r12
    pop rdi
    pop rbx
    inc qword [cur]
    ret
.claimrel:
    lea rcx, [msg_claimrel]
    mov edx, msg_claimrel_len
    jmp fail
.rebound:
    lea rcx, [msg_rebound]
    mov edx, msg_rebound_len
    jmp fail
.nomark:
    lea rcx, [msg_norelease]
    mov edx, msg_norelease_len
    jmp fail

; line_of(rcx = token index) -> rax = the number of the line holding that token (read off the newline token that
; ends it), so that goto / gosub / return keep `lineno` true for the trace and the error messages
line_of:
.f:
    cmp rcx, [ntok]
    jge .eof
    push rcx
    call tok_ptr
    pop rcx
    cmp qword [rax+16], 3
    je .nl
    inc rcx
    jmp .f
.nl:
    lea rdx, [tokline]
    mov rax, [rdx+rcx*8]
    ret
.eof:
    mov rax, [lineno]
    ret

; ============================================================ fourteenth cut: the certificate block (the Finite Data Principle)
; At the end of every run that keeps a Process log -- normal end or failure -- the interpreter appends a certificate:
; the program's path and the SHA-256 of its bytes as read, the interpreter's path and the SHA-256 of its own image,
; and the counts of statements executed, checks passed and records written. A claim in the log is thereby bound to
; the finite data it was decided on (the program text with its matrices) and to the exact procedure that decided it
; (this executable); a checker with the same bytes can re-run or re-derive every line. SHA-256 is integer
; arithmetic on 32-bit words: rotations, shifts, additions modulo 2^32 -- no floating point, like everything else.

section .data
sha_k: dd 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
       dd 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
       dd 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
       dd 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
       dd 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
       dd 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
       dd 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
       dd 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
sha_h0: dd 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
hexdigits: db '0123456789abcdef'
msg_cert_prog:   db 'certificate: program ', 0
msg_cert_interp: db 'certificate: interpreter ', 0
msg_cert_sha:    db '  sha256 ', 0
msg_cert_counts: db 'certificate: statements executed ', 0
msg_cert_checks: db ', checks passed ', 0
msg_cert_records: db ', records written ', 0
msg_cert_cost:   db 'certificate: rational operations ', 0
msg_cert_limbs:  db ', largest integer at most ', 0
msg_cert_bits:   db ' x 64 bits', 0
section .bss
sha_h:   resd 8
sha_s:   resd 8
sha_w:   resd 64
sha_dig: resb 32
stmts_run:     resq 1           ; statements executed (every non-empty line the run loop dispatched)
checks_passed: resq 1           ; check statements that passed
records_made:  resq 1           ; record statements written
qops:          resq 1           ; rational additions, subtractions, multiplications, divisions performed
bnmax:         resq 1           ; the largest integer allocated, in 64-bit limbs
section .text

; sha256(rcx = ptr, rdx = len) : the digest is left in sha_dig (32 bytes, big-endian words)
sha256:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    push rbp
    sub rsp, 16
    mov rsi, rcx
    mov r12, rdx                ; length
    lea rax, [r12+9+63]
    and rax, -64
    mov r13, rax                ; padded length
    mov rcx, rax
    call alloc                  ; fresh arena memory is zero
    mov rdi, rax
    xor ecx, ecx
.cp:
    cmp rcx, r12
    jge .pad
    mov al, [rsi+rcx]
    mov [rdi+rcx], al
    inc rcx
    jmp .cp
.pad:
    mov byte [rdi+r12], 0x80
    mov rax, r12
    shl rax, 3
    bswap rax
    mov [rdi+r13-8], rax        ; the bit length, big-endian, in the last 8 bytes
    lea rax, [sha_h0]
    lea rdx, [sha_h]
    xor ecx, ecx
.h0:
    cmp ecx, 8
    jge .chunks
    mov r8d, [rax+rcx*4]
    mov [rdx+rcx*4], r8d
    inc ecx
    jmp .h0
.chunks:
    xor r14d, r14d              ; chunk offset
.chunk:
    cmp r14, r13
    jge .final
    lea rbx, [sha_w]
    xor ecx, ecx
.w16:
    cmp ecx, 16
    jge .w64
    lea rdx, [rdi+r14]
    mov eax, [rdx+rcx*4]
    bswap eax
    mov [rbx+rcx*4], eax
    inc ecx
    jmp .w16
.w64:
    cmp ecx, 64
    jge .init_state
    mov eax, [rbx+rcx*4-8]      ; W[t-2]
    mov edx, eax
    ror edx, 17
    mov r8d, eax
    ror r8d, 19
    xor edx, r8d
    shr eax, 10
    xor edx, eax                ; sigma1
    mov eax, [rbx+rcx*4-60]     ; W[t-15]
    mov r8d, eax
    ror r8d, 7
    mov r9d, eax
    ror r9d, 18
    xor r8d, r9d
    shr eax, 3
    xor r8d, eax                ; sigma0
    add edx, r8d
    add edx, [rbx+rcx*4-28]     ; W[t-7]
    add edx, [rbx+rcx*4-64]     ; W[t-16]
    mov [rbx+rcx*4], edx
    inc ecx
    jmp .w64
.init_state:
    lea rax, [sha_h]
    lea rdx, [sha_s]
    xor ecx, ecx
.is:
    cmp ecx, 8
    jge .rounds
    mov r8d, [rax+rcx*4]
    mov [rdx+rcx*4], r8d
    inc ecx
    jmp .is
.rounds:
    mov qword [rsp], 0          ; t
    lea r15, [sha_s]            ; a b c d e f g h at r15 + 0 4 8 12 16 20 24 28
.round:
    mov rcx, [rsp]
    cmp rcx, 64
    jge .addstate
    mov esi, [r15+16]           ; e
    mov eax, esi
    ror eax, 6
    mov edx, esi
    ror edx, 11
    xor eax, edx
    mov edx, esi
    ror edx, 25
    xor eax, edx                ; Sigma1(e)
    mov edx, esi
    and edx, [r15+20]           ; e & f
    mov r8d, esi
    not r8d
    and r8d, [r15+24]           ; ~e & g
    xor edx, r8d                ; ch
    add eax, edx
    add eax, [r15+28]           ; + h
    lea rdx, [sha_k]
    add eax, [rdx+rcx*4]        ; + K[t]
    add eax, [rbx+rcx*4]        ; + W[t]  -> T1 in eax
    mov esi, [r15]              ; a
    mov edx, esi
    ror edx, 2
    mov r8d, esi
    ror r8d, 13
    xor edx, r8d
    mov r8d, esi
    ror r8d, 22
    xor edx, r8d                ; Sigma0(a)
    mov r8d, esi
    and r8d, [r15+4]            ; a & b
    mov r9d, esi
    and r9d, [r15+8]            ; a & c
    xor r8d, r9d
    mov r9d, [r15+4]
    and r9d, [r15+8]            ; b & c
    xor r8d, r9d                ; maj
    add edx, r8d                ; T2 in edx
    mov r8d, [r15+24]
    mov [r15+28], r8d           ; h = g
    mov r8d, [r15+20]
    mov [r15+24], r8d           ; g = f
    mov r8d, [r15+16]
    mov [r15+20], r8d           ; f = e
    mov r8d, [r15+12]
    add r8d, eax
    mov [r15+16], r8d           ; e = d + T1
    mov r8d, [r15+8]
    mov [r15+12], r8d           ; d = c
    mov r8d, [r15+4]
    mov [r15+8], r8d            ; c = b
    mov r8d, [r15]
    mov [r15+4], r8d            ; b = a
    add eax, edx
    mov [r15], eax              ; a = T1 + T2
    inc qword [rsp]
    jmp .round
.addstate:
    lea rax, [sha_h]
    xor ecx, ecx
.as:
    cmp ecx, 8
    jge .nextchunk
    mov r8d, [r15+rcx*4]
    add [rax+rcx*4], r8d
    inc ecx
    jmp .as
.nextchunk:
    add r14, 64
    jmp .chunk
.final:
    lea rax, [sha_h]
    lea rdx, [sha_dig]
    xor ecx, ecx
.dg:
    cmp ecx, 8
    jge .out
    mov r8d, [rax+rcx*4]
    bswap r8d
    mov [rdx+rcx*4], r8d
    inc ecx
    jmp .dg
.out:
    add rsp, 16
    pop rbp
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; emit_hex(rcx = ptr, rdx = len) : the bytes as lowercase hex
emit_hex:
    push rbx
    push rsi
    push r12
    mov rsi, rcx
    mov r12, rdx
    xor ebx, ebx
.h:
    cmp rbx, r12
    jge .done
    movzx eax, byte [rsi+rbx]
    mov ecx, eax
    shr ecx, 4
    lea rdx, [hexdigits]
    mov cl, [rdx+rcx]
    call emit_char
    movzx eax, byte [rsi+rbx]
    and eax, 15
    lea rdx, [hexdigits]
    mov cl, [rdx+rax]
    call emit_char
    inc rbx
    jmp .h
.done:
    pop r12
    pop rsi
    pop rbx
    ret


; cert_lines : append the certificate block; the caller has the emitter pointed at the log (proc_begin)
cert_lines:
    push rbx
    push rsi
    lea rcx, [msg_cert_prog]
    call emit_cstr
    mov rsi, [wpath]
    test rsi, rsi
    jnz .pp
    lea rsi, [wbuf]
.pp:
    call emit_wide
    lea rcx, [msg_cert_sha]
    call emit_cstr
    mov rcx, [srcptr]
    mov rdx, [srclen]
    call sha256
    lea rcx, [sha_dig]
    mov edx, 32
    call emit_hex
    call emit_nl
    lea rcx, [msg_cert_interp]
    call emit_cstr
    lea rsi, [wbuf]
    call emit_wide
    lea rcx, [msg_cert_sha]
    call emit_cstr
    mov rcx, [selfptr]
    mov rdx, [selflen]
    call sha256
    lea rcx, [sha_dig]
    mov edx, 32
    call emit_hex
    call emit_nl
    call cert_inputs
    call cert_io
    call cert_claims
    lea rcx, [msg_cert_counts]
    call emit_cstr
    mov rcx, [stmts_run]
    call emit_int
    lea rcx, [msg_cert_checks]
    call emit_cstr
    mov rcx, [checks_passed]
    call emit_int
    lea rcx, [msg_cert_records]
    call emit_cstr
    mov rcx, [records_made]
    call emit_int
    call emit_nl
    lea rcx, [msg_cert_cost]
    call emit_cstr
    mov rcx, [qops]
    call emit_int
    lea rcx, [msg_cert_limbs]
    call emit_cstr
    mov rcx, [bnmax]
    call emit_int
    lea rcx, [msg_cert_bits]
    call emit_cstr
    call emit_nl
    pop rsi
    pop rbx
    ret

; ============================================================ fifteenth/sixteenth cut: inputs bound into the certificate, claims by rule
; Every file a program reads (`load NAME PATH`, `load NAME arg`) is hashed as read and named in the certificate, and
; the command-line argument is recorded (paths and the argument written as UTF-8, losslessly). A claim is an explicit
; proposition. In its typed forms the interpreter checks, at `established`, that the evidence establishes it by the
; rule of that form -- `claim unsolvable A b` is established by `established y` only if y^T A = 0 and y^T b != 0,
; `claim injective A` only if nullity A = 0, and so on -- and a rule that fails stops the program. The free-text form
; `claim "..."` is an annotation: `established` closes it and the log says `closed`, never `established`; the
; certificate counts the two kinds apart. (The first version counted a closed annotation as established; the review
; showed `claim "1 = 2 over Q"` / `established` passing. It no longer means anything but "closed".)

section .data
msg_cert_input:  db 'certificate: input ', 0
msg_cert_arg:    db 'certificate: arg ', 0
msg_cert_argw:   db 'arg=', 0
msg_cert_claims: db 'certificate: claims established by rule ', 0
msg_cert_annot:  db '; annotations closed ', 0
msg_cert_of:     db ' of ', 0
msg_cert_open:   db 'certificate: claim not established: ', 0
msg_claim_open:  db 'claim: ', 0
msg_claim_rule:  db 'claim by rule ', 0
msg_established: db 'established by rule ', 0
msg_closed:      db 'closed (annotation, not a proof): ', 0
msg_est_checks:  db '  -- checks passed inside it: ', 0
msg_est_lines:   db ', lines ', 0
msg_witness:     db ' with witness ', 0
msg_noclaim: db 'established: no claim is open', 10
msg_noclaim_len equ $ - msg_noclaim
msg_deepclaim: db 'claim: too many open claims', 10
msg_deepclaim_len equ $ - msg_deepclaim
msg_notestab: db 'established: the evidence does not establish the claim by its rule', 10
msg_notestab_len equ $ - msg_notestab
msg_needwit: db 'established: this claim form needs a witness', 10
msg_needwit_len equ $ - msg_needwit
msg_toomanyin: db 'certificate: too many inputs to bind (the limit is 4096)', 10
msg_toomanyin_len equ $ - msg_toomanyin
; the claim forms: keyword, operand count, witness required
form_names: dq kw_zero, kw_equal, kw_injective, kw_surjective, kw_isomorphism, kw_noninjective, kw_nonsurjective, kw_solvable, kw_unsolvable, kw_exact, kw_boundary, kw_notboundary, kw_nonzero_c, 0
form_nops:  db 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1
form_wit:   db 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0
section .bss
MAXIN equ 4096
inputs_tok: resq MAXIN          ; token index of the path, or -1 for `arg`
inputs_dig: resb MAXIN*32
ninputs:    resq 1
load_tok:   resq 1
MAXCLAIM equ 16
claim_tok:  resq MAXCLAIM       ; the proposition's string token, or -1
claim_form: resq MAXCLAIM       ; 0 = annotation, else the form's number (1-based)
claim_a:    resq MAXCLAIM       ; first operand (a value)
claim_b:    resq MAXCLAIM       ; second operand, or 0
claim_chk:  resq MAXCLAIM       ; checks passed when the claim opened
claim_line: resq MAXCLAIM       ; line where it opened
nclaims:    resq 1              ; open claims
claims_made: resq 1             ; typed claims opened
claims_done: resq 1             ; typed claims established by their rule
annots_made: resq 1
annots_done: resq 1
section .text

; ---- UTF-8 <-> UTF-16, lossless, for paths and the argument
; emit_utf8(eax = code point) : as 1..4 bytes
emit_utf8:
    push rbx
    mov ebx, eax
    cmp ebx, 0x80
    jb .one
    cmp ebx, 0x800
    jb .two
    cmp ebx, 0x10000
    jb .three
    mov ecx, ebx
    shr ecx, 18
    or cl, 0xF0
    call emit_char
    mov ecx, ebx
    shr ecx, 12
    and cl, 0x3F
    or cl, 0x80
    call emit_char
    jmp .tail2
.three:
    mov ecx, ebx
    shr ecx, 12
    or cl, 0xE0
    call emit_char
.tail2:
    mov ecx, ebx
    shr ecx, 6
    and cl, 0x3F
    or cl, 0x80
    call emit_char
    jmp .last
.two:
    mov ecx, ebx
    shr ecx, 6
    or cl, 0xC0
    call emit_char
.last:
    mov ecx, ebx
    and cl, 0x3F
    or cl, 0x80
    call emit_char
    pop rbx
    ret
.one:
    mov ecx, ebx
    call emit_char
    pop rbx
    ret

; emit_wide(rsi = UTF-16 string, NUL-terminated) : as UTF-8, surrogate pairs combined
emit_wide:
    push rsi
.w:
    movzx eax, word [rsi]
    test eax, eax
    jz .done
    add rsi, 2
    cmp eax, 0xD800
    jb .emit
    cmp eax, 0xDC00
    jae .emit
    movzx edx, word [rsi]
    cmp edx, 0xDC00
    jb .emit
    cmp edx, 0xE000
    jae .emit
    add rsi, 2
    sub eax, 0xD800
    shl eax, 10
    sub edx, 0xDC00
    add eax, edx
    add eax, 0x10000
.emit:
    call emit_utf8
    jmp .w
.done:
    pop rsi
    ret

; utf8_to_wide(rcx = bytes, rdx = len, r8 = destination (words), r9 = capacity in words) -> rax = words written
; (no terminator written; the caller adds it)
utf8_to_wide:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    lea r12, [rcx+rdx]          ; end
    mov rdi, r8
    mov r13, r9
    xor ebx, ebx                ; words written
.l:
    cmp rsi, r12
    jge .done
    movzx eax, byte [rsi]
    inc rsi
    cmp eax, 0x80
    jb .put
    cmp eax, 0xE0
    jb .two
    cmp eax, 0xF0
    jb .three
    and eax, 0x07
    call .cont
    call .cont
    call .cont
    jmp .put
.three:
    and eax, 0x0F
    call .cont
    call .cont
    jmp .put
.two:
    and eax, 0x1F
    call .cont
.put:
    cmp eax, 0x10000
    jb .bmp
    sub eax, 0x10000
    mov edx, eax
    shr edx, 10
    add edx, 0xD800
    lea rcx, [rbx+2]
    cmp rcx, r13
    ja .done
    mov [rdi+rbx*2], dx
    inc rbx
    and eax, 0x3FF
    add eax, 0xDC00
.bmp:
    cmp rbx, r13
    jae .done
    mov [rdi+rbx*2], ax
    inc rbx
    jmp .l
.cont:                          ; shift in one continuation byte
    cmp rsi, r12
    jge .cret
    movzx edx, byte [rsi]
    inc rsi
    and edx, 0x3F
    shl eax, 6
    or eax, edx
.cret:
    ret
.done:
    mov rax, rbx
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; ---- inputs
; note_input(rcx = bytes, rdx = len, r8 = path token index or -1) : hash the input and remember it for the certificate
note_input:
    push rbx
    push r12
    mov rax, [ninputs]
    cmp rax, MAXIN
    jge .toomany
    mov r12, rax
    mov rbx, r8
    call sha256
    lea rax, [inputs_tok]
    mov [rax+r12*8], rbx
    lea rax, [inputs_dig]
    mov rcx, r12
    shl rcx, 5
    add rax, rcx
    lea rdx, [sha_dig]
    xor ecx, ecx
.cp:
    cmp ecx, 32
    jge .done
    mov r8b, [rdx+rcx]
    mov [rax+rcx], r8b
    inc ecx
    jmp .cp
.done:
    inc qword [ninputs]
    pop r12
    pop rbx
    ret
.toomany:
    lea rcx, [msg_toomanyin]
    mov edx, msg_toomanyin_len
    jmp fail

; cert_inputs : the argument and every input, with its hash (the emitter points at the log)
cert_inputs:
    push rbx
    push rsi
    push r12
    mov rsi, [orig_title]       ; the command line's argument (a chapter's is named by its line)
    test rsi, rsi
    jz .inputs
    lea rcx, [msg_cert_arg]
    call emit_cstr
    call emit_wide
    call emit_nl
.inputs:
    xor r12d, r12d
.l:
    cmp r12, [ninputs]
    jge .done
    lea rcx, [msg_cert_input]
    call emit_cstr
    lea rax, [inputs_tok]
    mov rcx, [rax+r12*8]
    cmp rcx, -1
    je .arg
    call tok_ptr
    mov rcx, [rax]
    mov rdx, [rax+8]
    call emit_str
    jmp .hash
.arg:
    lea rcx, [msg_cert_argw]
    call emit_cstr
    mov rsi, [orig_title]       ; the command line's argument (a chapter's is named by its line)
    call emit_wide
.hash:
    lea rcx, [msg_cert_sha]
    call emit_cstr
    lea rcx, [inputs_dig]
    mov rax, r12
    shl rax, 5
    add rcx, rax
    mov edx, 32
    call emit_hex
    call emit_nl
    inc r12
    jmp .l
.done:
    pop r12
    pop rsi
    pop rbx
    ret

; ---- claims
; claim "text"                       an annotation
; claim FORM A [B] ["text"]          a typed claim; FORM in zero equal injective surjective isomorphism noninjective
;                                    nonsurjective solvable unsolvable exact boundary notboundary
st_claim:
    push rbx
    push r12
    push r13
    push r14
    mov rax, [nclaims]
    cmp rax, MAXCLAIM
    jge .deep
    mov r12, rax                ; slot
    lea rax, [claim_form]
    mov qword [rax+r12*8], 0
    lea rax, [claim_a]
    mov qword [rax+r12*8], 0
    lea rax, [claim_b]
    mov qword [rax+r12*8], 0
    lea rax, [claim_tok]
    mov qword [rax+r12*8], -1
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    je .text
    ; a form keyword
    xor r13d, r13d              ; form index
.f:
    lea rax, [form_names]
    mov rdx, [rax+r13*8]
    test rdx, rdx
    jz .syntax
    mov rcx, [cur]
    call tok_is
    test eax, eax
    jnz .found
    inc r13
    jmp .f
.found:
    inc qword [cur]
    lea rax, [claim_form]
    lea rcx, [r13+1]
    mov [rax+r12*8], rcx
    call expect_word
    mov rcx, rax
    call value_at
    lea rcx, [claim_a]
    mov [rcx+r12*8], rax
    lea rax, [form_nops]
    cmp byte [rax+r13], 2
    jne .optext
    call expect_word
    mov rcx, rax
    call value_at
    lea rcx, [claim_b]
    mov [rcx+r12*8], rax
.optext:                        ; an optional annotation string
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    jne .open
.text:
    mov rax, [cur]
    lea rcx, [claim_tok]
    mov [rcx+r12*8], rax
    inc qword [cur]
.open:
    lea rax, [claim_chk]
    mov rdx, [checks_passed]
    mov [rax+r12*8], rdx
    lea rax, [claim_line]
    mov rdx, [lineno]
    mov [rax+r12*8], rdx
    inc qword [nclaims]
    lea rax, [claim_form]
    cmp qword [rax+r12*8], 0
    je .annot
    inc qword [claims_made]
    jmp .log
.annot:
    inc qword [annots_made]
.log:
    cmp qword [proch], 0
    je .out
    call proc_begin
    mov rcx, r12
    call claim_describe
    call emit_nl
    call proc_end
.out:
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.syntax:
    jmp syntax_error
.deep:
    lea rcx, [msg_deepclaim]
    mov edx, msg_deepclaim_len
    jmp fail

; claim_describe(rcx = slot) : "claim: <text>" or "claim by rule <form>[: <text>]"
claim_describe:
    push rbx
    push r12
    mov r12, rcx
    lea rax, [claim_form]
    mov rbx, [rax+r12*8]
    test rbx, rbx
    jz .plain
    lea rcx, [msg_claim_rule]
    call emit_cstr
    lea rax, [form_names]
    mov rcx, [rax+rbx*8-8]
    call emit_cstr
    lea rax, [claim_tok]
    cmp qword [rax+r12*8], -1
    je .done
    mov cl, ':'
    call emit_char
    mov cl, ' '
    call emit_char
    jmp .text
.plain:
    lea rcx, [msg_claim_open]
    call emit_cstr
.text:
    lea rax, [claim_tok]
    mov rcx, [rax+r12*8]
    cmp rcx, -1
    je .done
    call tok_ptr
    mov rcx, [rax]
    mov rdx, [rax+8]
    call emit_str
.done:
    pop r12
    pop rbx
    ret

; established [WITNESS] : close the innermost claim; a typed claim is checked by its rule first
st_established:
    push rbx
    push r12
    push r13
    push r14
    mov rax, [nclaims]
    test rax, rax
    jz .none
    dec rax
    mov r12, rax                ; slot (still open until the rule passes)
    xor r14d, r14d              ; witness
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 0
    jne .nowit
    call expect_word
    mov rcx, rax
    call value_at
    mov r14, rax
.nowit:
    lea rax, [claim_form]
    mov rbx, [rax+r12*8]
    test rbx, rbx
    jz .close
    lea rax, [form_wit]
    cmp byte [rax+rbx-1], 0
    je .rule
    test r14, r14
    jz .needwit
.rule:
    mov rcx, r12
    mov rdx, r14
    call claim_rule
    test eax, eax
    jz .notestab
.close:
    mov [nclaims], r12
    lea rax, [claim_chk]
    mov r13, [checks_passed]
    sub r13, [rax+r12*8]
    test rbx, rbx
    jz .annot
    inc qword [claims_done]
    jmp .log
.annot:
    inc qword [annots_done]
.log:
    cmp qword [proch], 0
    je .out
    call proc_begin
    test rbx, rbx
    jz .logannot
    lea rcx, [msg_established]
    call emit_cstr
    lea rax, [form_names]
    mov rcx, [rax+rbx*8-8]
    call emit_cstr
    test r14, r14
    jz .ltext
    lea rcx, [msg_witness]
    call emit_cstr
    mov rcx, r14
    call emit_value_plain_inline
    jmp .ltext
.logannot:
    lea rcx, [msg_closed]
    call emit_cstr
.ltext:
    lea rax, [claim_tok]
    mov rcx, [rax+r12*8]
    cmp rcx, -1
    je .lcounts
    mov cl, ' '
    call emit_char
    lea rax, [claim_tok]
    mov rcx, [rax+r12*8]
    call tok_ptr
    mov rcx, [rax]
    mov rdx, [rax+8]
    call emit_str
.lcounts:
    lea rcx, [msg_est_checks]
    call emit_cstr
    mov rcx, r13
    call emit_int
    lea rcx, [msg_est_lines]
    call emit_cstr
    lea rax, [claim_line]
    mov rcx, [rax+r12*8]
    call emit_int
    mov cl, '-'
    call emit_char
    mov rcx, [lineno]
    call emit_int
    call emit_nl
    call proc_end
.out:
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.none:
    lea rcx, [msg_noclaim]
    mov edx, msg_noclaim_len
    jmp fail
.needwit:
    lea rcx, [msg_needwit]
    mov edx, msg_needwit_len
    jmp fail
.notestab:
    lea rcx, [msg_notestab]
    mov edx, msg_notestab_len
    jmp fail

; emit_value_plain_inline(rcx = matrix) : a small matrix on one line for the log
emit_value_plain_inline:
    jmp emit_value_plain

; claim_rule(rcx = slot, rdx = witness or 0) -> eax = 1 when the evidence establishes the claim by its rule
claim_rule:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov r12, rcx
    mov r13, rdx
    lea rax, [claim_form]
    mov rbx, [rax+r12*8]
    lea rax, [claim_a]
    mov rsi, [rax+r12*8]
    lea rax, [claim_b]
    mov rdi, [rax+r12*8]
    cmp rbx, 1
    je .zero
    cmp rbx, 2
    je .equal
    cmp rbx, 3
    je .inj
    cmp rbx, 4
    je .sur
    cmp rbx, 5
    je .iso
    cmp rbx, 6
    je .noninj
    cmp rbx, 7
    je .nonsur
    cmp rbx, 8
    je .solv
    cmp rbx, 9
    je .unsolv
    cmp rbx, 10
    je .exact
    cmp rbx, 11
    je .solv
    cmp rbx, 13
    je .nonzero
    cmp rbx, 12
    je .unsolv
    xor eax, eax
    jmp .out
.zero:
    mov rcx, rsi
    call mat_is_zero
    jmp .out
.equal:
    mov rcx, rsi
    mov rdx, rdi
    mov r8, -1
    call mat_addsub
    mov rcx, rax
    call mat_is_zero
    jmp .out
.inj:
    mov rcx, rsi
    call mat_rank
    cmp rax, [rsi+8]
    jmp .flag
.sur:
    mov rcx, rsi
    call mat_rank
    cmp rax, [rsi]
    jmp .flag
.iso:
    mov rcx, rsi
    call mat_rank
    cmp rax, [rsi]
    jne .no
    cmp rax, [rsi+8]
    jmp .flag
.noninj:                        ; witness v != 0 with A v = 0
    mov rcx, r13
    call mat_is_zero
    test eax, eax
    jnz .no
    mov rcx, rsi
    mov rdx, r13
    call mat_mul
    mov rcx, rax
    call mat_is_zero
    jmp .out
.nonsur:                        ; witness y != 0 with y^T A = 0
    mov rcx, r13
    call mat_is_zero
    test eax, eax
    jnz .no
    mov rcx, r13
    call mat_transpose
    mov rcx, rax
    mov rdx, rsi
    call mat_mul
    mov rcx, rax
    call mat_is_zero
    jmp .out
.solv:                          ; witness x with A x = b
    mov rcx, rsi
    mov rdx, r13
    call mat_mul
    mov rcx, rax
    mov rdx, rdi
    mov r8, -1
    call mat_addsub
    mov rcx, rax
    call mat_is_zero
    jmp .out
.unsolv:                        ; witness y with y^T A = 0 and y^T b != 0
    mov rcx, r13
    call mat_transpose
    mov r13, rax
    mov rcx, rax
    mov rdx, rsi
    call mat_mul
    mov rcx, rax
    call mat_is_zero
    test eax, eax
    jz .no
    mov rcx, r13
    mov rdx, rdi
    call mat_mul
    mov rcx, rax
    call mat_is_zero
    test eax, eax
    jnz .no
    mov eax, 1
    jmp .out
.nonzero:
    mov rcx, rsi
    call mat_is_zero
    xor eax, 1
    jmp .out
.exact:
    mov rcx, rsi
    mov rdx, rdi
    call mat_exact
    jmp .out
.flag:
    jne .no
    mov eax, 1
    jmp .out
.no:
    xor eax, eax
.out:
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; cert_claims : the claims summary and every claim still open (the emitter points at the log)
cert_claims:
    push rbx
    push r12
    xor r12d, r12d
.l:
    cmp r12, [nclaims]
    jge .summary
    lea rcx, [msg_cert_open]
    call emit_cstr
    mov rcx, r12
    call claim_describe
    call emit_nl
    inc r12
    jmp .l
.summary:
    lea rcx, [msg_cert_claims]
    call emit_cstr
    mov rcx, [claims_done]
    call emit_int
    lea rcx, [msg_cert_of]
    call emit_cstr
    mov rcx, [claims_made]
    call emit_int
    lea rcx, [msg_cert_annot]
    call emit_cstr
    mov rcx, [annots_done]
    call emit_int
    lea rcx, [msg_cert_of]
    call emit_cstr
    mov rcx, [annots_made]
    call emit_int
    call emit_nl
    pop r12
    pop rbx
    ret
; ============================================================ twentieth cut: the minimal polynomial as a primitive
; minpoly A     the monic minimal polynomial of a square A, highest first (Krylov on vec(A^k): the first k with vec(A^k)
;               in the span of vec(I), .., vec(A^(k-1)) gives A^k = sum c_j A^j, mu = x^k - sum c_j x^j; k <= n)
; companion p   the companion matrix of p / lead(p): the shift with -(lower coefficients) as the last column
; polygcd p q   the monic greatest common divisor (Euclid with polyrem; gcd(0, 0) = 0)
; polyderiv p   the derivative
section .data
msg_deg0:      db 'companion: the polynomial has degree 0', 10
msg_deg0_len   equ $ - msg_deg0
msg_nodep:     db 'minpoly: no dependency among the powers (impossible by Cayley-Hamilton)', 10
msg_nodep_len  equ $ - msg_nodep
section .text

; mat_minpoly(rcx = A, n x n) -> rax = mu as a column of deg + 1 entries
mat_minpoly:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 48
    mov rbx, rcx
    mov r12, [rbx]
    cmp r12, [rbx+8]
    jne .notsq
    mov rcx, r12
    call mat_identity
    mov r13, rax                ; Pk = A^(k-1)
    mov rcx, rax
    call mat_vec
    mov r14, rax                ; K = [vec(I) .. vec(A^(k-1))]
    mov r15, 1                  ; k
.loop:
    mov rcx, rbx
    mov rdx, r13
    call mat_mul
    mov r13, rax                ; A^k
    mov rcx, rax
    call mat_vec
    mov rsi, rax                ; v_k
    mov rcx, r14
    mov rdx, rsi
    call mat_solve
    test rax, rax
    jnz .found
    mov rcx, r14
    mov rdx, rsi
    call mat_augment
    mov r14, rax
    inc r15
    cmp r15, r12
    jle .loop
    lea rcx, [msg_nodep]
    mov edx, msg_nodep_len
    jmp fail
.found:
    mov rdi, rax                ; c_0 .. c_(k-1)
    lea rcx, [r15+1]
    mov rdx, 1
    call mat_new
    mov rsi, rax
    mov rdx, [q_one]
    mov [rsi+16], rdx           ; the leading 1
    mov qword [rsp+32], 0       ; j
.fill:
    mov rax, [rsp+32]
    cmp rax, r15
    jge .done
    mov rcx, [rdi+16+rax*8]     ; c_j
    call q_neg
    mov rdx, [rsp+32]
    mov rcx, r15
    sub rcx, rdx                ; row k - j holds the coefficient of x^j
    mov [rsi+16+rcx*8], rax
    inc qword [rsp+32]
    jmp .fill
.done:
    mov rax, rsi
    add rsp, 48
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.notsq:
    lea rcx, [msg_notsq]
    mov edx, msg_notsq_len
    jmp fail

; mat_companion(rcx = p, a column highest first) -> rax = the k x k companion matrix of p / lead, k = deg p
mat_companion:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 48
    call poly_trim
    mov rbx, rax
    mov r12, [rbx]
    dec r12                     ; k
    cmp r12, 1
    jl .deg0
    mov rcx, r12
    mov rdx, r12
    call mat_new
    mov rsi, rax
    mov rcx, 1                  ; the subdiagonal: cell (i, i - 1) = 1, i = 1 .. k-1
.sub:
    cmp rcx, r12
    jge .last
    mov rax, rcx
    imul rax, r12
    add rax, rcx
    dec rax
    mov rdx, [q_one]
    mov [rsi+16+rax*8], rdx
    inc rcx
    jmp .sub
.last:
    xor r13d, r13d              ; row j of the last column = -p[k - j] / p[0]
.lc:
    cmp r13, r12
    jge .done
    mov rax, r12
    sub rax, r13
    mov rcx, [rbx+16+rax*8]
    mov rdx, [rbx+16]
    call q_div
    mov rcx, rax
    call q_neg
    mov rcx, r13
    imul rcx, r12
    add rcx, r12
    dec rcx
    mov [rsi+16+rcx*8], rax
    inc r13
    jmp .lc
.done:
    mov rax, rsi
    add rsp, 48
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.deg0:
    lea rcx, [msg_deg0]
    mov edx, msg_deg0_len
    jmp fail

; poly_is_zero(rcx = p, trimmed) -> eax 1 when p = [0]
poly_is_zero:
    cmp qword [rcx], 1
    jne .no
    mov rcx, [rcx+16]
    jmp q_is_zero
.no:
    xor eax, eax
    ret

; poly_gcd(rcx = p, rdx = q) -> rax = the monic gcd (Euclid), [0] when both are 0
poly_gcd:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 48
    mov rsi, rdx
    call poly_trim
    mov rbx, rax                ; a
    mov rcx, rsi
    call poly_trim
    mov rsi, rax                ; b
.loop:
    mov rcx, rsi
    call poly_is_zero
    test eax, eax
    jnz .norm
    mov rcx, rbx
    mov rdx, rsi
    call mat_polydivmod         ; rdx = a mod b
    mov rbx, rsi
    mov rsi, rdx
    jmp .loop
.norm:
    mov rcx, rbx
    call poly_is_zero
    test eax, eax
    jnz .zero
    mov rcx, [q_one]
    mov rdx, [rbx+16]
    call q_div                  ; 1 / lead
    mov rcx, rax
    mov rdx, rbx
    call mat_scale
    jmp .done
.zero:
    mov rax, rbx
.done:
    add rsp, 48
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; poly_deriv(rcx = p) -> rax = p' (highest first; the derivative of a constant is [0])
poly_deriv:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 48
    call poly_trim
    mov rbx, rax
    mov r12, [rbx]
    dec r12                     ; d = degree
    jg .some
    mov rcx, 1
    mov rdx, 1
    call mat_new
    jmp .done
.some:
    mov rcx, r12
    mov rdx, 1
    call mat_new
    mov rsi, rax
    xor r13d, r13d              ; i = 0 .. d-1 : r[i] = (d - i) p[i]
.fill:
    cmp r13, r12
    jge .fin
    mov rcx, r12
    sub rcx, r13
    call q_from_i64
    mov rdx, rax
    mov rcx, [rbx+16+r13*8]
    call q_mul
    mov [rsi+16+r13*8], rax
    inc r13
    jmp .fill
.fin:
    mov rax, rsi
.done:
    add rsp, 48
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
; ============================================================ twenty-first cut: bytes, files and the network
; text NAME "literal"                  NAME := address of the UTF-8 bytes (zero-terminated); NAME_len := the length.
;                                      In `text` and `net` literals: \q is a double quote, \n \r \t \\ as usual.
; text NAME join A B ...               concatenation of literals and words (a word is an address of zero-terminated bytes)
; text NAME escape A / unescape A      JSON string escaping; unescaping reads from A to the closing unescaped quote
; text NAME upto A "delim"             the bytes of A before the first occurrence of the delimiter
; text NAME find HAY NDL / after       the address of the first occurrence (0 when none) / the address just past it
; text NAME base64 A                   the bytes decoded from base64 at A (stops at the first non-alphabet byte)
; text NAME compare A B                0 when the byte strings are equal, 1 when they differ
; text NAME count HAY NDL              the number of non-overlapping occurrences
; text NAME int W / num A              the decimal digits of a word / the integer read at A
; read NAME PATH                       the bytes of a file (zero-terminated), NAME_len; hashed into the certificate as an input
; write PATH ADDR LEN                  LEN bytes at ADDR to the file; hashed into the certificate as an output
; net http NAME HOST PORT METHOD PATH  an HTTP/1.1 request to a dotted IP; NAME := the body (zero-terminated), NAME_len
; net probe NAME HOST PORT             NAME := 1 when a TCP connection can be made, else 0
; net ws NAME HOST PORT PATH           a WebSocket (RFC 6455) client connection; NAME := its handle
; net send WS TEXT / net recv NAME WS  a text message out / the next text message in (NAME := 0 when the peer closed)
; net cdp NAME WS ID METHOD PARAMS     Chrome DevTools Protocol: {"id":ID,"method":METHOD,"params":PARAMS}, NAME := the reply with that id
; net close WS
section .data
kw_text:       db 'text', 0
kw_read:       db 'read', 0
kw_write:      db 'write', 0
kw_net:        db 'net', 0
kw_join:       db 'join', 0
kw_escape:     db 'escape', 0
kw_unescape:   db 'unescape', 0
kw_upto:       db 'upto', 0
kw_find:       db 'find', 0
kw_after:      db 'after', 0
kw_base64:     db 'base64', 0
kw_compare:    db 'compare', 0
kw_count:      db 'count', 0
kw_int:        db 'int', 0
kw_num:        db 'num', 0
kw_http:       db 'http', 0
kw_probe:      db 'probe', 0
kw_ws:         db 'ws', 0
kw_send:       db 'send', 0
kw_recv:       db 'recv', 0
kw_cdp:        db 'cdp', 0
kw_close:      db 'close', 0
ws2name:       db 'ws2_32.dll', 0
n_WSAStartup:  db 'WSAStartup', 0
n_socket:      db 'socket', 0
n_connect:     db 'connect', 0
n_send:        db 'send', 0
n_recv:        db 'recv', 0
n_closesocket: db 'closesocket', 0
n_htons:       db 'htons', 0
n_inet_addr:   db 'inet_addr', 0
s_space:       db ' ', 0
s_http_host:   db ' HTTP/1.1', 13, 10, 'Host: ', 0
s_http_tail:   db 13, 10, 'Connection: close', 13, 10, 13, 10, 0
s_ws_get:      db 'GET ', 0
s_ws_tail:     db 13, 10, 'Upgrade: websocket', 13, 10, 'Connection: Upgrade', 13, 10, 'Sec-WebSocket-Version: 13', 13, 10, 'Sec-WebSocket-Key: AAAAAAAAAAAAAAAAAAAAAA==', 13, 10, 13, 10, 0
s_clen:        db 'Content-Length:', 0
s_cdp1:        db '{"id":', 0
s_cdp2:        db ',"method":"', 0
s_cdp3:        db '","params":', 0
s_cdp4:        db '}', 0
s_comma:       db ',', 0
s_empty_obj:   db '{}', 0
s_ulen:        db '_len', 0
msg_netinit:   db 'network: ws2_32 could not be loaded', 10
msg_netinit_len equ $ - msg_netinit
msg_netconn:   db 'network: the connection was refused', 10
msg_netconn_len equ $ - msg_netconn
msg_netio:     db 'network: send or receive failed', 10
msg_netio_len  equ $ - msg_netio
msg_nethdr:    db 'network: the peer closed before the headers were complete', 10
msg_nethdr_len equ $ - msg_nethdr
msg_wsref:     db 'websocket: the upgrade was refused', 10
msg_wsref_len  equ $ - msg_wsref
msg_wsclosed:  db 'websocket: closed by the peer while a reply was awaited', 10
msg_wsclosed_len equ $ - msg_wsclosed
msg_toolong:   db 'network: a message exceeds 256 MB', 10
msg_toolong_len equ $ - msg_toolong
msg_noread:    db 'read: the file cannot be opened', 10
msg_noread_len equ $ - msg_noread
msg_nowr:      db 'write: the file cannot be written', 10
msg_nowr_len   equ $ - msg_nowr
msg_ioful:     db 'certificate: too many files (the limit is 4096)', 10
msg_ioful_len  equ $ - msg_ioful
msg_ionames:   db 'certificate: the names of the files read and written exceed 1048576 bytes', 10
msg_ionames_len equ $ - msg_ionames
msg_cert_in:   db 'certificate: input ', 0
msg_cert_out:  db 'certificate: output ', 0
msg_nulladdr:  db 'text: the word holds address 0 (nothing was found)', 10
msg_nulladdr_len equ $ - msg_nulladdr
section .bss
p_WSAStartup:  resq 1
p_socket:      resq 1
p_connect:     resq 1
p_send:        resq 1
p_recv:        resq 1
p_closesocket: resq 1
p_htons:       resq 1
p_inet_addr:   resq 1
net_ready:     resq 1
wsadata:       resb 512
MAXIO equ 4096
IONAMES equ MAXIO*256
io_path:       resq MAXIO       ; each points into io_names: a chapter releases the arena, the certificate comes after
io_kind:       resq MAXIO
io_dig:        resb MAXIO*32
nio:           resq 1
io_names:      resb IONAMES     ; every distinct path once, zero-terminated
io_names_used: resq 1
section .text

%macro NPRO 0
    push rbp
    mov rbp, rsp
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 72
%endmacro
%macro NEPI 0
    lea rsp, [rbp-56]
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    pop rbp
    ret
%endmacro
%macro NFAIL 1
    lea rcx, [%1]
    mov edx, %1_len
    jmp fail
%endmacro

; ---------------------------------------------------------------- bytes
zlen:                           ; rcx = cstr -> rax = length
    xor eax, eax
.l:
    cmp byte [rcx+rax], 0
    je .d
    inc rax
    jmp .l
.d:
    ret

memcpy_:                        ; rcx = dst, rdx = src, r8 = n
    push rsi
    push rdi
    mov rdi, rcx
    mov rsi, rdx
    mov rcx, r8
    rep movsb
    pop rdi
    pop rsi
    ret

append:                         ; rcx = dst end, rdx = src cstr -> rax = the new end
    push rsi
    push rdi
    mov rdi, rcx
    mov rsi, rdx
.l:
    mov al, [rsi]
    mov [rdi], al
    test al, al
    jz .d
    inc rsi
    inc rdi
    jmp .l
.d:
    mov rax, rdi
    pop rdi
    pop rsi
    ret

memfind:                        ; rcx = hay, rdx = haylen, r8 = needle cstr -> rax = ptr or 0
    push rbx
    push rsi
    push rdi
    push r12
    mov rsi, rcx
    mov rdi, rdx
    mov r12, r8
    mov rcx, r8
    call zlen
    mov rbx, rax                ; needle length
    cmp rdi, rbx
    jl .none
    sub rdi, rbx                ; last start
    xor ecx, ecx
.outer:
    cmp rcx, rdi
    jg .none
    xor edx, edx
.inner:
    cmp rdx, rbx
    jge .hit
    lea rax, [rsi+rcx]
    mov al, [rax+rdx]
    cmp al, [r12+rdx]
    jne .next
    inc rdx
    jmp .inner
.hit:
    lea rax, [rsi+rcx]
    jmp .out
.next:
    inc rcx
    jmp .outer
.none:
    xor eax, eax
.out:
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

find_z:                         ; rcx = hay cstr, rdx = needle cstr -> rax = ptr or 0
    push rbx
    mov rbx, rdx
    call zlen
    mov rdx, rax
    mov r8, rbx
    call memfind
    pop rbx
    ret

atoi_z:                         ; rcx = cstr -> rax (spaces skipped, optional -)
    push rbx
    xor eax, eax
    xor ebx, ebx
.sp:
    cmp byte [rcx], ' '
    jne .sign
    inc rcx
    jmp .sp
.sign:
    cmp byte [rcx], '-'
    jne .dig
    mov ebx, 1
    inc rcx
.dig:
    movzx edx, byte [rcx]
    sub edx, '0'
    cmp edx, 9
    ja .d
    imul rax, 10
    add rax, rdx
    inc rcx
    jmp .dig
.d:
    test ebx, ebx
    jz .out
    neg rax
.out:
    pop rbx
    ret

int_to_str:                     ; rcx = value -> rax = cstr, rdx = len
    push rbx
    push rsi
    mov rbx, rcx
    mov rcx, 24
    call alloc
    mov rsi, rax
    mov rax, rbx
    lea rcx, [rsi+22]
    mov byte [rcx], 0
    mov rbx, rax
    test rax, rax
    jns .pos
    neg rax
.pos:
    mov r8, 10
.l:
    xor edx, edx
    div r8
    add dl, '0'
    dec rcx
    mov [rcx], dl
    test rax, rax
    jnz .l
    test rbx, rbx
    jns .nosign
    dec rcx
    mov byte [rcx], '-'
.nosign:
    lea rdx, [rsi+22]
    sub rdx, rcx
    mov rax, rcx
    pop rsi
    pop rbx
    ret

; lit_or_word(rcx = token index) -> rax = zero-terminated bytes, rdx = length
lit_or_word:
    NPRO
    mov rbx, rcx
    call tok_ptr
    cmp qword [rax+16], 4
    jne .word
    mov rsi, [rax]
    mov r12, [rax+8]
    lea rcx, [r12+1]
    call alloc
    mov rdi, rax
    xor r13d, r13d
    xor r14d, r14d
.cp:
    cmp r13, r12
    jge .cpd
    movzx eax, byte [rsi+r13]
    inc r13
    cmp al, '\'
    jne .put
    cmp r13, r12
    jge .put
    movzx ecx, byte [rsi+r13]
    cmp cl, 'q'
    jne .e1
    mov al, '"'
    jmp .esc
.e1:
    cmp cl, 'n'
    jne .e2
    mov al, 10
    jmp .esc
.e2:
    cmp cl, 'r'
    jne .e3
    mov al, 13
    jmp .esc
.e3:
    cmp cl, 't'
    jne .e4
    mov al, 9
    jmp .esc
.e4:
    cmp cl, '\'
    jne .put
.esc:
    inc r13
.put:
    mov [rdi+r14], al
    inc r14
    jmp .cp
.cpd:
    mov byte [rdi+r14], 0
    mov rax, rdi
    mov rdx, r14
    NEPI
.word:
    mov rcx, rbx
    call sym_find
    test rax, rax
    jz unknown_error
    cmp qword [rax+16], 3
    jne unknown_error
    mov r12, [rax+24]
    test r12, r12
    jz .null
    mov rcx, rbx
    mov rdx, r12
    call word_len
    mov rdx, rax
    mov rax, r12
    NEPI
.null:
    NFAIL msg_nulladdr

; next_arg -> rax = bytes, rdx = len : the next token as a literal or word, consumed
next_arg:
    mov rcx, [cur]
    inc qword [cur]
    jmp lit_or_word

; next_int -> rax : the next token as a machine word (literal integer, word or 1x1 integer value), consumed
next_int:
    mov rcx, [cur]
    inc qword [cur]
    jmp operand

; at_eol -> eax 1 when the current token is a newline or the end
at_eol:
    mov rcx, [cur]
    cmp rcx, [ntok]
    jge .yes
    call tok_ptr
    cmp qword [rax+16], 3
    je .yes
    xor eax, eax
    ret
.yes:
    mov eax, 1
    ret

; sym_set_bytes(rcx = name ptr, rdx = name len, r8 = kind, r9 = payload)
sym_set_bytes:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    mov rdi, rdx
    mov r12, r8
    mov r13, r9
    lea rbx, [symbols]
    xor ecx, ecx
.loop:
    cmp rcx, [nsym]
    jge .new
    cmp [rbx+8], rdi
    jne .next
    xor edx, edx
.cmp:
    cmp rdx, rdi
    jge .hit
    mov r8, [rbx]
    mov al, [rsi+rdx]
    cmp al, [r8+rdx]
    jne .next
    inc rdx
    jmp .cmp
.hit:
    mov rax, rbx
    jmp .store
.next:
    add rbx, 32
    inc rcx
    jmp .loop
.new:
    mov rax, [nsym]
    cmp rax, MAXSYM
    jge sym_full
    imul rax, 32
    lea rdx, [symbols]
    add rax, rdx
    inc qword [nsym]
    mov [rax], rsi
    mov [rax+8], rdi
.store:
    mov [rax+16], r12
    mov [rax+24], r13
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; set_word_pair(rcx = name token, rdx = address, r8 = length): NAME := address, NAME_len := length
set_word_pair:
    NPRO
    mov rbx, rcx
    mov r12, rdx
    mov r13, r8
    mov edx, 3
    mov r8, r12
    call sym_set
    mov rcx, rbx
    call tok_ptr
    mov rsi, [rax]
    mov rdi, [rax+8]
    lea rcx, [rdi+5]
    call alloc
    mov r14, rax
    mov rcx, rax
    mov rdx, rsi
    mov r8, rdi
    call memcpy_
    lea rcx, [r14+rdi]
    lea rdx, [s_ulen]
    call append
    mov rcx, r14
    lea rdx, [rdi+4]
    mov r8d, 3
    mov r9, r13
    call sym_set_bytes
    NEPI

; ---------------------------------------------------------------- JSON strings, base64
json_escape:                    ; rcx = src, rdx = len -> rax = dst (zero-terminated), rdx = len
    NPRO
    mov rsi, rcx
    mov r12, rdx
    lea rcx, [rdx*8+8]
    call alloc
    mov rdi, rax
    xor r13d, r13d
    xor r14d, r14d
.l:
    cmp r13, r12
    jge .d
    movzx eax, byte [rsi+r13]
    inc r13
    cmp al, '"'
    je .bs
    cmp al, '\'
    je .bs
    cmp al, 10
    je .n
    cmp al, 13
    je .r
    cmp al, 9
    je .t
    cmp al, 0x20
    jb .u
    mov [rdi+r14], al
    inc r14
    jmp .l
.bs:
    mov byte [rdi+r14], '\'
    mov [rdi+r14+1], al
    add r14, 2
    jmp .l
.n:
    mov al, 'n'
    jmp .two
.r:
    mov al, 'r'
    jmp .two
.t:
    mov al, 't'
.two:
    mov byte [rdi+r14], '\'
    mov [rdi+r14+1], al
    add r14, 2
    jmp .l
.u:
    mov dword [rdi+r14], '\u00'
    mov ecx, eax
    shr ecx, 4
    add cl, '0'
    mov [rdi+r14+4], cl
    and eax, 15
    cmp eax, 10
    jb .dg
    add eax, 'a' - 10 - '0'
.dg:
    add al, '0'
    mov [rdi+r14+5], al
    add r14, 6
    jmp .l
.d:
    mov byte [rdi+r14], 0
    mov rax, rdi
    mov rdx, r14
    NEPI

hexval:                         ; al = hex digit -> eax value (0 when not hex)
    cmp al, '9'
    ja .let
    sub al, '0'
    movzx eax, al
    ret
.let:
    or al, 0x20
    sub al, 'a' - 10
    movzx eax, al
    cmp eax, 15
    jbe .ok
    xor eax, eax
.ok:
    ret

put_utf8:                       ; rdi = dst, r14 = index, eax = code point -> r14 advanced
    cmp eax, 0x80
    jb .one
    cmp eax, 0x800
    jb .two
    cmp eax, 0x10000
    jb .three
    mov ecx, eax
    shr ecx, 18
    or cl, 0xF0
    mov [rdi+r14], cl
    mov ecx, eax
    shr ecx, 12
    and cl, 0x3F
    or cl, 0x80
    mov [rdi+r14+1], cl
    mov ecx, eax
    shr ecx, 6
    and cl, 0x3F
    or cl, 0x80
    mov [rdi+r14+2], cl
    and al, 0x3F
    or al, 0x80
    mov [rdi+r14+3], al
    add r14, 4
    ret
.three:
    mov ecx, eax
    shr ecx, 12
    or cl, 0xE0
    mov [rdi+r14], cl
    mov ecx, eax
    shr ecx, 6
    and cl, 0x3F
    or cl, 0x80
    mov [rdi+r14+1], cl
    and al, 0x3F
    or al, 0x80
    mov [rdi+r14+2], al
    add r14, 3
    ret
.two:
    mov ecx, eax
    shr ecx, 6
    or cl, 0xC0
    mov [rdi+r14], cl
    and al, 0x3F
    or al, 0x80
    mov [rdi+r14+1], al
    add r14, 2
    ret
.one:
    mov [rdi+r14], al
    inc r14
    ret

read_u4:                        ; rsi = src, r13 = index at the 4 hex digits -> eax = code, r13 advanced by 4
    xor r8d, r8d
    xor ecx, ecx
.l:
    cmp ecx, 4
    jge .d
    movzx eax, byte [rsi+r13]
    test al, al
    jz .d
    push rcx
    call hexval
    pop rcx
    shl r8d, 4
    or r8d, eax
    inc r13
    inc ecx
    jmp .l
.d:
    mov eax, r8d
    ret

json_unescape:                  ; rcx = src (after the opening quote) -> rax = dst (zero-terminated), rdx = len
    NPRO
    mov rsi, rcx
    call zlen
    lea rcx, [rax+4]
    call alloc
    mov rdi, rax
    xor r13d, r13d
    xor r14d, r14d
.l:
    movzx eax, byte [rsi+r13]
    test al, al
    jz .d
    cmp al, '"'
    je .d
    inc r13
    cmp al, '\'
    jne .put
    movzx eax, byte [rsi+r13]
    test al, al
    jz .d
    inc r13
    cmp al, 'n'
    je .n
    cmp al, 'r'
    je .r
    cmp al, 't'
    je .t
    cmp al, 'b'
    je .b
    cmp al, 'f'
    je .f
    cmp al, 'u'
    je .u
    jmp .put                    ; \" \\ \/ and anything else: the character itself
.n:
    mov al, 10
    jmp .put
.r:
    mov al, 13
    jmp .put
.t:
    mov al, 9
    jmp .put
.b:
    mov al, 8
    jmp .put
.f:
    mov al, 12
    jmp .put
.u:
    call read_u4
    mov r15d, eax
    cmp eax, 0xD800
    jb .cp
    cmp eax, 0xDBFF
    ja .cp
    cmp byte [rsi+r13], '\'
    jne .cp
    cmp byte [rsi+r13+1], 'u'
    jne .cp
    add r13, 2
    call read_u4
    sub r15d, 0xD800
    shl r15d, 10
    sub eax, 0xDC00
    add r15d, eax
    add r15d, 0x10000
.cp:
    mov eax, r15d
    call put_utf8
    jmp .l
.put:
    mov [rdi+r14], al
    inc r14
    jmp .l
.d:
    mov byte [rdi+r14], 0
    mov rax, rdi
    mov rdx, r14
    NEPI

b64val:                         ; al -> eax value, or -1 when outside the alphabet
    cmp al, 'A'
    jb .n1
    cmp al, 'Z'
    ja .n1
    sub al, 'A'
    movzx eax, al
    ret
.n1:
    cmp al, 'a'
    jb .n2
    cmp al, 'z'
    ja .n2
    sub al, 'a' - 26
    movzx eax, al
    ret
.n2:
    cmp al, '0'
    jb .n3
    cmp al, '9'
    ja .n3
    sub al, '0' - 52
    movzx eax, al
    ret
.n3:
    cmp al, '+'
    je .plus
    cmp al, '-'
    je .plus
    cmp al, '/'
    je .slash
    cmp al, '_'
    je .slash
    mov eax, -1
    ret
.plus:
    mov eax, 62
    ret
.slash:
    mov eax, 63
    ret

b64_decode:                     ; rcx = src -> rax = bytes, rdx = len
    NPRO
    mov rsi, rcx
    call zlen
    mov rcx, rax
    call alloc
    mov rdi, rax
    xor r13d, r13d              ; in
    xor r14d, r14d              ; out
    xor r12d, r12d              ; accumulator
    xor r15d, r15d              ; bits
.l:
    movzx eax, byte [rsi+r13]
    test al, al
    jz .d
    inc r13
    cmp al, '='
    je .d
    call b64val
    cmp eax, -1
    je .d
    shl r12d, 6
    or r12d, eax
    add r15d, 6
    cmp r15d, 8
    jb .l
    sub r15d, 8
    mov eax, r12d
    mov ecx, r15d
    shr eax, cl
    mov [rdi+r14], al
    inc r14
    mov eax, 1
    mov ecx, r15d
    shl eax, cl
    dec eax
    and r12d, eax
    jmp .l
.d:
    mov rax, rdi
    mov rdx, r14
    NEPI

; ---------------------------------------------------------------- the network
%macro RESOLVE 2
    mov rcx, rbx
    lea rdx, [%1]
    call GetProcAddress
    test rax, rax
    jz .fail
    mov [%2], rax
%endmacro

net_init:
    NPRO
    cmp qword [net_ready], 0
    jne .done
    lea rcx, [ws2name]
    call LoadLibraryA
    test rax, rax
    jz .fail
    mov rbx, rax
    RESOLVE n_WSAStartup, p_WSAStartup
    RESOLVE n_socket, p_socket
    RESOLVE n_connect, p_connect
    RESOLVE n_send, p_send
    RESOLVE n_recv, p_recv
    RESOLVE n_closesocket, p_closesocket
    RESOLVE n_htons, p_htons
    RESOLVE n_inet_addr, p_inet_addr
    mov ecx, 0x202
    lea rdx, [wsadata]
    call [p_WSAStartup]
    test eax, eax
    jnz .fail
    mov qword [net_ready], 1
.done:
    NEPI
.fail:
    NFAIL msg_netinit

; tcp_connect(rcx = host cstr (dotted), rdx = port, r8 = 1 soft) -> rax = socket, or -1 when soft and refused
tcp_connect:
    NPRO
    mov rbx, rcx
    mov r12, rdx
    mov r15, r8
    call net_init
    mov ecx, 2
    mov edx, 1
    mov r8d, 6
    call [p_socket]
    cmp rax, -1
    je .fail
    mov r13, rax
    mov word [rsp+32], 2
    mov rcx, r12
    call [p_htons]
    mov [rsp+34], ax
    mov rcx, rbx
    call [p_inet_addr]
    mov [rsp+36], eax
    mov qword [rsp+40], 0
    mov rcx, r13
    lea rdx, [rsp+32]
    mov r8d, 16
    call [p_connect]
    test eax, eax
    jnz .refused
    mov rax, r13
    NEPI
.refused:
    mov rcx, r13
    call [p_closesocket]
.fail:
    test r15, r15
    jz .hard
    mov rax, -1
    NEPI
.hard:
    NFAIL msg_netconn

tcp_send_all:                   ; rcx = socket, rdx = ptr, r8 = len
    NPRO
    mov rbx, rcx
    mov rsi, rdx
    mov r12, r8
.l:
    test r12, r12
    jle .d
    mov rcx, rbx
    mov rdx, rsi
    mov r8, r12
    cmp r8, 1048576
    jle .ok
    mov r8, 1048576
.ok:
    xor r9d, r9d
    call [p_send]
    movsxd rax, eax
    test rax, rax
    jle .fail
    add rsi, rax
    sub r12, rax
    jmp .l
.d:
    NEPI
.fail:
    NFAIL msg_netio

tcp_recv:                       ; rcx = socket, rdx = ptr, r8 = max -> rax = n (0 when closed)
    NPRO
    cmp r8, 1048576
    jle .ok
    mov r8, 1048576
.ok:
    xor r9d, r9d
    call [p_recv]
    movsxd rax, eax
    js .fail
    NEPI
.fail:
    NFAIL msg_netio

find_hdr_end:                   ; rcx = buf, rdx = n -> rax = offset after CRLFCRLF, or -1
    xor eax, eax
.l:
    lea r8, [rax+4]
    cmp r8, rdx
    jg .none
    cmp dword [rcx+rax], 0x0A0D0A0D
    je .hit
    inc rax
    jmp .l
.hit:
    add rax, 4
    ret
.none:
    mov rax, -1
    ret

; http_request(rcx = host, rdx = port, r8 = method, r9 = path) -> rax = body (zero-terminated), rdx = len, r8 = status
http_request:
    NPRO
    mov rbx, rcx
    mov r12, rdx
    mov r13, r8
    mov r14, r9
    mov rcx, 8192
    call alloc
    mov rdi, rax
    mov rcx, rdi
    mov rdx, r13
    call append
    mov rcx, rax
    lea rdx, [s_space]
    call append
    mov rcx, rax
    mov rdx, r14
    call append
    mov rcx, rax
    lea rdx, [s_http_host]
    call append
    mov rcx, rax
    mov rdx, rbx
    call append
    mov [rsp+40], rax
    mov rcx, r12
    call int_to_str
    mov rdx, rax
    mov rcx, [rsp+40]
    mov byte [rcx], ':'
    inc rcx
    call append
    mov rcx, rax
    lea rdx, [s_http_tail]
    call append
    mov r15, rax
    sub r15, rdi
    mov rcx, rbx
    mov rdx, r12
    xor r8d, r8d
    call tcp_connect
    mov rsi, rax
    mov rcx, rsi
    mov rdx, rdi
    mov r8, r15
    call tcp_send_all
    mov rcx, 16777216
    call alloc
    mov rdi, rax
    xor r13d, r13d              ; fill
    mov r14, -1                 ; header end
    mov r15, -1                 ; content length
.rd:
    mov r8, 16777216
    sub r8, r13
    dec r8
    jle .toolong
    mov rcx, rsi
    lea rdx, [rdi+r13]
    call tcp_recv
    test rax, rax
    jz .closed
    add r13, rax
    cmp r14, -1
    jne .body
    mov rcx, rdi
    mov rdx, r13
    call find_hdr_end
    cmp rax, -1
    je .rd
    mov r14, rax
    mov rcx, rdi
    mov rdx, r14
    lea r8, [s_clen]
    call memfind
    test rax, rax
    jz .body
    lea rcx, [rax+15]
    call atoi_z
    mov r15, rax
.body:
    cmp r15, -1
    je .rd
    mov rax, r14
    add rax, r15
    cmp r13, rax
    jl .rd
    jmp .done
.closed:
    cmp r14, -1
    je .nohdr
.done:
    mov rcx, rsi
    call [p_closesocket]
    mov rdx, r15
    cmp rdx, -1
    jne .len
    mov rdx, r13
    sub rdx, r14
.len:
    mov [rsp+32], rdx
    lea rax, [rdi+r14]
    add rax, rdx
    mov byte [rax], 0
    lea rcx, [rdi+9]
    call atoi_z
    mov r8, rax
    lea rax, [rdi+r14]
    mov rdx, [rsp+32]
    NEPI
.nohdr:
    NFAIL msg_nethdr
.toolong:
    NFAIL msg_toolong

; ws_open(rcx = host, rdx = port, r8 = path) -> rax = ws {socket, rbuf, rfill, rpos}
ws_open:
    NPRO
    mov rbx, rcx
    mov r12, rdx
    mov r14, r8
    mov rcx, 8192
    call alloc
    mov rdi, rax
    mov rcx, rdi
    lea rdx, [s_ws_get]
    call append
    mov rcx, rax
    mov rdx, r14
    call append
    mov rcx, rax
    lea rdx, [s_http_host]
    call append
    mov rcx, rax
    mov rdx, rbx
    call append
    mov [rsp+40], rax
    mov rcx, r12
    call int_to_str
    mov rdx, rax
    mov rcx, [rsp+40]
    mov byte [rcx], ':'
    inc rcx
    call append
    mov rcx, rax
    lea rdx, [s_ws_tail]
    call append
    mov r15, rax
    sub r15, rdi
    mov rcx, rbx
    mov rdx, r12
    xor r8d, r8d
    call tcp_connect
    mov rsi, rax
    mov rcx, rsi
    mov rdx, rdi
    mov r8, r15
    call tcp_send_all
    mov rcx, 64
    call alloc
    mov r13, rax                ; ws
    mov [r13], rsi
    mov rcx, 1048576
    call alloc
    mov [r13+8], rax
    mov qword [r13+16], 0
    mov qword [r13+24], 0
    mov rdi, rax
    mov rcx, 65536
    call alloc
    mov [r13+32], rax           ; the message assembly buffer
    mov qword [r13+40], 65536   ; its capacity
    xor r12d, r12d              ; fill
.rd:
    mov r8, 65536
    sub r8, r12
    jle .refused
    mov rcx, rsi
    lea rdx, [rdi+r12]
    call tcp_recv
    test rax, rax
    jz .refused
    add r12, rax
    mov rcx, rdi
    mov rdx, r12
    call find_hdr_end
    cmp rax, -1
    je .rd
    mov r14, rax
    cmp dword [rdi+8], ' 101'
    jne .refused
    mov [r13+16], r12
    mov [r13+24], r14
    mov rax, r13
    NEPI
.refused:
    NFAIL msg_wsref

ws_read_exact:                  ; rcx = ws, rdx = dst, r8 = n (reads from the buffer, refilling from the socket)
    NPRO
    mov rbx, rcx
    mov rsi, rdx
    mov r12, r8
.l:
    test r12, r12
    jle .d
    mov rax, [rbx+16]
    sub rax, [rbx+24]           ; available
    jg .take
    mov rcx, [rbx]
    mov rdx, [rbx+8]
    mov r8, 1048576
    call tcp_recv
    test rax, rax
    jz .closed
    mov [rbx+16], rax
    mov qword [rbx+24], 0
    jmp .l
.take:
    cmp rax, r12
    jle .n
    mov rax, r12
.n:
    mov r13, rax
    mov rcx, rsi
    mov rdx, [rbx+8]
    add rdx, [rbx+24]
    mov r8, r13
    call memcpy_
    add [rbx+24], r13
    add rsi, r13
    sub r12, r13
    jmp .l
.d:
    NEPI
.closed:
    NFAIL msg_wsclosed

ws_send_frame:                  ; rcx = ws, rdx = ptr, r8 = len, r9 = opcode (masked with the zero key)
    NPRO
    mov rbx, rcx
    mov rsi, rdx
    mov r12, r8
    mov r13, r9
    or r13b, 0x80
    lea rdi, [rsp+32]           ; header, at most 14 bytes
    mov [rdi], r13b
    cmp r12, 126
    jb .short
    cmp r12, 65536
    jb .mid
    mov byte [rdi+1], 0xFF
    mov rax, r12
    bswap rax
    mov [rdi+2], rax
    mov dword [rdi+10], 0
    mov r14, 14
    jmp .send
.mid:
    mov byte [rdi+1], 0xFE
    mov ax, r12w
    xchg al, ah
    mov [rdi+2], ax
    mov dword [rdi+4], 0
    mov r14, 8
    jmp .send
.short:
    mov al, r12b
    or al, 0x80
    mov [rdi+1], al
    mov dword [rdi+2], 0
    mov r14, 6
.send:
    mov rcx, [rbx]
    mov rdx, rdi
    mov r8, r14
    call tcp_send_all
    test r12, r12
    jz .d
    mov rcx, [rbx]
    mov rdx, rsi
    mov r8, r12
    call tcp_send_all
.d:
    NEPI

; ws_recv_text(rcx = ws) -> rax = message (zero-terminated), rdx = len; rax = 0 when the peer closed
ws_recv_text:
    NPRO
    mov rbx, rcx
    mov rdi, [rbx+32]           ; the connection's assembly buffer
    mov r15, [rbx+40]           ; its capacity
    xor r14d, r14d              ; fill
.frame:
    mov rcx, rbx
    lea rdx, [rsp+32]
    mov r8d, 2
    call ws_read_exact
    movzx r12d, byte [rsp+32]   ; fin | opcode
    movzx eax, byte [rsp+33]
    mov r13d, eax
    and r13d, 0x7F              ; length
    and eax, 0x80
    mov [rsp+48], rax           ; masked?
    cmp r13d, 126
    jb .len
    cmp r13d, 127
    je .len8
    mov rcx, rbx
    lea rdx, [rsp+40]
    mov r8d, 2
    call ws_read_exact
    movzx eax, word [rsp+40]
    xchg al, ah
    mov r13d, eax
    jmp .len
.len8:
    mov rcx, rbx
    lea rdx, [rsp+40]
    mov r8d, 8
    call ws_read_exact
    mov r13, [rsp+40]
    bswap r13
.len:
    cmp qword [rsp+48], 0
    je .nomask
    mov rcx, rbx
    lea rdx, [rsp+56]
    mov r8d, 4
    call ws_read_exact
.nomask:
    mov eax, r12d
    and eax, 15
    cmp eax, 8
    je .closed
    cmp eax, 9
    je .ping
    cmp eax, 10
    je .pong
    ; data: make room for len + 1
    mov rax, r14
    add rax, r13
    inc rax
    cmp rax, r15
    jbe .room
.grow:
    shl r15, 1
    cmp r15, 268435456
    ja .toolong
    cmp rax, r15
    ja .grow
    mov rcx, r15
    call alloc
    mov rsi, rax
    mov rcx, rsi
    mov rdx, rdi
    mov r8, r14
    call memcpy_
    mov rdi, rsi
    mov [rbx+32], rdi
    mov [rbx+40], r15
.room:
    mov rcx, rbx
    lea rdx, [rdi+r14]
    mov r8, r13
    call ws_read_exact
    cmp qword [rsp+48], 0
    je .unmasked
    xor ecx, ecx
.um:
    cmp rcx, r13
    jge .unmasked
    mov eax, ecx
    and eax, 3
    mov dl, [rsp+56+rax]
    lea rax, [rdi+r14]
    xor [rax+rcx], dl
    inc rcx
    jmp .um
.unmasked:
    add r14, r13
    test r12b, 0x80
    jz .frame
    lea rcx, [r14+1]
    call alloc
    mov rsi, rax
    mov rcx, rsi
    mov rdx, rdi
    mov r8, r14
    call memcpy_
    mov byte [rsi+r14], 0
    mov rax, rsi
    mov rdx, r14
    NEPI
.ping:
    mov rcx, r13
    inc rcx
    call alloc
    mov rsi, rax
    mov rcx, rbx
    mov rdx, rsi
    mov r8, r13
    call ws_read_exact
    mov rcx, rbx
    mov rdx, rsi
    mov r8, r13
    mov r9d, 10
    call ws_send_frame
    jmp .frame
.pong:
    mov rcx, r13
    inc rcx
    call alloc
    mov rcx, rbx
    mov rdx, rax
    mov r8, r13
    call ws_read_exact
    jmp .frame
.closed:
    xor eax, eax
    xor edx, edx
    NEPI
.toolong:
    NFAIL msg_toolong

; cdp_call(rcx = ws, rdx = id, r8 = method cstr, r9 = params cstr) -> rax = the reply with that id, rdx = len
cdp_call:
    NPRO
    mov rbx, rcx
    mov r12, rdx
    mov r13, r8
    mov r14, r9
    mov rcx, r12
    call int_to_str
    mov r15, rax                ; the id's digits
    mov rcx, r13
    call zlen
    mov rsi, rax
    mov rcx, r14
    call zlen
    add rsi, rax
    lea rcx, [rsi+64]
    call alloc
    mov rdi, rax
    mov rcx, rdi
    lea rdx, [s_cdp1]
    call append
    mov rcx, rax
    mov rdx, r15
    call append
    mov rcx, rax
    lea rdx, [s_cdp2]
    call append
    mov rcx, rax
    mov rdx, r13
    call append
    mov rcx, rax
    lea rdx, [s_cdp3]
    call append
    mov rcx, rax
    mov rdx, r14
    call append
    mov rcx, rax
    lea rdx, [s_cdp4]
    call append
    mov rsi, rax
    sub rsi, rdi
    mov rcx, rbx
    mov rdx, rdi
    mov r8, rsi
    mov r9d, 1
    call ws_send_frame
    ; the prefix {"id":N,
    mov rcx, 64
    call alloc
    mov r13, rax
    mov rcx, r13
    lea rdx, [s_cdp1]
    call append
    mov rcx, rax
    mov rdx, r15
    call append
    mov rcx, rax
    lea rdx, [s_comma]
    call append
    mov r14, rax
    sub r14, r13                ; prefix length
.wait:
    mov rcx, rbx
    call ws_recv_text
    test rax, rax
    jz .closed
    mov rsi, rax
    mov [rsp+32], rdx
    cmp rdx, r14
    jl .wait
    xor ecx, ecx
.cmp:
    cmp rcx, r14
    jge .hit
    mov al, [rsi+rcx]
    cmp al, [r13+rcx]
    jne .wait
    inc rcx
    jmp .cmp
.hit:
    mov rax, rsi
    mov rdx, [rsp+32]
    NEPI
.closed:
    NFAIL msg_wsclosed

; ---------------------------------------------------------------- files with hashes in the certificate
io_note:                        ; rcx = path cstr, rdx = bytes, r8 = len, r9 = kind (0 input, 1 output)
    NPRO
    mov rbx, rcx
    mov r12, r9
    mov r14, rdx
    mov r15, r8
    mov rax, [nio]
    cmp rax, MAXIO
    jge .full
    mov r13, rax
    mov rcx, rbx
    call io_keep_name
    mov rbx, rax
    mov rcx, r14
    mov rdx, r15
    call sha256
    lea rax, [io_path]
    mov [rax+r13*8], rbx
    lea rax, [io_kind]
    mov [rax+r13*8], r12
    lea rcx, [io_dig]
    mov rax, r13
    shl rax, 5
    add rcx, rax
    lea rdx, [sha_dig]
    mov r8d, 32
    call memcpy_
    inc qword [nio]
    NEPI
.full:
    NFAIL msg_ioful

io_keep_name:                   ; rcx = path cstr -> rax = the same bytes in io_names (a path noted before is shared)
    NPRO
    mov rsi, rcx
    call zlen
    mov rdi, rax
    xor r12d, r12d
.find:
    cmp r12, [nio]
    jge .new
    lea rax, [io_path]
    mov rcx, [rax+r12*8]
    xor edx, edx
.cmp:
    mov al, [rcx+rdx]
    cmp al, [rsi+rdx]
    jne .next
    test al, al
    jz .hit
    inc rdx
    jmp .cmp
.next:
    inc r12
    jmp .find
.hit:
    mov rax, rcx
    NEPI
.new:
    mov rax, [io_names_used]
    lea rcx, [rax+rdi+1]
    cmp rcx, IONAMES
    ja .full
    mov [io_names_used], rcx
    lea r13, [io_names]
    add r13, rax
    mov rcx, r13
    mov rdx, rsi
    lea r8, [rdi+1]
    call memcpy_
    mov rax, r13
    NEPI
.full:
    NFAIL msg_ionames

cert_io:                        ; every file read or written, with its hash (the emitter points at the log)
    NPRO
    xor r12d, r12d
.l:
    cmp r12, [nio]
    jge .d
    lea rax, [io_kind]
    cmp qword [rax+r12*8], 0
    jne .out
    lea rcx, [msg_cert_in]
    jmp .k
.out:
    lea rcx, [msg_cert_out]
.k:
    call emit_cstr
    lea rax, [io_path]
    mov rcx, [rax+r12*8]
    call emit_cstr
    lea rcx, [msg_cert_sha]
    call emit_cstr
    lea rcx, [io_dig]
    mov rax, r12
    shl rax, 5
    add rcx, rax
    mov edx, 32
    call emit_hex
    call emit_nl
    inc r12
    jmp .l
.d:
    NEPI

; read NAME PATH
st_read:
    NPRO
    call expect_word
    mov rbx, rax
    call next_arg
    mov r12, rax                ; path
    mov rcx, rax
    call read_file_a
    test rax, rax
    jz .noread
    mov rsi, rax
    mov r13, rdx
    lea rcx, [rdx+1]
    call alloc
    mov rdi, rax
    mov rcx, rdi
    mov rdx, rsi
    mov r8, r13
    call memcpy_
    mov byte [rdi+r13], 0
    mov rcx, rbx
    mov rdx, rdi
    mov r8, r13
    call set_word_pair
    mov rcx, r12
    mov rdx, rdi
    mov r8, r13
    xor r9d, r9d
    call io_note
    NEPI
.noread:
    NFAIL msg_noread

; write PATH ADDR LEN
st_write:
    NPRO
    call next_arg
    mov rbx, rax                ; path
    call next_int
    mov r12, rax                ; bytes
    call next_int
    mov r13, rax                ; len
    mov rcx, rbx
    mov edx, 0x40000000
    xor r8d, r8d
    xor r9d, r9d
    mov qword [rsp+32], 2
    mov qword [rsp+40], 0x80
    mov qword [rsp+48], 0
    call CreateFileA
    cmp rax, -1
    je .nowrite
    mov r14, rax
    mov rcx, r14
    mov rdx, r12
    mov r8, r13
    lea r9, [rsp+56]
    mov qword [rsp+56], 0
    mov qword [rsp+32], 0
    call WriteFile
    test eax, eax
    jz .nowrite
    mov rcx, r14
    call CloseHandle
    mov eax, [rsp+56]
    cmp rax, r13
    jne .nowrite
    mov rcx, rbx
    mov rdx, r12
    mov r8, r13
    mov r9d, 1
    call io_note
    NEPI
.nowrite:
    NFAIL msg_nowr

; ---------------------------------------------------------------- text NAME ...
%macro VERB 2
    mov rcx, r12
    lea rdx, [%1]
    call tok_is
    test eax, eax
    jnz %2
%endmacro

st_text:
    NPRO
    call expect_word
    mov rbx, rax                ; NAME
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    je .literal
    call expect_word
    mov r12, rax                ; the verb
    VERB kw_join, .join
    VERB kw_escape, .escape
    VERB kw_unescape, .unescape
    VERB kw_upto, .upto
    VERB kw_find, .find
    VERB kw_after, .after
    VERB kw_base64, .base64
    VERB kw_compare, .compare
    VERB kw_count, .count
    VERB kw_int, .int
    VERB kw_num, .num
    VERB kw_arg, .argv
    VERB kw_crlf, .crlf
    VERB kw_wide, .wide
    VERB kw_le2, .le2
    VERB kw_le4, .le4
    VERB kw_le8, .le8
    VERB kw_oct, .oct
    VERB kw_crc32, .crc32
    VERB kw_pad, .padv
    VERB kw_os, .osv
    jmp syntax_error
.literal:
    call next_arg
    jmp .pair
.join:
    mov rcx, 1024
    call alloc
    mov r13, rax                ; up to 64 (ptr, len) pairs
    xor r14d, r14d              ; count
    xor r15d, r15d              ; total
.jl:
    call at_eol
    test eax, eax
    jnz .jcat
    cmp r14, 64
    jge syntax_error
    call next_arg
    mov [r13+r14*8], rax
    mov [r13+r14*8+512], rdx
    add r15, rdx
    inc r14
    jmp .jl
.jcat:
    lea rcx, [r15+1]
    call alloc
    mov rdi, rax
    mov rsi, rax
    xor ecx, ecx
    mov [rsp+32], rcx
.jc:
    mov rcx, [rsp+32]
    cmp rcx, r14
    jge .jd
    mov rdx, [r13+rcx*8]
    mov r8, [r13+rcx*8+512]
    mov rcx, rsi
    call memcpy_
    mov rcx, [rsp+32]
    add rsi, [r13+rcx*8+512]
    inc qword [rsp+32]
    jmp .jc
.jd:
    mov byte [rsi], 0
    mov rax, rdi
    mov rdx, r15
    jmp .pair
.escape:
    call next_arg
    mov rcx, rax
    call json_escape
    jmp .pair
.unescape:
    call next_arg
    mov rcx, rax
    call json_unescape
    jmp .pair
.upto:
    call next_arg
    mov r13, rax
    call next_arg
    mov rcx, r13
    mov rdx, rax
    call find_z
    test rax, rax
    jnz .uplen
    mov rcx, r13
    call zlen
    add rax, r13
.uplen:
    mov r14, rax
    sub r14, r13
    lea rcx, [r14+1]
    call alloc
    mov rdi, rax
    mov rcx, rdi
    mov rdx, r13
    mov r8, r14
    call memcpy_
    mov byte [rdi+r14], 0
    mov rax, rdi
    mov rdx, r14
    jmp .pair
.find:
    call next_arg
    mov r13, rax
    call next_arg
    mov rcx, r13
    mov rdx, rax
    call find_z
    xor edx, edx
    jmp .pair
.after:
    call next_arg
    mov r13, rax
    call next_arg
    mov r14, rax
    mov rcx, r13
    mov rdx, r14
    call find_z
    test rax, rax
    jz .aft0
    mov r13, rax
    mov rcx, r14
    call zlen
    add rax, r13
    mov r13, rax                ; the rest, with its length (to the NUL)
    mov rcx, rax
    call zlen
    mov rdx, rax
    mov rax, r13
    jmp .pair
.aft0:
    xor edx, edx
    jmp .pair
.base64:
    call next_arg
    mov rcx, rax
    call b64_decode
    jmp .pair
.compare:
    call next_arg
    mov r13, rax
    mov r14, rdx
    call next_arg
    cmp rdx, r14
    jne .differ
    xor ecx, ecx
.cl:
    cmp rcx, r14
    jge .same
    mov dl, [r13+rcx]
    cmp dl, [rax+rcx]
    jne .differ
    inc rcx
    jmp .cl
.same:
    xor eax, eax
    xor edx, edx
    jmp .pair
.differ:
    mov eax, 1
    xor edx, edx
    jmp .pair
.count:
    call next_arg
    mov r13, rax
    call next_arg
    mov r14, rax
    mov rcx, r14
    call zlen
    mov r15, rax
    xor esi, esi
.cnt:
    mov rcx, r13
    mov rdx, r14
    call find_z
    test rax, rax
    jz .cntd
    inc rsi
    lea r13, [rax+r15]
    jmp .cnt
.cntd:
    mov rax, rsi
    xor edx, edx
    jmp .pair
.int:
    call next_int
    mov rcx, rax
    call int_to_str
    jmp .pair
.argv:
    mov rcx, [titleptr]
    call wide_to_utf8
    jmp .pair
.crlf:
    call next_arg
    mov rcx, rax
    call text_crlf
    jmp .pair
.wide:
    call next_arg
    mov rcx, rax
    call text_wide
    jmp .pair
.le2:
    call next_int
    mov rcx, rax
    mov edx, 2
    call text_le
    jmp .pair
.le4:
    call next_int
    mov rcx, rax
    mov edx, 4
    call text_le
    jmp .pair
.le8:
    call next_int
    mov rcx, rax
    mov edx, 8
    call text_le
    jmp .pair
.oct:
    call next_int
    mov r13, rax
    call next_int
    mov rcx, r13
    mov rdx, rax
    call text_oct
    jmp .pair
.osv:
    lea rcx, [s_os]
    call zlen
    mov rdx, rax
    lea rax, [s_os]
    jmp .pair
.padv:
    call next_arg
    mov r13, rax
    mov r14, rdx
    call next_int
    mov rcx, r13
    mov rdx, r14
    mov r8, rax
    call text_pad
    jmp .pair
.crc32:
    call next_int
    mov r13, rax
    call next_int
    mov rcx, r13
    mov rdx, rax
    call crc32_bytes
    xor edx, edx
    jmp .pair
.num:
    call next_arg
    mov rcx, rax
    call atoi_z
    xor edx, edx
.pair:
    mov rcx, rbx
    mov r8, rdx
    mov rdx, rax
    call set_word_pair
    NEPI

; ---------------------------------------------------------------- net VERB ...
st_net:
    NPRO
    call expect_word
    mov r12, rax
    VERB kw_http, .http
    VERB kw_probe, .probe
    VERB kw_ws, .ws
    VERB kw_send, .send
    VERB kw_recv, .recv
    VERB kw_cdp, .cdp
    VERB kw_close, .close
    jmp syntax_error
.http:
    call expect_word
    mov rbx, rax
    call next_arg
    mov r13, rax                ; host
    call next_int
    mov r14, rax                ; port
    call next_arg
    mov r15, rax                ; method
    call next_arg
    mov rcx, r13
    mov rdx, r14
    mov r8, r15
    mov r9, rax
    call http_request
    jmp .pair
.probe:
    call expect_word
    mov rbx, rax
    call next_arg
    mov r13, rax
    call next_int
    mov rcx, r13
    mov rdx, rax
    mov r8d, 1
    call tcp_connect
    cmp rax, -1
    je .probe0
    mov rcx, rax
    call [p_closesocket]
    mov eax, 1
    jmp .probe1
.probe0:
    xor eax, eax
.probe1:
    xor edx, edx
    jmp .pair
.ws:
    call expect_word
    mov rbx, rax
    call next_arg
    mov r13, rax
    call next_int
    mov r14, rax
    call next_arg
    mov rcx, r13
    mov rdx, r14
    mov r8, rax
    call ws_open
    xor edx, edx
    jmp .pair
.send:
    call next_int
    mov r13, rax
    call next_arg
    mov rcx, r13
    mov r8, rdx
    mov rdx, rax
    mov r9d, 1
    call ws_send_frame
    NEPI
.recv:
    call expect_word
    mov rbx, rax
    call next_int
    mov rcx, rax
    call ws_recv_text
    jmp .pair
.cdp:
    call expect_word
    mov rbx, rax
    call next_int
    mov r13, rax                ; ws
    call next_int
    mov r14, rax                ; id
    call next_arg
    mov r15, rax                ; method
    lea rax, [s_empty_obj]
    mov [rsp+32], rax
    call at_eol
    test eax, eax
    jnz .cdpgo
    call next_arg
    mov [rsp+32], rax
.cdpgo:
    mov rcx, r13
    mov rdx, r14
    mov r8, r15
    mov r9, [rsp+32]
    call cdp_call
    jmp .pair
.close:
    call next_int
    mov rcx, [rax]
    call [p_closesocket]
    NEPI
.pair:
    mov rcx, rbx
    mov r8, rdx
    mov rdx, rax
    call set_word_pair
    NEPI

; wide_to_utf8(rcx = UTF-16 cstr or 0) -> rax = UTF-8 (zero-terminated), rdx = len
wide_to_utf8:
    NPRO
    mov rsi, rcx
    xor r12d, r12d
    test rsi, rsi
    jz .alloc
.cnt:
    cmp word [rsi+r12*2], 0
    je .alloc
    inc r12
    jmp .cnt
.alloc:
    lea rcx, [r12*4+4]
    call alloc
    mov rdi, rax
    xor r13d, r13d
    xor r14d, r14d
.l:
    cmp r13, r12
    jge .d
    movzx eax, word [rsi+r13*2]
    inc r13
    cmp eax, 0xD800
    jb .put
    cmp eax, 0xDBFF
    ja .put
    cmp r13, r12
    jge .put
    movzx ecx, word [rsi+r13*2]
    cmp ecx, 0xDC00
    jb .put
    cmp ecx, 0xDFFF
    ja .put
    inc r13
    sub eax, 0xD800
    shl eax, 10
    sub ecx, 0xDC00
    add eax, ecx
    add eax, 0x10000
.put:
    call put_utf8
    jmp .l
.d:
    mov byte [rdi+r14], 0
    mov rax, rdi
    mov rdx, r14
    NEPI

; ============================================================ twenty-fourth cut: the tools written in the language
; print A B ...                        the words and literals concatenated, then a newline, on stdout
; append PATH ADDR LEN                 LEN bytes appended to the file (created when missing); hashed as an output
; text NAME crlf A                     LF -> CR LF (for edit controls)
; text NAME wide A                     UTF-16 of A, zero-terminated; NAME_len = the bytes
; text NAME le2 W / le4 W / le8 W      the low 2 / 4 / 8 bytes of a word, little-endian
; text NAME oct W N                    N octal digits of W, zero-padded (tar headers)
; text NAME crc32 ADDR LEN             NAME := the CRC-32 (zip) of LEN bytes at ADDR
; set NAME bxor A B                    exclusive or of machine words
section .data
kw_print:      db 'print', 0
kw_append:     db 'append', 0
kw_crlf:       db 'crlf', 0
kw_le2:        db 'le2', 0
kw_le4:        db 'le4', 0
kw_le8:        db 'le8', 0
kw_oct:        db 'oct', 0
kw_crc32:      db 'crc32', 0
kw_bxor:       db 'bxor', 0
kw_div:        db 'div', 0
kw_mod:        db 'mod', 0
section .bss
crc_table:     resd 256
crc_ready:     resq 1
section .text

st_print:
    NPRO
.l:
    call at_eol
    test eax, eax
    jnz .d
    call next_arg
    mov rcx, rax
    call emit_str
    jmp .l
.d:
    call emit_nl
    NEPI

; append PATH ADDR LEN
st_append:
    NPRO
    call next_arg
    mov rbx, rax
    call next_int
    mov r12, rax
    call next_int
    mov r13, rax
    mov rcx, rbx
    mov edx, 4                  ; FILE_APPEND_DATA
    mov r8d, 1
    xor r9d, r9d
    mov qword [rsp+32], 4       ; OPEN_ALWAYS
    mov qword [rsp+40], 0x80
    mov qword [rsp+48], 0
    call CreateFileA
    cmp rax, -1
    je .nowrite
    mov r14, rax
    mov rcx, r14
    mov rdx, r12
    mov r8, r13
    lea r9, [rsp+56]
    mov qword [rsp+56], 0
    mov qword [rsp+32], 0
    call WriteFile
    mov rcx, r14
    call CloseHandle
    mov eax, [rsp+56]
    cmp rax, r13
    jne .nowrite
    NEPI
.nowrite:
    NFAIL msg_nowr

text_crlf:                      ; rcx = src, rdx = len -> rax = dst, rdx = len
    NPRO
    mov rsi, rcx
    mov r12, rdx
    lea rcx, [rdx*2+1]
    call alloc
    mov rdi, rax
    xor r13d, r13d
    xor r14d, r14d
.l:
    cmp r13, r12
    jge .d
    mov al, [rsi+r13]
    inc r13
    cmp al, 10
    jne .put
    mov byte [rdi+r14], 13
    inc r14
.put:
    mov [rdi+r14], al
    inc r14
    jmp .l
.d:
    mov byte [rdi+r14], 0
    mov rax, rdi
    mov rdx, r14
    NEPI

text_wide:                      ; rcx = src, rdx = len -> rax = UTF-16 (zero-terminated), rdx = bytes
    NPRO
    mov rsi, rcx
    mov r12, rdx
    lea rcx, [rdx*4+8]
    call alloc
    mov rdi, rax
    mov rcx, rsi
    mov rdx, r12
    mov r8, rdi
    lea r9, [r12*2+2]
    call utf8_to_wide           ; -> rax = words written
    mov word [rdi+rax*2], 0
    lea rdx, [rax*2]
    mov rax, rdi
    NEPI

text_le:                        ; rcx = value, rdx = n bytes -> rax = bytes, rdx = n
    NPRO
    mov rbx, rcx
    mov r12, rdx
    mov rcx, 16
    call alloc
    mov [rax], rbx
    mov byte [rax+8], 0
    mov rdx, r12
    NEPI

text_oct:                       ; rcx = value, rdx = digits -> rax = digits, rdx = n
    NPRO
    mov rbx, rcx
    mov r12, rdx
    lea rcx, [rdx+1]
    call alloc
    mov rdi, rax
    mov byte [rdi+r12], 0
    mov rcx, r12
.l:
    test rcx, rcx
    jz .d
    dec rcx
    mov rax, rbx
    and eax, 7
    add al, '0'
    mov [rdi+rcx], al
    shr rbx, 3
    jmp .l
.d:
    mov rax, rdi
    mov rdx, r12
    NEPI

crc32_bytes:                    ; rcx = ptr, rdx = len -> rax = crc32
    push rbx
    push rsi
    mov rsi, rcx
    mov rbx, rdx
    cmp qword [crc_ready], 0
    jne .go
    xor ecx, ecx
.tbl:
    mov eax, ecx
    mov r8d, 8
.bit:
    shr eax, 1
    jnc .nox
    xor eax, 0xEDB88320
.nox:
    dec r8d
    jnz .bit
    lea rdx, [crc_table]
    mov [rdx+rcx*4], eax
    inc ecx
    cmp ecx, 256
    jb .tbl
    mov qword [crc_ready], 1
.go:
    mov eax, 0xFFFFFFFF
    xor ecx, ecx
    lea r9, [crc_table]
.l:
    cmp rcx, rbx
    jge .d
    movzx edx, byte [rsi+rcx]
    xor dl, al
    movzx edx, dl
    shr eax, 8
    xor eax, [r9+rdx*4]
    inc rcx
    jmp .l
.d:
    not eax
    pop rsi
    pop rbx
    ret

; text NAME pad A N : A copied into N bytes, zero-filled (or cut) -- fixed-width fields
section .data
kw_pad:        db 'pad', 0
kw_os:         db 'os', 0
%ifdef LINUX
s_os:          db 'linux', 0
%else
s_os:          db 'windows', 0
%endif
section .text
text_pad:                       ; rcx = src, rdx = len, r8 = n -> rax = bytes, rdx = n
    NPRO
    mov rsi, rcx
    mov r12, rdx
    mov r13, r8
    lea rcx, [r13+1]
    call alloc
    mov rdi, rax
    cmp r12, r13
    jle .cp
    mov r12, r13
.cp:
    mov rcx, rdi
    mov rdx, rsi
    mov r8, r12
    call memcpy_
    mov rax, rdi
    mov rdx, r13
    NEPI

; sym_find_bytes(rcx = name ptr, rdx = name len) -> rax = the symbol, or 0
sym_find_bytes:
    push rbx
    push rsi
    push rdi
    mov rsi, rcx
    mov rdi, rdx
    lea rbx, [symbols]
    xor ecx, ecx
.loop:
    cmp rcx, [nsym]
    jge .none
    cmp [rbx+8], rdi
    jne .next
    xor edx, edx
.cmp:
    cmp rdx, rdi
    jge .hit
    mov r8, [rbx]
    mov al, [rsi+rdx]
    cmp al, [r8+rdx]
    jne .next
    inc rdx
    jmp .cmp
.hit:
    mov rax, rbx
    jmp .out
.next:
    add rbx, 32
    inc rcx
    jmp .loop
.none:
    xor eax, eax
.out:
    pop rdi
    pop rsi
    pop rbx
    ret

; word_len(rcx = token index of a word, rdx = its address) -> rax = NAME_len when that word exists, else the zero-terminated length
word_len:
    NPRO
    mov rbx, rcx
    mov r12, rdx
    call tok_ptr
    mov rsi, [rax]
    mov rdi, [rax+8]
    lea rcx, [rdi+5]
    call alloc
    mov r14, rax
    mov rcx, rax
    mov rdx, rsi
    mov r8, rdi
    call memcpy_
    lea rcx, [r14+rdi]
    lea rdx, [s_ulen]
    call append
    mov rcx, r14
    lea rdx, [rdi+4]
    call sym_find_bytes
    test rax, rax
    jz .z
    cmp qword [rax+16], 3
    jne .z
    mov rax, [rax+24]
    NEPI
.z:
    mov rcx, r12
    call zlen
    NEPI
; ============================================================ chapter: a program within the program (twenty-sixth cut)
; chapter "NAME" ["ARGUMENT"]
; NAME starts afresh inside the one program: the arena is released back to where the run began, the symbols, the labels
; and the gosub stack are the chapter's alone (its labels are scanned up to the next chapter), the previous chapter's
; Process log is closed, and `arg` reads ARGUMENT - or nothing, when the chapter names none (an input read through
; `arg` is then named in the certificate by the chapter line's string). The log opened before the first chapter is
; the one program's own: it is kept aside and receives the certificate at the end. Claims, inputs, outputs, statements
; and the cost keep accumulating: one program, one certificate. The line "chapter NAME" is printed.
section .data
msg_chapter:    db 10, 'chapter '
msg_chapter_len equ $ - msg_chapter
section .text
st_chapter:
    push rbx
    push rdi
    push r12
    push r13
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    jne syntax_error
    mov r12, [rax]
    mov r13, [rax+8]
    lea rcx, [msg_chapter]
    mov edx, msg_chapter_len
    call emit_str
    mov rcx, r12
    mov rdx, r13
    call emit_str
    call emit_nl
    inc qword [cur]
    inc qword [nchapters]
    ; the argument: the chapter's own, or none
    mov rax, [orig_title]
    mov [titleptr], rax
    mov qword [chap_argtok], -1
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    jne .noarg
    mov rcx, [rax]
    mov rdx, [rax+8]
    lea r8, [chapargw]
    mov r9, 1030
    call utf8_to_wide
    lea rdx, [chapargw]
    mov word [rdx+rax*2], 0
    mov [titleptr], rdx
    mov rax, [cur]
    mov [chap_argtok], rax
    inc qword [cur]
.noarg:
    ; the log open before the first chapter is the one program's own and is kept; a chapter's log is closed
    mov rcx, [proch]
    test rcx, rcx
    jz .nolog
    cmp qword [nchapters], 1
    jne .close
    mov [top_proch], rcx
    mov qword [proch], 0
    jmp .nolog
.close:
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 32
    call CloseHandle
    mov rsp, rbp
    pop rbp
    mov qword [proch], 0
.nolog:
    ; the arena back to the base and zeroed; the symbols, the mark and the gosub stack cleared
    mov rdi, [arena_base]
    mov rcx, [arena]
    sub rcx, rdi
    shr rcx, 3
    xor eax, eax
    rep stosq
    mov rax, [arena_base]
    mov [arena], rax
    mov qword [marked], 0
    mov qword [nsym], 0
    mov qword [dsp], 0
    mov qword [retsp], 0
    ; this chapter's labels
    mov rcx, [cur]
    call scan_labels
    pop r13
    pop r12
    pop rdi
    pop rbx
    ret

; top_log : at the end of the run, when a chapter's log is open and the one program's own was kept aside, the
; chapter's is closed and the program's own becomes the log again, so the certificate lands there.
top_log:
    mov rax, [top_proch]
    test rax, rax
    jz .ret
    mov rcx, [proch]
    test rcx, rcx
    jz .swap
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 32
    call CloseHandle
    mov rsp, rbp
    pop rbp
.swap:
    mov rax, [top_proch]
    mov [proch], rax
    mov qword [top_proch], 0
.ret:
    ret
; ============================================================ use: libraries (twenty-seventh cut)
; use "PATH"
; A library is a file of routines (label ... return) and the values they agree on. Before the program is tokenized,
; every line-leading `use "PATH"` in the program - and in the libraries it brings in - is resolved: the file is read
; (PATH relative to the program's directory, else to the interpreter's), once however often it is used, and its text is
; appended to the program after a line `library "PATH"`. The program ends where the first library begins; the routines
; beyond that line are reached by gosub. Their labels belong to every chapter. Each library read from disk is an input
; of the certificate. `emit` writes the program with its libraries appended, so the binary needs no file: when the
; text already holds `library "PATH"`, `use "PATH"` loads nothing. At run time both statements are no-ops.
section .data
msg_nolib:      db 'use: the library was not found', 10
msg_nolib_len   equ $ - msg_nolib
msg_manylibs:   db 'use: more than 64 libraries', 10
msg_manylibs_len equ $ - msg_manylibs
lib_line:       db 10, 'library "'
lib_line_len    equ $ - lib_line
section .bss
MAXLIB equ 64
libtab:     resq MAXLIB*4        ; path ptr, path len, text ptr, text len
nlibs:      resq 1
usepathw:   resw 1100
usebuf:     resb 1200
prog_end:   resq 1               ; token index where the first library begins (ntok when there is none)
section .text

; flatten_uses : resolve the program's uses; srcptr/srclen become the program with its libraries appended
flatten_uses:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov qword [nlibs], 0
    mov rcx, [srcptr]
    mov rdx, [srclen]
    call scan_uses
    cmp qword [nlibs], 0
    je .ret
    mov rax, [srclen]
    xor r12d, r12d
    lea rbx, [libtab]
.sum:
    cmp r12, [nlibs]
    jge .alloc
    add rax, [rbx+8]
    add rax, [rbx+24]
    add rax, lib_line_len+2
    add rbx, 32
    inc r12
    jmp .sum
.alloc:
    mov rcx, rax
    call alloc
    mov r13, rax                ; the new text
    mov rdi, rax
    mov rcx, rdi
    mov rdx, [srcptr]
    mov r8, [srclen]
    call memcpy_
    add rdi, [srclen]
    xor r12d, r12d
    lea rbx, [libtab]
.app:
    cmp r12, [nlibs]
    jge .done
    mov rcx, rdi
    lea rdx, [lib_line]
    mov r8d, lib_line_len
    call memcpy_
    add rdi, lib_line_len
    mov rcx, rdi
    mov rdx, [rbx]
    mov r8, [rbx+8]
    call memcpy_
    add rdi, [rbx+8]
    mov byte [rdi], '"'
    mov byte [rdi+1], 10
    add rdi, 2
    mov rcx, rdi
    mov rdx, [rbx+16]
    mov r8, [rbx+24]
    call memcpy_
    mov [rbx+16], rdi           ; the section's text is now the copy
    add rdi, [rbx+24]
    add rbx, 32
    inc r12
    jmp .app
.done:
    mov [srcptr], r13
    sub rdi, r13
    mov [srclen], rdi
.ret:
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; scan_uses(rcx = text, rdx = len) : every line-leading use "PATH" loads its library (and that library's uses)
scan_uses:
    push rbx
    push rsi
    push r12
    push r13
    push r14
    mov rsi, rcx
    lea r12, [rcx+rdx]
    mov ebx, 1                  ; at the start of a line
.l:
    cmp rsi, r12
    jae .done
    test ebx, ebx
    jnz .check
    movzx eax, byte [rsi]
    inc rsi
    cmp al, 10
    jne .l
    mov ebx, 1
    jmp .l
.check:
    xor ebx, ebx
    lea rax, [rsi+5]
    cmp rax, r12
    ja .l
    cmp byte [rsi], 'u'
    jne .l
    cmp byte [rsi+1], 's'
    jne .l
    cmp byte [rsi+2], 'e'
    jne .l
    cmp byte [rsi+3], ' '
    jne .l
    cmp byte [rsi+4], '"'
    jne .l
    lea r13, [rsi+5]
    mov r14, r13
.pe:
    cmp r14, r12
    jae .l
    cmp byte [r14], '"'
    je .got
    inc r14
    jmp .pe
.got:
    mov rcx, r13
    mov rdx, r14
    sub rdx, r13
    call use_load
    mov rsi, r14
    jmp .l
.done:
    pop r14
    pop r13
    pop r12
    pop rsi
    pop rbx
    ret

; use_load(rcx = path bytes, rdx = len) : read the library unless it is already in the table or in the text
use_load:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    mov r12, rcx
    mov r13, rdx
    ; already loaded?
    xor r14d, r14d
    lea rbx, [libtab]
.t:
    cmp r14, [nlibs]
    jge .intext
    cmp [rbx+8], r13
    jne .tn
    mov rcx, [rbx]
    mov rdx, r12
    mov r8, r13
    call mem_eq
    test eax, eax
    jnz .ret
.tn:
    add rbx, 32
    inc r14
    jmp .t
.intext:                        ; a section library "PATH" already in the program text (an emitted program)?
    lea rdi, [usebuf]
    mov rcx, rdi
    lea rdx, [lib_line]
    mov r8d, lib_line_len
    call memcpy_
    add rdi, lib_line_len
    mov rcx, rdi
    mov rdx, r12
    mov r8, r13
    call memcpy_
    add rdi, r13
    mov byte [rdi], '"'
    mov byte [rdi+1], 0
    mov rcx, [srcptr]
    mov rdx, [srclen]
    lea r8, [usebuf]
    call memfind
    test rax, rax
    jnz .ret
    cmp qword [nlibs], MAXLIB
    jge .many
    ; beside the program, then beside the interpreter
    mov rsi, [wpath]
    test rsi, rsi
    jz .self
    call use_path
    lea rcx, [usepathw]
    call read_file_w
    test rax, rax
    jnz .have
.self:
    lea rsi, [wbuf]
    call use_path
    lea rcx, [usepathw]
    call read_file_w
    test rax, rax
    jz .nolib
.have:
    mov rcx, [nlibs]
    shl rcx, 5
    lea rbx, [libtab]
    add rbx, rcx
    mov [rbx], r12
    mov [rbx+8], r13
    mov [rbx+16], rax
    mov [rbx+24], rdx
    inc qword [nlibs]
    mov rcx, rax
    call scan_uses              ; the library's own uses
.ret:
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.nolib:
    lea rcx, [msg_nolib]
    mov edx, msg_nolib_len
    jmp fail
.many:
    lea rcx, [msg_manylibs]
    mov edx, msg_manylibs_len
    jmp fail

; use_path : usepathw := the directory of the wide path at rsi + the UTF-8 name r12/r13, terminated
use_path:
    push rbx
    push rdi
    xor ecx, ecx
    mov rdx, -1
.s:
    movzx eax, word [rsi+rcx*2]
    test eax, eax
    jz .copy
    cmp eax, '\'
    je .sep
    cmp eax, '/'
    jne .next
.sep:
    mov rdx, rcx
.next:
    inc rcx
    cmp rcx, 1000
    jb .s
.copy:
    lea rbx, [usepathw]
    xor edi, edi                ; words written
    test rdx, rdx
    js .name
    xor ecx, ecx
.cp:
    movzx eax, word [rsi+rcx*2]
    mov [rbx+rdi*2], ax
    inc rdi
    inc rcx
    cmp rcx, rdx
    jle .cp
.name:
    mov rcx, r12
    mov rdx, r13
    lea r8, [rbx+rdi*2]
    mov r9, 1090
    sub r9, rdi
    call utf8_to_wide
    add rdi, rax
    mov word [rbx+rdi*2], 0
    pop rdi
    pop rbx
    ret

; mem_eq(rcx, rdx, r8 = n) -> eax 1 when the n bytes agree
mem_eq:
    xor eax, eax
.l:
    test r8, r8
    jz .yes
    mov r9b, [rcx]
    cmp r9b, [rdx]
    jne .no
    inc rcx
    inc rdx
    dec r8
    jmp .l
.yes:
    mov eax, 1
.no:
    ret

; find_prog_end : after tokenizing, the first line-leading `library` token ends the program; each library section
; read from disk is noted as an input (its path string token names it in the certificate)
find_prog_end:
    push rbx
    push r12
    push r13
    mov rax, [ntok]
    mov [prog_end], rax
    xor r12d, r12d              ; token index
    xor r13d, r13d              ; sections seen
.l:
    cmp r12, [ntok]
    jge .done
    mov rcx, r12
    lea rdx, [kw_library]
    call tok_is
    test eax, eax
    jz .next
    test r12, r12
    jz .lead
    mov rcx, r12
    dec rcx
    call tok_ptr
    cmp qword [rax+16], 3
    jne .next
.lead:
    cmp r13, 0
    jne .note
    mov [prog_end], r12
.note:
    cmp r13, [nlibs]
    jge .count
    mov rax, r13
    shl rax, 5
    lea rbx, [libtab]
    add rbx, rax
    mov rcx, [rbx+16]
    mov rdx, [rbx+24]
    lea r8, [r12+1]
    call note_input
.count:
    inc r13
.next:
    inc r12
    jmp .l
.done:
    pop r13
    pop r12
    pop rbx
    ret

; use "PATH" / library "PATH" at run time: nothing (resolved before the run)
st_use:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 4
    jne syntax_error
    inc qword [cur]
    ret
; ============================================================ push / pop: a data stack for recursion (twenty-eighth cut)
; push A B C ...   saves the current binding (kind and payload) of each name, in order
; pop A B C ...    restores them: the same list as the push, restored from the last name back to the first
; Names are global; a routine that calls itself, directly or through others, pushes the names it still needs after
; the call and pops them after it. A name not yet bound is saved as the machine word 0.
section .data
msg_dstack_full: db 'push: the data stack is full', 10
msg_dstack_full_len equ $ - msg_dstack_full
msg_dstack_empty: db 'pop: the data stack is empty', 10
msg_dstack_empty_len equ $ - msg_dstack_empty
section .bss
MAXDSTACK equ 131072
dstack:     resq MAXDSTACK
dsp:        resq 1
section .text

st_push:
    push rbx
.l:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 3
    je .done
    cmp qword [rax+16], 0
    jne syntax_error
    mov rbx, [dsp]
    cmp rbx, MAXDSTACK-2
    jae .full
    mov rcx, [cur]
    call sym_find
    test rax, rax
    jz .unbound
    mov rcx, [rax+16]
    mov rdx, [rax+24]
    jmp .store
.unbound:
    mov ecx, 3
    xor edx, edx
.store:
    lea rax, [dstack]
    mov [rax+rbx*8], rcx
    mov [rax+rbx*8+8], rdx
    add rbx, 2
    mov [dsp], rbx
    inc qword [cur]
    jmp .l
.done:
    pop rbx
    ret
.full:
    lea rcx, [msg_dstack_full]
    mov edx, msg_dstack_full_len
    jmp fail

st_pop:
    push rbx
    push r12
    push r13
    mov r12, [cur]              ; the first name
    mov r13, r12
.count:                          ; r13 := the newline token
    mov rcx, r13
    call tok_ptr
    cmp qword [rax+16], 3
    je .back
    cmp qword [rax+16], 0
    jne syntax_error
    inc r13
    jmp .count
.back:
    mov [cur], r13
    mov rbx, r13
.l:
    cmp rbx, r12
    jbe .done
    dec rbx
    mov rax, [dsp]
    cmp rax, 2
    jb .empty
    sub rax, 2
    mov [dsp], rax
    lea rdx, [dstack]
    mov r8, [rdx+rax*8+8]       ; payload
    mov rdx, [rdx+rax*8]        ; kind
    mov rcx, rbx
    call sym_set
    jmp .l
.done:
    pop r13
    pop r12
    pop rbx
    ret
.empty:
    lea rcx, [msg_dstack_empty]
    mov edx, msg_dstack_empty_len
    jmp fail
tokenize:
    push rbx
    push rsi
    push rdi
    push r12
    mov rsi, [srcptr]
    mov rdi, rsi
    add rdi, [srclen]
    lea r12, [tokens]
    mov qword [ntok], 0
.loop:
    cmp rsi, rdi
    jge .done
    movzx eax, byte [rsi]
    cmp al, ' '
    je .skip
    cmp al, 9
    je .skip
    cmp al, 13
    je .skip
    cmp al, ';'
    je .comment
    cmp al, 10
    je .newline
    cmp al, '['
    je .lbr
    cmp al, ']'
    je .rbr
    cmp al, '"'
    je .string
    ; word
    mov rbx, rsi
.word:
    cmp rsi, rdi
    jge .word_end
    movzx eax, byte [rsi]
    cmp al, ' '
    je .word_end
    cmp al, 9
    je .word_end
    cmp al, 13
    je .word_end
    cmp al, 10
    je .word_end
    cmp al, '['
    je .word_end
    cmp al, ']'
    je .word_end
    cmp al, ';'
    je .word_end
    inc rsi
    jmp .word
.word_end:
    mov [r12], rbx
    mov rax, rsi
    sub rax, rbx
    mov [r12+8], rax
    mov qword [r12+16], 0
    add r12, 24
    inc qword [ntok]
    jmp .loop
.comment:
    cmp rsi, rdi
    jge .done
    cmp byte [rsi], 10
    je .loop
    inc rsi
    jmp .comment
.newline:
    mov [r12], rsi
    mov qword [r12+8], 1
    mov qword [r12+16], 3
    mov rax, [ntok]
    mov rcx, [nlseen]
    inc rcx
    mov [nlseen], rcx
    lea rdx, [tokline]
    mov [rdx+rax*8], rcx
    add r12, 24
    inc qword [ntok]
    inc rsi
    jmp .loop
.lbr:
    mov [r12], rsi
    mov qword [r12+8], 1
    mov qword [r12+16], 1
    add r12, 24
    inc qword [ntok]
    inc rsi
    jmp .loop
.rbr:
    mov [r12], rsi
    mov qword [r12+8], 1
    mov qword [r12+16], 2
    add r12, 24
    inc qword [ntok]
    inc rsi
    jmp .loop
.string:
    inc rsi                     ; skip the opening quote
    mov rbx, rsi                ; content start
.string_scan:
    cmp rsi, rdi
    jge .string_end
    cmp byte [rsi], '"'
    je .string_end
    inc rsi
    jmp .string_scan
.string_end:
    mov [r12], rbx
    mov rax, rsi
    sub rax, rbx
    mov [r12+8], rax
    mov qword [r12+16], 4       ; type 4 = string literal
    add r12, 24
    inc qword [ntok]
    cmp rsi, rdi
    jge .loop
    inc rsi                     ; skip the closing quote
    jmp .loop
.skip:
    inc rsi
    jmp .loop
.done:
    ; a final newline token so every line is terminated
    mov [r12], rsi
    mov qword [r12+8], 1
    mov qword [r12+16], 3
    inc qword [ntok]
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; tok_ptr(rcx=index) -> rax = &tokens[index]
tok_ptr:
    mov rax, rcx
    imul rax, 24
    lea rdx, [tokens]
    add rax, rdx
    ret

; tok_is(rcx=index, rdx=NUL string) -> eax 1/0 : word token equal to the string
tok_is:
    push rbx
    push rsi
    mov rsi, rdx
    call tok_ptr
    cmp qword [rax+16], 0
    jne .no
    mov rbx, [rax]
    mov rcx, [rax+8]
.cmp:
    movzx eax, byte [rsi]
    test rcx, rcx
    jz .end_tok
    cmp al, [rbx]
    jne .no
    test al, al
    jz .no
    inc rsi
    inc rbx
    dec rcx
    jmp .cmp
.end_tok:
    test al, al
    jnz .no
    mov eax, 1
    pop rsi
    pop rbx
    ret
.no:
    xor eax, eax
    pop rsi
    pop rbx
    ret

; tok_int(rcx=index) -> rax : the word as a signed integer, or syntax error
tok_int:
    push rbx
    push rsi
    push rdi
    call tok_ptr
    cmp qword [rax+16], 0
    jne syntax_error
    mov rsi, [rax]
    mov rdi, [rax+8]
    xor ebx, ebx                ; negative flag
    test rdi, rdi
    jz syntax_error
    ; a '.' makes this a decimal literal: parse it exactly, then it must be a whole number for a machine word
    xor ecx, ecx
.scan_dot:
    cmp rcx, rdi
    jge .no_dot
    cmp byte [rsi+rcx], '.'
    je .decimal
    inc rcx
    jmp .scan_dot
.decimal:
    mov rcx, rsi
    mov rdx, rdi
    call q_parse
    mov rcx, rax
    call q_to_i64
    pop rdi
    pop rsi
    pop rbx
    ret
.no_dot:
    cmp byte [rsi], '-'
    jne .digits_start
    mov ebx, 1
    inc rsi
    dec rdi
    test rdi, rdi
    jz syntax_error
.digits_start:
    xor eax, eax
    ; a 0x / 0X prefix switches to hexadecimal (needed for bytes, GUIDs, property ids)
    cmp rdi, 2
    jl .digits
    cmp byte [rsi], '0'
    jne .digits
    movzx ecx, byte [rsi+1]
    or cl, 0x20
    cmp cl, 'x'
    jne .digits
    add rsi, 2
    sub rdi, 2
    test rdi, rdi
    jz syntax_error
.hex:
    test rdi, rdi
    jz .done
    movzx ecx, byte [rsi]
    or cl, 0x20                 ; fold A-F onto a-f (and leave digits unchanged)
    cmp cl, '0'
    jb syntax_error
    cmp cl, '9'
    jbe .hdig
    cmp cl, 'a'
    jb syntax_error
    cmp cl, 'f'
    ja syntax_error
    sub cl, ('a' - 10)
    jmp .hput
.hdig:
    sub cl, '0'
.hput:
    ; Accumulate a negative magnitude so -2^63 is representable throughout.
    imul rax, rax, 16
    jo overflow
    movzx ecx, cl
    sub rax, rcx
    jo overflow
    inc rsi
    dec rdi
    jmp .hex
.digits:
    test rdi, rdi
    jz .done
    movzx ecx, byte [rsi]
    sub ecx, '0'
    cmp ecx, 9
    ja syntax_error
    imul rax, rax, 10
    jo overflow
    sub rax, rcx
    jo overflow
    inc rsi
    dec rdi
    jmp .digits
.done:
    test ebx, ebx
    jnz .out
    neg rax
    jo overflow
.out:
    pop rdi
    pop rsi
    pop rbx
    ret

; ============================================================ symbols
; sym_find(rcx=token index) -> rax = &symbol or 0
sym_find:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    call tok_ptr
    mov rsi, [rax]              ; name ptr
    mov rdi, [rax+8]            ; name len
    lea r12, [symbols]
    xor r13, r13
.loop:
    cmp r13, [nsym]
    jge .none
    cmp [r12+8], rdi
    jne .next
    mov rbx, [r12]
    xor ecx, ecx
.cmp:
    cmp rcx, rdi
    jge .hit
    mov al, [rbx+rcx]
    cmp al, [rsi+rcx]
    jne .next
    inc rcx
    jmp .cmp
.hit:
    mov rax, r12
    jmp .out
.next:
    add r12, 32
    inc r13
    jmp .loop
.none:
    xor eax, eax
.out:
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; sym_set(rcx=token index, rdx=kind, r8=payload)
sym_set:
    push rbx
    push r12
    push r13
    push r14
    mov r13, rdx
    mov r14, r8
    mov rbx, rcx
    call sym_find
    test rax, rax
    jnz .store
    mov rax, [nsym]
    cmp rax, MAXSYM
    jge sym_full
    imul rax, 32
    lea rdx, [symbols]
    add rax, rdx
    inc qword [nsym]
    mov rcx, rbx
    push rax
    call tok_ptr
    mov rdx, rax
    pop rax
    mov rcx, [rdx]
    mov [rax], rcx
    mov rcx, [rdx+8]
    mov [rax+8], rcx
.store:
    mov [rax+16], r13
    mov [rax+24], r14
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; value_at(rcx=token index) -> rax = matrix (a value symbol), or unknown error
; the symbol table is full: every name, label and library label of a program (or of one chapter) takes one entry
section .data
msg_sym_full: db 'too many names: the symbol table holds 16384', 10
msg_sym_full_len equ $ - msg_sym_full
section .text
sym_full:
    lea rcx, [msg_sym_full]
    mov edx, msg_sym_full_len
    jmp fail

; value_at(rcx = token index) -> rax = matrix : a value symbol, or a machine word lifted to a 1x1 matrix
value_at:
    call sym_find
    test rax, rax
    jz unknown_error
    cmp qword [rax+16], 2
    je .value
    cmp qword [rax+16], 3
    jne unknown_error
    mov rcx, [rax+24]
    call q_from_i64
    push rax
    mov ecx, 1
    mov edx, 1
    call mat_new
    pop rdx
    mov [rax+16], rdx
    ret
.value:
    mov rax, [rax+24]
    ret

; space_at(rcx = token index) -> rax = dimension
space_at:
    call sym_find
    test rax, rax
    jz unknown_error
    cmp qword [rax+16], 1
    jne unknown_error
    mov rax, [rax+24]
    ret

; tok_q(rcx = token index) -> rax = the word as a rational
tok_q:
    call tok_ptr
    cmp qword [rax+16], 0
    jne syntax_error
    mov rcx, [rax]
    mov rdx, [rax+8]
    jmp q_parse

; tok_is_number(rcx = token index) -> eax 1 when the word begins with a digit or '-'
tok_is_number:
    call tok_ptr
    cmp qword [rax+16], 0
    jne .no
    mov rcx, [rax]
    movzx edx, byte [rcx]
    cmp dl, '-'
    je .yes
    cmp dl, '0'
    jb .no
    cmp dl, '9'
    ja .no
.yes:
    mov eax, 1
    ret
.no:
    xor eax, eax
    ret

; q_operand(rcx = token index) -> rax = rational : a literal, a machine word, or the first cell of a value
q_operand:
    push rbx
    mov rbx, rcx
    call tok_is_number
    test eax, eax
    jz .sym
    mov rcx, rbx
    call tok_q
    pop rbx
    ret
.sym:
    mov rcx, rbx
    call sym_find
    test rax, rax
    jz unknown_error
    cmp qword [rax+16], 3
    jne .value
    mov rcx, [rax+24]
    call q_from_i64
    pop rbx
    ret
.value:
    cmp qword [rax+16], 2
    jne unknown_error
    mov rax, [rax+24]
    mov rax, [rax+16]
    pop rbx
    ret

; ============================================================ parsing literals
; parse_matrix: at [cur] expect '[' ... ']' ; rows are '[ a b ]' groups, or a flat list = a column vector. -> rax
parse_matrix:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub rsp, 32
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 1
    jne syntax_error
    inc qword [cur]
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 1
    je .nested
    ; flat: count numbers until ']'
    mov r12, [cur]
    xor r13d, r13d
.count:
    mov rcx, r12
    call tok_ptr
    cmp qword [rax+16], 2
    je .flat_alloc
    cmp qword [rax+16], 0
    jne syntax_error
    inc r12
    inc r13
    jmp .count
.flat_alloc:
    mov rcx, r13
    mov edx, 1
    call mat_new
    mov r14, rax
    xor r15d, r15d
.flat_fill:
    cmp r15, r13
    jge .flat_done
    mov rcx, [cur]
    call tok_q
    mov [r14+16+r15*8], rax
    inc qword [cur]
    inc r15
    jmp .flat_fill
.flat_done:
    inc qword [cur]             ; the ']'
    mov rax, r14
    jmp .out
.nested:
    ; first pass: count rows and the first row's columns
    mov r12, [cur]
    xor r13d, r13d              ; rows
    xor ebx, ebx                ; cols of the first row
.rows:
    mov rcx, r12
    call tok_ptr
    cmp qword [rax+16], 2
    je .alloc
    cmp qword [rax+16], 1
    jne syntax_error
    inc r12
    xor edi, edi
.cells:
    mov rcx, r12
    call tok_ptr
    cmp qword [rax+16], 2
    je .row_end
    cmp qword [rax+16], 0
    jne syntax_error
    inc r12
    inc rdi
    jmp .cells
.row_end:
    inc r12
    test r13, r13
    jnz .check_cols
    mov rbx, rdi
.check_cols:
    cmp rdi, rbx
    jne shape_error
    inc r13
    jmp .rows
.alloc:
    mov rcx, r13
    mov rdx, rbx
    call mat_new
    mov r14, rax
    xor r15d, r15d              ; flat index
.fill_rows:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 2
    je .fill_done
    inc qword [cur]             ; '['
.fill_cells:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 2
    je .fill_row_end
    mov rcx, [cur]
    call tok_q
    mov [r14+16+r15*8], rax
    inc r15
    inc qword [cur]
    jmp .fill_cells
.fill_row_end:
    inc qword [cur]             ; ']'
    jmp .fill_rows
.fill_done:
    inc qword [cur]             ; outer ']'
    mov rax, r14
.out:
    add rsp, 32
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret

; ============================================================ statements
report_map:
    push rbx
    push rsi
    push r12
    mov rbx, rcx
    mov rsi, rdx
    mov rcx, rbx
    call tok_ptr
    mov rcx, [rax]
    mov rdx, [rax+8]
    call emit_str
    lea rcx, [msg_colon]
    call emit_cstr
    mov rcx, [rsi+8]
    call emit_int
    lea rcx, [msg_arrow]
    call emit_cstr
    mov rcx, [rsi]
    call emit_int
    mov rcx, rsi
    call mat_rank
    mov r12, rax
    lea rcx, [msg_rank]
    call emit_cstr
    mov rcx, r12
    call emit_int
    lea rcx, [msg_nullity]
    call emit_cstr
    mov rcx, [rsi+8]
    sub rcx, r12
    call emit_int
    call emit_nl
    pop r12
    pop rsi
    pop rbx
    ret

; skip_line: advance cur past the next newline token
skip_line:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 3
    je .nl
    inc qword [cur]
    jmp skip_line
.nl:
    inc qword [cur]
    inc qword [lineno]
    ret

; expect_word: current token must be a word; returns its index in rax and advances
expect_word:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 0
    jne syntax_error
    mov rax, [cur]
    inc qword [cur]
    ret

; ---- statement handlers; each leaves cur at the newline
st_space:                       ; space NAME N
    push rbx
    call expect_word
    mov rbx, rax
    call expect_word
    mov rcx, rax
    call tok_int
    mov rcx, rbx
    mov edx, 1
    mov r8, rax
    call sym_set
    pop rbx
    ret

st_vector:                      ; vector NAME [: S] [ ... ]
    push rbx
    push r12
    call expect_word
    mov rbx, rax
    mov r12, -1                 ; declared dim
    mov rcx, [cur]
    lea rdx, [kw_colon]
    call tok_is
    test eax, eax
    jz .literal
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call space_at
    mov r12, rax
.literal:
    call parse_matrix
    cmp r12, -1
    je .store
    cmp [rax], r12
    jne .space_err
.store:
    mov rcx, rbx
    mov edx, 2
    mov r8, rax
    call sym_set
    pop r12
    pop rbx
    ret
.space_err:
    lea rcx, [msg_space]
    mov edx, msg_space_len
    jmp fail

st_map:                         ; map NAME [: S -> T] [ [ .. ] .. ]
    push rbx
    push r12
    push r13
    call expect_word
    mov rbx, rax
    mov r12, -1
    mov r13, -1
    mov rcx, [cur]
    lea rdx, [kw_colon]
    call tok_is
    test eax, eax
    jz .literal
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call space_at
    mov r12, rax                ; domain dim
    mov rcx, [cur]
    lea rdx, [kw_arrow]
    call tok_is
    test eax, eax
    jz syntax_error
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call space_at
    mov r13, rax                ; codomain dim
.literal:
    call parse_matrix
    cmp r12, -1
    je .store
    cmp [rax+8], r12
    jne .space_err
    cmp [rax], r13
    jne .space_err
.store:
    mov rcx, rbx
    mov edx, 2
    mov r8, rax
    push rax
    call sym_set
    pop rdx
    mov rcx, rbx
    call report_map
    pop r13
    pop r12
    pop rbx
    ret
.space_err:
    lea rcx, [msg_space]
    mov edx, msg_space_len
    jmp fail


%macro OPCASE 2                 ; if the op token (r12) is %1, jump to %2
    mov rcx, r12
    lea rdx, [%1]
    call tok_is
    test eax, eax
    jnz %2
%endmacro

st_let:                         ; let NAME OP args
    push rbx
    push r12
    push r13
    push r14
    call expect_word
    mov rbx, rax                ; result name
    call expect_word
    mov r12, rax                ; op
    OPCASE kw_apply, .binary_mul
    OPCASE kw_compose, .binary_mul
    OPCASE kw_add, .add
    OPCASE kw_sub, .sub
    OPCASE kw_tensor, .tensor
    OPCASE kw_power, .power
    OPCASE kw_transpose, .transpose
    OPCASE kw_scale, .scale
    OPCASE kw_kernel, .kernel
    OPCASE kw_image, .image
    OPCASE kw_left, .left_word
    OPCASE kw_right, .right_word
    OPCASE kw_leftinverse, .left
    OPCASE kw_rightinverse, .right
    OPCASE kw_inverse, .inverse
    OPCASE kw_solve, .solve
    OPCASE kw_rref, .rref
    OPCASE kw_iterate, .iterate
    OPCASE kw_identity, .identity
    OPCASE kw_augment, .augment
    OPCASE kw_stack, .stack
    OPCASE kw_directsum, .directsum
    OPCASE kw_trace, .trace
    OPCASE kw_det, .det
    OPCASE kw_charpoly, .charpoly
    OPCASE kw_evaluate, .evaluate
    OPCASE kw_orthogonalize, .orthogonalize
    OPCASE kw_projector, .projector
    OPCASE kw_entry, .entry
    OPCASE kw_total, .total
    OPCASE kw_refute, .refute
    OPCASE kw_nullvector, .nullvector
    OPCASE kw_cowitness, .cowitness
    OPCASE kw_complement, .complement
    OPCASE kw_block, .block
    OPCASE kw_rows, .rowsval
    OPCASE kw_cols, .colsval
    OPCASE kw_zero, .zeromat
    OPCASE kw_polymul, .polymul
    OPCASE kw_polyadd, .polyadd
    OPCASE kw_polysub, .polysub
    OPCASE kw_polyquo, .polyquo
    OPCASE kw_polyrem, .polyrem
    OPCASE kw_vec, .vec
    OPCASE kw_diagonal, .diagonal
    OPCASE kw_quotient, .quotient
    OPCASE kw_homology, .homology
    OPCASE kw_blockdet, .blockdet
    OPCASE kw_blocktrace, .blocktrace
    OPCASE kw_diag, .diagvec
    OPCASE kw_unvec, .unvec
    OPCASE kw_blockmul, .blockmul
    OPCASE kw_cost, .costval
    OPCASE kw_minpoly, .minpoly
    OPCASE kw_companion, .companion
    OPCASE kw_polygcd, .polygcd
    OPCASE kw_polyderiv, .polyderiv
    OPCASE kw_rank, .rankval
    OPCASE kw_nullity, .nullityval
    jmp syntax_error
.binary_mul:
    call two_values
    mov rcx, rax
    call mat_mul
    jmp .store
.add:
    call two_values
    mov rcx, rax
    mov r8, 1
    call mat_addsub
    jmp .store
.sub:
    call two_values
    mov rcx, rax
    mov r8, -1
    call mat_addsub
    jmp .store
.tensor:
    call two_values
    mov rcx, rax
    call mat_kron
    jmp .store
.augment:
    call two_values
    mov rcx, rax
    call mat_augment
    jmp .store
.stack:
    call two_values
    mov rcx, rax
    call mat_stack
    jmp .store
.directsum:
    call two_values
    mov rcx, rax
    call mat_directsum
    jmp .store
.evaluate:
    call two_values
    mov rcx, rax
    call mat_polyeval
    jmp .store
.power:
    call expect_word
    mov rcx, rax
    call value_at
    mov r13, rax
    call expect_word
    mov rcx, rax
    call operand
    mov rcx, r13
    mov rdx, rax
    call mat_power
    jmp .store
.identity:
    call expect_word
    mov rcx, rax
    call operand
    mov rcx, rax
    call mat_identity
    jmp .store
.transpose:
    call one_value
    call mat_transpose
    jmp .store
.kernel:
    call one_value
    call mat_kernel
    jmp .store
.image:
    call one_value
    call mat_image
    jmp .store
.rref:
    call one_value
    call mat_rref_copy
    jmp .store
.total:
    call one_value
    call mat_total
    mov rcx, rax
    call scalar_mat
    jmp .store
.trace:
    call one_value
    call mat_trace
    mov rcx, rax
    call scalar_mat
    jmp .store
.det:
    call one_value
    call mat_det
    mov rcx, rax
    call scalar_mat
    jmp .store
.charpoly:
    call one_value
    call mat_charpoly
    jmp .store
.orthogonalize:
    call one_value
    call mat_orthogonalize
    jmp .store
.projector:
    call one_value
    call mat_projector
    test rax, rax
    jz .noproj
    jmp .store
.scale:
    call expect_word
    mov rcx, rax
    call q_operand
    mov r13, rax
    call one_value
    mov rdx, rcx
    mov rcx, r13
    call mat_scale
    jmp .store
.entry:                         ; entry v i  (a column) | entry M i j ; indices from 1
    call one_value
    mov r13, rcx
    call expect_word
    mov rcx, rax
    call operand
    dec rax
    mov r14, rax                ; i
    xor edx, edx                ; j
    cmp qword [r13+8], 1
    je .entry_get
    call expect_word
    mov rcx, rax
    call operand
    dec rax
    mov rdx, rax
.entry_get:
    cmp r14, [r13]
    jae shape_error
    cmp rdx, [r13+8]
    jae shape_error
    mov rcx, r13
    mov r8, rdx
    mov rdx, r14
    call cell
    mov rcx, [rax]
    call scalar_mat
    jmp .store
.left_word:                     ; "left inverse A"
    call expect_word
    mov rcx, rax
    lea rdx, [kw_inverse]
    call tok_is
    test eax, eax
    jz syntax_error
.left:
    call one_value
    call mat_leftinverse
    test rax, rax
    jz .noleft
    jmp .store
.right_word:                    ; "right inverse A"
    call expect_word
    mov rcx, rax
    lea rdx, [kw_inverse]
    call tok_is
    test eax, eax
    jz syntax_error
.right:
    call one_value
    call mat_rightinverse
    test rax, rax
    jz .noright
    jmp .store
.inverse:                       ; both sides: the left inverse of a square map of full rank
    call one_value
    mov r13, rcx
    mov rcx, [r13]
    cmp rcx, [r13+8]
    jne .noleft
    mov rcx, r13
    call mat_leftinverse
    test rax, rax
    jz .noleft
    jmp .store
.refute:
    call two_values
    mov rcx, rax
    call mat_refute
    test rax, rax
    jz .norefute
    jmp .store
.nullvector:
    call one_value
    call mat_nullvector
    test rax, rax
    jz .nonull
    jmp .store
.cowitness:
    call one_value
    call mat_cowitness
    test rax, rax
    jz .nocow
    jmp .store
.complement:
    call one_value
    call mat_complement
    jmp .store
.block:                         ; block M r1 r2 c1 c2 (1-based, inclusive)
    call one_value
    mov r13, rcx
    lea r14, [callargs]
    call expect_word
    mov rcx, rax
    call operand
    dec rax
    mov [r14], rax
    call expect_word
    mov rcx, rax
    call operand
    dec rax
    mov [r14+8], rax
    call expect_word
    mov rcx, rax
    call operand
    dec rax
    mov [r14+16], rax
    call expect_word
    mov rcx, rax
    call operand
    dec rax
    mov [r14+24], rax
    mov rcx, r13
    mov rdx, r14
    call mat_block
    jmp .store
.polymul:
    call two_values
    mov rcx, rax
    call mat_polymul
    jmp .store
.polyadd:
    call two_values
    mov rcx, rax
    mov r8, 1
    call mat_polyaddsub
    jmp .store
.polysub:
    call two_values
    mov rcx, rax
    mov r8, -1
    call mat_polyaddsub
    jmp .store
.polyquo:
    call two_values
    mov rcx, rax
    call mat_polydivmod
    jmp .store
.polyrem:
    call two_values
    mov rcx, rax
    call mat_polydivmod
    mov rax, rdx
    jmp .store
.vec:
    call one_value
    call mat_vec
    jmp .store
.diagonal:
    call one_value
    call mat_diagonal
    jmp .store
.quotient:                      ; quotient K B : representatives of span K modulo span B
    call two_values
    mov rcx, rax
    call mat_quotient
    test rax, rax
    jz .noquot
    jmp .store
.noquot:
    lea rcx, [msg_noquot]
    mov edx, msg_noquot_len
    jmp fail
.homology:                      ; homology d1 d2 : ker d1 / im d2
    call two_values
    mov rcx, rax
    call mat_homology
    test rax, rax
    jz .nobdry
    jmp .store
.nobdry:
    lea rcx, [msg_nobdry]
    mov edx, msg_nobdry_len
    jmp fail
.blockdet:                      ; blockdet M k
    call one_value
    mov r13, rcx
    call expect_word
    mov rcx, rax
    call operand
    mov rcx, r13
    mov rdx, rax
    call mat_blockdet
    jmp .store
.blocktrace:                    ; blocktrace M k
    call one_value
    mov r13, rcx
    call expect_word
    mov rcx, rax
    call operand
    mov rcx, r13
    mov rdx, rax
    call mat_blocktrace
    jmp .store
.diagvec:
    call one_value
    call mat_diagvec
    jmp .store
.unvec:                         ; unvec v m
    call one_value
    mov r13, rcx
    call expect_word
    mov rcx, rax
    call operand
    mov rcx, r13
    mov rdx, rax
    call mat_unvec
    jmp .store
.blockmul:                      ; blockmul A B k : blockwise product
    call two_values
    mov r13, rax
    mov r14, rdx
    call expect_word
    mov rcx, rax
    call operand
    mov rcx, r13
    mov rdx, r14
    mov r8, rax
    call mat_blockmul
    jmp .store
.costval:                       ; cost : the rational operations performed so far, as a 1x1 value
    mov rcx, [qops]
    call int_scalar
    jmp .store
.minpoly:
    call one_value
    call mat_minpoly
    jmp .store
.companion:
    call one_value
    call mat_companion
    jmp .store
.polygcd:
    call two_values
    mov rcx, rax
    call poly_gcd
    jmp .store
.polyderiv:
    call one_value
    call poly_deriv
    jmp .store
.rowsval:
    call one_value
    mov rcx, [rcx]
    call int_scalar
    jmp .store
.colsval:
    call one_value
    mov rcx, [rcx+8]
    call int_scalar
    jmp .store
.zeromat:                       ; zero m n
    call expect_word
    mov rcx, rax
    call operand
    mov r13, rax
    call expect_word
    mov rcx, rax
    call operand
    mov rcx, r13
    mov rdx, rax
    call mat_new
    jmp .store
.rankval:
    call one_value
    call mat_rank
    mov rcx, rax
    call int_scalar
    jmp .store
.nullityval:
    call one_value
    mov r13, rcx
    call mat_rank
    mov rcx, [r13+8]
    sub rcx, rax
    call int_scalar
    jmp .store
.solve:
    call two_values
    mov rcx, rax
    call mat_solve
    test rax, rax
    jz .nosol
    jmp .store
.iterate:                       ; iterate A k v
    call one_value
    mov r13, rcx
    call expect_word
    mov rcx, rax
    call operand
    mov r14, rax
    call one_value
    mov rax, rcx
.it:
    test r14, r14
    jle .store
    mov rcx, r13
    mov rdx, rax
    call mat_mul
    dec r14
    jmp .it
.store:
    mov rcx, rbx
    mov edx, 2
    mov r8, rax
    call sym_set
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.noleft:
    lea rcx, [msg_noleft]
    mov edx, msg_noleft_len
    jmp fail
.noright:
    lea rcx, [msg_noright]
    mov edx, msg_noright_len
    jmp fail
.nosol:
    lea rcx, [msg_nosol]
    mov edx, msg_nosol_len
    jmp fail
.norefute:
    lea rcx, [msg_norefute]
    mov edx, msg_norefute_len
    jmp fail
.nonull:
    lea rcx, [msg_nonull]
    mov edx, msg_nonull_len
    jmp fail
.nocow:
    lea rcx, [msg_nocow]
    mov edx, msg_nocow_len
    jmp fail
.noproj:
    lea rcx, [msg_noproj]
    mov edx, msg_noproj_len
    jmp fail

; one_value: reads one name -> rcx = its matrix (rax too)
one_value:
    call expect_word
    mov rcx, rax
    call value_at
    mov rcx, rax
    ret
two_values:
    push rbx
    call expect_word
    mov rcx, rax
    call value_at
    mov rbx, rax
    call expect_word
    mov rcx, rax
    call value_at
    mov rdx, rax
    mov rax, rbx
    pop rbx
    ret


st_show:                        ; show X | show rank A | show nullity A | show wide ADDR
    push rbx
    mov rcx, [cur]
    lea rdx, [kw_wide]
    call tok_is
    test eax, eax
    jnz .wide
    mov rcx, [cur]
    lea rdx, [kw_rank]
    call tok_is
    test eax, eax
    jnz .rank
    mov rcx, [cur]
    lea rdx, [kw_nullity]
    call tok_is
    test eax, eax
    jnz .nullity
    call expect_word
    mov rcx, rax
    call sym_find
    test rax, rax
    jz unknown_error
    cmp qword [rax+16], 3
    je .word
    cmp qword [rax+16], 2
    jne unknown_error
    mov rcx, [rax+24]
    call print_mat
    pop rbx
    ret
.word:
    mov rcx, [rax+24]
    call emit_int
    call emit_nl
    pop rbx
    ret
.wide:
    inc qword [cur]
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov rcx, rax
    call emit_utf16
    pop rbx
    ret
.rank:
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rcx, rax
    call mat_rank
    mov rcx, rax
    call emit_int
    call emit_nl
    pop rbx
    ret
.nullity:
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rbx, rax
    mov rcx, rax
    call mat_rank
    mov rcx, [rbx+8]
    sub rcx, rax
    call emit_int
    call emit_nl
    pop rbx
    ret

%macro CHECKCASE 2              ; if the word at cur is %1, jump to %2
    mov rcx, [cur]
    lea rdx, [%1]
    call tok_is
    test eax, eax
    jnz %2
%endmacro

st_check:                       ; check zero X | independent A B .. | orthogonal A B | projection P | injective A | surjective A | isomorphism A
    push rbx
    push r12
    push r13
    push r14
    CHECKCASE kw_zero, .zero
    CHECKCASE kw_nonzero_c, .nonzero
    CHECKCASE kw_nonnegative, .nonneg
    CHECKCASE kw_exact, .exact
    CHECKCASE kw_independent, .independent
    CHECKCASE kw_orthogonal, .orthogonal
    CHECKCASE kw_projection, .projection
    CHECKCASE kw_injective, .injective
    CHECKCASE kw_surjective, .surjective
    CHECKCASE kw_isomorphism, .isomorphism
    jmp syntax_error
.zero:
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rcx, rax
    call mat_is_zero
    test eax, eax
    jz .notzero_j
    jmp .zero_ok
.nonzero:
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rcx, rax
    call mat_is_zero
    test eax, eax
    jnz .notnonzero
    lea rcx, [msg_ok_nonzero]
    mov edx, msg_ok_nonzero_len
    call emit_str
    jmp .done
.notnonzero:
    lea rcx, [msg_notnonzero]
    mov edx, msg_notnonzero_len
    jmp fail
.nonneg:
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rcx, rax
    call mat_nonnegative
    test eax, eax
    jz .notnonneg
    lea rcx, [msg_ok_nonneg]
    mov edx, msg_ok_nonneg_len
    call emit_str
    jmp .done
.notnonneg:
    lea rcx, [msg_notnonneg]
    mov edx, msg_notnonneg_len
    jmp fail
.exact:                         ; check exact A B : im B = ker A
    inc qword [cur]
    call two_values
    mov rcx, rax
    call mat_exact
    test eax, eax
    jz .notexact
    lea rcx, [msg_ok_exact]
    mov edx, msg_ok_exact_len
    call emit_str
    jmp .done
.notexact:
    lea rcx, [msg_notexact]
    mov edx, msg_notexact_len
    jmp fail
.zero_ok:
    lea rcx, [msg_ok_zero]
    mov edx, msg_ok_zero_len
    call emit_str
    jmp .done
.notzero_j:
    jmp .notzero
.notzero:
    lea rcx, [msg_notzero]
    mov edx, msg_notzero_len
    jmp fail
.independent:
    inc qword [cur]
    ; gather the names up to the newline; every map flattened is one column of a big matrix; rank must equal count
    mov r12, [cur]
    xor r13d, r13d              ; count
.count:
    mov rcx, r12
    call tok_ptr
    cmp qword [rax+16], 3
    je .counted
    inc r12
    inc r13
    jmp .count
.counted:
    test r13, r13
    jz syntax_error
    mov rcx, [cur]
    call value_at
    mov rbx, [rax]
    imul rbx, [rax+8]           ; entries per map
    mov rcx, rbx
    mov rdx, r13
    call mat_new
    mov r14, rax                ; big matrix: entries x count
    xor r12d, r12d              ; column
.fill:
    cmp r12, r13
    jge .filled
    call expect_word
    mov rcx, rax
    call value_at
    mov rcx, [rax]
    imul rcx, [rax+8]
    cmp rcx, rbx
    jne shape_error
    xor edx, edx
.entries:
    cmp rdx, rbx
    jge .fill_next
    mov r8, [rax+16+rdx*8]
    mov r9, rdx
    imul r9, r13
    add r9, r12
    mov [r14+16+r9*8], r8
    inc rdx
    jmp .entries
.fill_next:
    inc r12
    jmp .fill
.filled:
    mov rcx, r14
    call mat_rank
    cmp rax, r13
    jne .dependent
    lea rcx, [msg_ok_ind]
    mov edx, msg_ok_ind_len
    call emit_str
    jmp .done
.dependent:
    lea rcx, [msg_dependent]
    mov edx, msg_dependent_len
    jmp fail
.orthogonal:
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rbx, rax
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 3
    je .orth_cols
    call expect_word
    mov rcx, rax
    call value_at
    mov r12, rax                ; B
    mov rcx, rbx
    call mat_transpose
    mov rcx, rax
    mov rdx, r12
    call mat_mul                ; A^T B
    mov rcx, rax
    call mat_is_zero
    test eax, eax
    jz .notorth
    lea rcx, [msg_ok_orth]
    mov edx, msg_ok_orth_len
    call emit_str
    jmp .done
.notorth:
    lea rcx, [msg_notorth]
    mov edx, msg_notorth_len
    jmp fail
.orth_cols:                     ; one value: its columns must be pairwise orthogonal, i.e. A^T A diagonal
    mov rcx, rbx
    call mat_transpose
    mov rcx, rax
    mov rdx, rbx
    call mat_mul
    mov rcx, rax
    call mat_offdiag_zero
    test eax, eax
    jz .notorthc
    lea rcx, [msg_ok_orth]
    mov edx, msg_ok_orth_len
    call emit_str
    jmp .done
.notorthc:
    lea rcx, [msg_notorthc]
    mov edx, msg_notorthc_len
    jmp fail
.projection:                    ; P P - P = 0
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rbx, rax
    mov rcx, rax
    mov rdx, rax
    call mat_mul
    mov rcx, rax
    mov rdx, rbx
    mov r8, -1
    call mat_addsub
    mov rcx, rax
    call mat_is_zero
    test eax, eax
    jz .notproj
    lea rcx, [msg_ok_proj]
    mov edx, msg_ok_proj_len
    call emit_str
    jmp .done
.notproj:
    lea rcx, [msg_notproj]
    mov edx, msg_notproj_len
    jmp fail
.injective:                     ; rank = dim domain
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rbx, rax
    mov rcx, rax
    call mat_rank
    cmp rax, [rbx+8]
    jne .notinj
    lea rcx, [msg_ok_inj]
    mov edx, msg_ok_inj_len
    call emit_str
    jmp .done
.notinj:
    lea rcx, [msg_notinj]
    mov edx, msg_notinj_len
    jmp fail
.surjective:                    ; rank = dim codomain
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rbx, rax
    mov rcx, rax
    call mat_rank
    cmp rax, [rbx]
    jne .notsur
    lea rcx, [msg_ok_sur]
    mov edx, msg_ok_sur_len
    call emit_str
    jmp .done
.notsur:
    lea rcx, [msg_notsur]
    mov edx, msg_notsur_len
    jmp fail
.isomorphism:                   ; both
    inc qword [cur]
    call expect_word
    mov rcx, rax
    call value_at
    mov rbx, rax
    mov rcx, rax
    call mat_rank
    cmp rax, [rbx]
    jne .notiso
    cmp rax, [rbx+8]
    jne .notiso
    lea rcx, [msg_ok_iso]
    mov edx, msg_ok_iso_len
    call emit_str
    jmp .done
.notiso:
    lea rcx, [msg_notiso]
    mov edx, msg_notiso_len
    jmp fail
.done:
    inc qword [checks_passed]
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; ============================================================ the imperative / OS layer
; operand(rcx = token index) -> rax = a machine word: a number literal, a machine-word symbol, or the first
; cell of a value (which must be an integer that fits)
operand:
    push rbx
    mov rbx, rcx
    call tok_is_number
    test eax, eax
    jnz .num
    mov rcx, rbx
    call sym_find
    test rax, rax
    jz unknown_error
    cmp qword [rax+16], 3
    jne .value
    mov rax, [rax+24]
    pop rbx
    ret
.value:
    cmp qword [rax+16], 2
    jne unknown_error
    mov rax, [rax+24]
    mov rcx, [rax+16]
    call q_to_i64
    pop rbx
    ret
.num:
    mov rcx, rbx
    call tok_int
    pop rbx
    ret

; store_scalar(rcx = name token index, rdx = value): NAME := a machine word
store_scalar:
    mov r8, rdx
    mov edx, 3
    jmp sym_set
do_call:
    push rbp
    mov rbp, rsp
    push rbx
    push rsi
    mov rax, rcx
    mov rbx, r8
    sub rsp, 96                 ; 32 shadow + room for stack args 5..12
    and rsp, -16
    mov rcx, [rbx+32]
    mov [rsp+32], rcx
    mov rcx, [rbx+40]
    mov [rsp+40], rcx
    mov rcx, [rbx+48]
    mov [rsp+48], rcx
    mov rcx, [rbx+56]
    mov [rsp+56], rcx
    mov rcx, [rbx+64]
    mov [rsp+64], rcx
    mov rcx, [rbx+72]
    mov [rsp+72], rcx
    mov rcx, [rbx+80]
    mov [rsp+80], rcx
    mov rcx, [rbx+88]
    mov [rsp+88], rcx
    mov rcx, [rbx]
    mov rdx, [rbx+8]
    mov r8,  [rbx+16]
    mov r9,  [rbx+24]
    call rax
    lea rsp, [rbp-16]
    pop rsi
    pop rbx
    pop rbp
    ret

; goto_newline: advance cur to the next newline token, leaving cur AT it
goto_newline:
.l:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 3
    je .at
    inc qword [cur]
    jmp .l
.at:
    ret

; token_to_cstr(rcx = token index, rdx = dest): copy the word's bytes then a NUL
token_to_cstr:
    push rbx
    push rsi
    push rdi
    mov rdi, rdx
    call tok_ptr
    mov rsi, [rax]
    mov rbx, [rax+8]
    xor ecx, ecx
.l:
    cmp rcx, rbx
    jge .end
    mov dl, [rsi+rcx]
    mov [rdi+rcx], dl
    inc rcx
    jmp .l
.end:
    mov byte [rdi+rcx], 0
    pop rdi
    pop rsi
    pop rbx
    ret

; emit_utf16(rcx = address of a NUL-terminated UTF-16 string): print it as UTF-8
emit_utf16:
    push rbx
    push rsi
    mov rsi, rcx
    test rsi, rsi
    jz .done
.loop:
    movzx eax, word [rsi]
    test ax, ax
    jz .done
    add rsi, 2
    cmp ax, 0xD800
    jb .enc
    cmp ax, 0xDC00
    jae .enc
    movzx edx, word [rsi]
    cmp dx, 0xDC00
    jb .enc
    cmp dx, 0xE000
    jae .enc
    add rsi, 2
    movzx eax, ax
    sub eax, 0xD800
    shl eax, 10
    movzx ecx, dx
    sub ecx, 0xDC00
    add eax, ecx
    add eax, 0x10000
.enc:
    cmp eax, 0x80
    jb .one
    cmp eax, 0x800
    jb .two
    cmp eax, 0x10000
    jb .three
    mov ebx, eax
    mov ecx, ebx
    shr ecx, 18
    and ecx, 0x07
    or ecx, 0xF0
    call emit_char
    mov ecx, ebx
    shr ecx, 12
    and ecx, 0x3F
    or ecx, 0x80
    call emit_char
    mov ecx, ebx
    shr ecx, 6
    and ecx, 0x3F
    or ecx, 0x80
    call emit_char
    mov ecx, ebx
    and ecx, 0x3F
    or ecx, 0x80
    call emit_char
    jmp .loop
.three:
    mov ebx, eax
    mov ecx, ebx
    shr ecx, 12
    and ecx, 0x0F
    or ecx, 0xE0
    call emit_char
    mov ecx, ebx
    shr ecx, 6
    and ecx, 0x3F
    or ecx, 0x80
    call emit_char
    mov ecx, ebx
    and ecx, 0x3F
    or ecx, 0x80
    call emit_char
    jmp .loop
.two:
    mov ebx, eax
    mov ecx, ebx
    shr ecx, 6
    and ecx, 0x1F
    or ecx, 0xC0
    call emit_char
    mov ecx, ebx
    and ecx, 0x3F
    or ecx, 0x80
    call emit_char
    jmp .loop
.one:
    mov ecx, eax
    call emit_char
    jmp .loop
.done:
    pop rsi
    pop rbx
    ret

; scan_labels(rcx = first token): the labels from there to the next chapter, then the libraries' (from prog_end)
scan_labels:
    push rcx
    mov rcx, [prog_end]
    mov rdx, [ntok]
    cmp rcx, rdx
    jae .none
    call scan_range             ; the libraries first: a label of the program itself wins over theirs
.none:
    pop rcx
    mov rdx, [prog_end]
    call scan_range
    ret

; scan_range(rcx = first token, rdx = end): every line-leading "label NAME" up to end or the next line-leading
; `chapter` becomes a symbol (kind 4) -> the newline index of its line
scan_range:
    push rbx
    push r12
    push r13
    mov r12, rcx
    mov r13, rdx
.l:
    cmp r12, r13
    jge .done
    mov rcx, r12
    lea rdx, [kw_chapter]
    call tok_is
    test eax, eax
    jz .notch
    test r12, r12
    jz .done
    mov rcx, r12
    dec rcx
    call tok_ptr
    cmp qword [rax+16], 3
    je .done
.notch:
    mov rcx, r12
    lea rdx, [kw_label]
    call tok_is
    test eax, eax
    jz .next
    test r12, r12
    jz .islabel
    mov rcx, r12
    dec rcx
    call tok_ptr
    cmp qword [rax+16], 3
    jne .next
.islabel:
    lea rbx, [r12+1]            ; name token index
    mov r12, rbx
.findnl:
    inc r12
    cmp r12, [ntok]
    jge .reg
    mov rcx, r12
    call tok_ptr
    cmp qword [rax+16], 3
    jne .findnl
.reg:
    mov rcx, rbx
    mov edx, 4
    mov r8, r12
    call sym_set
    jmp .next
.next:
    inc r12
    jmp .l
.done:
    pop r13
    pop r12
    pop rbx
    ret

; extern NAME DLL FUNC  ->  NAME := the address of FUNC in DLL
st_extern:
    push rbx
    push r12
    call expect_word
    mov rbx, rax                ; NAME token
    call expect_word
    mov rcx, rax
    lea rdx, [namebuf1]
    call token_to_cstr
    call expect_word
    mov rcx, rax
    lea rdx, [namebuf2]
    call token_to_cstr
    ; LoadLibraryA(namebuf1) through an aligned frame (Win32 uses SSE and faults on a misaligned stack)
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 32
    lea rcx, [namebuf1]
    call LoadLibraryA
    mov rsp, rbp
    pop rbp
    test rax, rax
    jz .fail
    mov r12, rax                ; module
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 32
    mov rcx, r12
    lea rdx, [namebuf2]
    call GetProcAddress
    mov rsp, rbp
    pop rbp
    test rax, rax
    jz .fail
    mov rcx, rbx
    mov rdx, rax
    call store_scalar
    pop r12
    pop rbx
    ret
.fail:
    lea rcx, [msg_extern]
    mov edx, msg_extern_len
    jmp fail

; blob NAME [ b b b ... ]  ->  NAME := address of a byte block
st_blob:
    push rbx
    push r12
    push r13
    call expect_word
    mov rbx, rax
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 1
    jne syntax_error
    inc qword [cur]
    mov r12, [cur]
    xor r13, r13
.count:
    mov rcx, r12
    call tok_ptr
    cmp qword [rax+16], 2
    je .alloc
    inc r12
    inc r13
    jmp .count
.alloc:
    mov rcx, r13
    test rcx, rcx
    jnz .nz
    mov rcx, 1
.nz:
    call alloc
    mov r12, rax
    xor r13, r13
.fill:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 2
    je .fdone
    mov rcx, [cur]
    call tok_int
    mov [r12+r13], al
    inc r13
    inc qword [cur]
    jmp .fill
.fdone:
    inc qword [cur]
    mov rcx, rbx
    mov rdx, r12
    call store_scalar
    pop r13
    pop r12
    pop rbx
    ret

; poke ADDR WIDTH VALUE
st_poke:
    push rbx
    push r12
    push r13
    mov rcx, [cur]
    call operand
    mov rbx, rax
    inc qword [cur]
    mov rcx, [cur]
    call operand
    mov r12, rax
    inc qword [cur]
    mov rcx, [cur]
    call operand
    mov r13, rax
    inc qword [cur]
    cmp r12, 1
    je .b1
    cmp r12, 2
    je .b2
    cmp r12, 4
    je .b4
    mov [rbx], r13
    jmp .done
.b1:
    mov [rbx], r13b
    jmp .done
.b2:
    mov [rbx], r13w
    jmp .done
.b4:
    mov [rbx], r13d
.done:
    pop r13
    pop r12
    pop rbx
    ret

; set NAME OP args   (const, arg, alloc, peek, call, vcall, add/sub/mul/shl/shr/band/bor)
st_set:
    push rbx
    push r12
    push r13
    push r14
    call expect_word
    mov rbx, rax                ; result name token
    call expect_word
    mov r12, rax                ; op token
    mov rcx, r12
    lea rdx, [kw_const]
    call tok_is
    test eax, eax
    jnz .const
    mov rcx, r12
    lea rdx, [kw_arg]
    call tok_is
    test eax, eax
    jnz .arg
    mov rcx, r12
    lea rdx, [kw_alloc]
    call tok_is
    test eax, eax
    jnz .alloc
    mov rcx, r12
    lea rdx, [kw_peek]
    call tok_is
    test eax, eax
    jnz .peek
    mov rcx, r12
    lea rdx, [kw_call]
    call tok_is
    test eax, eax
    jnz .call
    mov rcx, r12
    lea rdx, [kw_vcall]
    call tok_is
    test eax, eax
    jnz .vcall
    mov rcx, r12
    lea rdx, [kw_add]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_sub]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_mul]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_shl]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_shr]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_band]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_bor]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_bxor]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_div]
    call tok_is
    test eax, eax
    jnz .arith
    mov rcx, r12
    lea rdx, [kw_mod]
    call tok_is
    test eax, eax
    jnz .arith
    jmp syntax_error
.const:
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov r14, rax
    jmp .store
.arg:
    mov r14, [titleptr]
    jmp .store
.alloc:
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov rcx, rax
    call alloc
    mov r14, rax
    jmp .store
.peek:
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov r13, rax
    mov rcx, [cur]
    call operand
    inc qword [cur]
    cmp rax, 1
    je .pk1
    cmp rax, 2
    je .pk2
    cmp rax, 4
    je .pk4
    mov r14, [r13]
    jmp .store
.pk1:
    movzx r14d, byte [r13]
    jmp .store
.pk2:
    movzx r14d, word [r13]
    jmp .store
.pk4:
    mov r14d, dword [r13]
    jmp .store
.call:
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov r13, rax                ; fn
    call .zeroargs
    xor r14, r14
.call_args:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 3
    je .call_go
    cmp r14, 12
    jge .call_go
    mov rcx, [cur]
    call operand
    inc qword [cur]
    lea rcx, [callargs]
    mov [rcx+r14*8], rax
    inc r14
    jmp .call_args
.call_go:
    mov rcx, r13
    mov rdx, r14
    lea r8, [callargs]
    call do_call
    mov r14, rax
    jmp .store
.vcall:
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov r13, rax                ; obj
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov rdx, [r13]              ; vtable
    mov rdx, [rdx+rax*8]        ; fn at slot
    call .zeroargs
    lea rcx, [callargs]
    mov [rcx], r13             ; obj is the first argument
    mov r13, rdx              ; keep fn in r13
    mov r14, 1
.vcall_args:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 3
    je .vcall_go
    cmp r14, 12
    jge .vcall_go
    mov rcx, [cur]
    call operand
    inc qword [cur]
    lea rcx, [callargs]
    mov [rcx+r14*8], rax
    inc r14
    jmp .vcall_args
.vcall_go:
    mov rcx, r13
    mov rdx, r14
    lea r8, [callargs]
    call do_call
    mov r14, rax
    jmp .store
.arith:
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov r13, rax
    mov rcx, [cur]
    call operand
    inc qword [cur]
    mov r14, rax
    mov rcx, r12
    lea rdx, [kw_add]
    call tok_is
    test eax, eax
    jnz .a_add
    mov rcx, r12
    lea rdx, [kw_sub]
    call tok_is
    test eax, eax
    jnz .a_sub
    mov rcx, r12
    lea rdx, [kw_mul]
    call tok_is
    test eax, eax
    jnz .a_mul
    mov rcx, r12
    lea rdx, [kw_shl]
    call tok_is
    test eax, eax
    jnz .a_shl
    mov rcx, r12
    lea rdx, [kw_shr]
    call tok_is
    test eax, eax
    jnz .a_shr
    mov rcx, r12
    lea rdx, [kw_band]
    call tok_is
    test eax, eax
    jnz .a_band
    mov rcx, r12
    lea rdx, [kw_bxor]
    call tok_is
    test eax, eax
    jnz .a_bxor
    mov rcx, r12
    lea rdx, [kw_div]
    call tok_is
    test eax, eax
    jnz .a_div
    mov rcx, r12
    lea rdx, [kw_mod]
    call tok_is
    test eax, eax
    jnz .a_mod
    mov rax, r13
    or rax, r14
    mov r14, rax
    jmp .store
.a_div:
    test r14, r14
    jz .divzero
    cmp r14, -1
    jne .a_div_ready
    mov rax, 0x8000000000000000
    cmp r13, rax
    jne .a_div_ready
    mov r14, r13
    jmp .store
.a_div_ready:
    mov rax, r13
    cqo
    idiv r14
    mov r14, rax
    jmp .store
.a_mod:
    test r14, r14
    jz .divzero
    cmp r14, -1
    jne .a_mod_ready
    mov rax, 0x8000000000000000
    cmp r13, rax
    jne .a_mod_ready
    xor r14, r14
    jmp .store
.a_mod_ready:
    mov rax, r13
    cqo
    idiv r14
    mov r14, rdx
    jmp .store
.divzero:
    lea rcx, [msg_divzero]
    mov edx, msg_divzero_len
    jmp fail
.a_bxor:
    mov rax, r13
    xor rax, r14
    mov r14, rax
    jmp .store
.a_add:
    mov rax, r13
    add rax, r14
    mov r14, rax
    jmp .store
.a_sub:
    mov rax, r13
    sub rax, r14
    mov r14, rax
    jmp .store
.a_mul:
    mov rax, r13
    imul rax, r14
    mov r14, rax
    jmp .store
.a_shl:
    mov rax, r13
    mov rcx, r14
    shl rax, cl
    mov r14, rax
    jmp .store
.a_shr:
    mov rax, r13
    mov rcx, r14
    shr rax, cl
    mov r14, rax
    jmp .store
.a_band:
    mov rax, r13
    and rax, r14
    mov r14, rax
.store:
    mov rcx, rbx
    mov rdx, r14
    call store_scalar
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.zeroargs:
    lea rax, [callargs]
    mov qword [rax], 0
    mov qword [rax+8], 0
    mov qword [rax+16], 0
    mov qword [rax+24], 0
    mov qword [rax+32], 0
    mov qword [rax+40], 0
    mov qword [rax+48], 0
    mov qword [rax+56], 0
    ret

; goto NAME
st_goto:
    call expect_word
    mov rcx, rax
    call sym_find
    test rax, rax
    jz unknown_error
    cmp qword [rax+16], 4
    jne unknown_error
    mov rax, [rax+24]
    mov [cur], rax
    mov rcx, rax
    call line_of
    mov [lineno], rax
    ret

; when zero|nonzero|negative X goto NAME
st_when:
    push rbx
    mov rcx, [cur]
    lea rdx, [kw_zero]
    call tok_is
    test eax, eax
    jnz .cz
    mov rcx, [cur]
    lea rdx, [kw_nonzero]
    call tok_is
    test eax, eax
    jnz .cn
    mov rcx, [cur]
    lea rdx, [kw_negative]
    call tok_is
    test eax, eax
    jnz .cg
    jmp syntax_error
.cz:
    xor ebx, ebx
    jmp .have
.cn:
    mov ebx, 1
    jmp .have
.cg:
    mov ebx, 2
.have:
    inc qword [cur]
    mov rcx, [cur]
    call operand
    inc qword [cur]
    cmp ebx, 0
    jne .c1
    test rax, rax
    jz .take
    jmp .notake
.c1:
    cmp ebx, 1
    jne .c2
    test rax, rax
    jnz .take
    jmp .notake
.c2:
    test rax, rax
    js .take
    jmp .notake
.take:
    mov rcx, [cur]
    lea rdx, [kw_goto]
    call tok_is
    test eax, eax
    jz syntax_error
    inc qword [cur]
    call st_goto
    pop rbx
    ret
.notake:
    call goto_newline
    pop rbx
    ret

; run: every line

; gosub NAME : remember the end of this line, then jump to the label
st_gosub:
    push rbx
    call expect_word
    mov rbx, rax
    call goto_newline
    mov rax, [retsp]
    cmp rax, MAXRET
    jge .deep
    mov rcx, [cur]
    lea rdx, [retstack]
    mov [rdx+rax*8], rcx
    inc qword [retsp]
    mov rcx, rbx
    call sym_find
    test rax, rax
    jz unknown_error
    cmp qword [rax+16], 4
    jne unknown_error
    mov rax, [rax+24]
    mov [cur], rax
    mov rcx, rax
    call line_of
    mov [lineno], rax
    pop rbx
    ret
.deep:
    lea rcx, [msg_deep]
    mov edx, msg_deep_len
    jmp fail

; return : back to the line after the last gosub
st_return:
    mov rax, [retsp]
    test rax, rax
    jz .none
    dec rax
    mov [retsp], rax
    lea rdx, [retstack]
    mov rcx, [rdx+rax*8]
    mov [cur], rcx
    call line_of
    mov [lineno], rax
    ret
.none:
    lea rcx, [msg_noret]
    mov edx, msg_noret_len
    jmp fail

; ============================================================ the loop over lines
%macro STMT 2                   ; if the word at cur is %1, jump to %2
    mov rcx, [cur]
    lea rdx, [%1]
    call tok_is
    test eax, eax
    jnz %2
%endmacro

%macro HANDLE 2                 ; %1 = local label, %2 = handler
%1:
    inc qword [cur]
    call %2
    jmp .end_line
%endmacro

run:
    push rbx
    mov qword [cur], 0
    mov qword [lineno], 1
    mov qword [retsp], 0
    mov rax, [arena]
    mov [arena_base], rax
    mov rax, [titleptr]
    mov [orig_title], rax
    mov qword [chap_argtok], -1
    mov qword [top_proch], 0
    xor ecx, ecx
    call scan_labels
.line:
    mov rax, [cur]
    cmp rax, [ntok]
    jge .done
    cmp rax, [prog_end]         ; the program ends where its libraries begin
    je .done
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 3
    je .empty
    call trace_line
    inc qword [stmts_run]
    STMT kw_space, .space
    STMT kw_vector, .vector
    STMT kw_map, .map
    STMT kw_let, .let
    STMT kw_show, .show
    STMT kw_check, .check
    STMT kw_extern, .extern
    STMT kw_blob, .blob
    STMT kw_set, .set
    STMT kw_poke, .poke
    STMT kw_label, .label
    STMT kw_goto, .goto
    STMT kw_gosub, .gosub
    STMT kw_return, .return
    STMT kw_load, .load
    STMT kw_save, .save
    STMT kw_say, .say
    STMT kw_process, .process
    STMT kw_chapter, .chapter
    STMT kw_use, .use
    STMT kw_push, .push
    STMT kw_pop, .pop
    STMT kw_library, .library
    STMT kw_record, .record
    STMT kw_when, .when
    STMT kw_arena, .arena
    STMT kw_trace, .trace
    STMT kw_claim, .claim
    STMT kw_established, .established
    STMT kw_text, .text
    STMT kw_read, .read
    STMT kw_write, .write
    STMT kw_net, .net
    STMT kw_print, .print
    STMT kw_append, .append
    jmp syntax_error
    HANDLE .space, st_space
    HANDLE .vector, st_vector
    HANDLE .map, st_map
    HANDLE .let, st_let
    HANDLE .show, st_show
    HANDLE .check, st_check
    HANDLE .extern, st_extern
    HANDLE .blob, st_blob
    HANDLE .set, st_set
    HANDLE .poke, st_poke
    HANDLE .label, goto_newline
    HANDLE .goto, st_goto
    HANDLE .gosub, st_gosub
    HANDLE .return, st_return
    HANDLE .load, st_load
    HANDLE .save, st_save
    HANDLE .say, st_say
    HANDLE .process, st_process
    HANDLE .chapter, st_chapter
    HANDLE .use, st_use
    HANDLE .push, st_push
    HANDLE .pop, st_pop
    HANDLE .library, st_use
    HANDLE .record, st_record
    HANDLE .when, st_when
    HANDLE .arena, st_arena
    HANDLE .trace, st_trace
    HANDLE .claim, st_claim
    HANDLE .established, st_established
    HANDLE .text, st_text
    HANDLE .read, st_read
    HANDLE .write, st_write
    HANDLE .net, st_net
    HANDLE .print, st_print
    HANDLE .append, st_append
.end_line:
    mov rcx, [cur]
    call tok_ptr
    cmp qword [rax+16], 3
    jne syntax_error
.empty:
    call skip_line
    jmp .line
.done:
    call trace_end
    pop rbx
    ret

; ============================================================ files and the entry point
; read_file_w(rcx = UTF-16 path) -> rax = bytes (in the arena), rdx = length; rax = 0 when the file cannot be opened
read_file_w:
    push rbp
    mov rbp, rsp
    push rbx
    push r12
    and rsp, -16
    sub rsp, 96
    mov edx, 0x80000000         ; GENERIC_READ
    mov r8d, 1                  ; FILE_SHARE_READ
    xor r9d, r9d
    mov qword [rsp+32], 3       ; OPEN_EXISTING
    mov qword [rsp+40], 0x80
    mov qword [rsp+48], 0
    call CreateFileW
    cmp rax, -1
    je .none
    mov rbx, rax
    mov rcx, rbx
    lea rdx, [rsp+64]
    call GetFileSizeEx          ; the buffer is sized by the file, not a fixed 64 MB
    mov rcx, [rsp+64]
    inc rcx
    call alloc
    mov r12, rax
    mov rcx, rbx
    mov rdx, rax
    mov r8, [rsp+64]
    lea r9, [rsp+56]
    mov qword [rsp+32], 0
    mov qword [rsp+56], 0
    call ReadFile
    mov rcx, rbx
    call CloseHandle
    mov rax, r12
    mov edx, [rsp+56]
    jmp .out
.none:
    xor eax, eax
    xor edx, edx
.out:
    lea rsp, [rbp-16]
    pop r12
    pop rbx
    pop rbp
    ret

; write_all(rcx = handle, rdx = bytes, r8 = length)
write_all:
    sub rsp, 56
    lea r9, [rsp+48]
    mov qword [rsp+32], 0
    call WriteFile
    add rsp, 56
    ret

start:
    sub rsp, 120
    mov ecx, -11
    call GetStdHandle
    mov [hstdout], rax
    ; the arena: 1 GB, committed lazily by Windows
    xor ecx, ecx
    mov rdx, ARENA
    mov r8d, 0x3000             ; MEM_COMMIT | MEM_RESERVE
    mov r9d, 4                  ; PAGE_READWRITE
    call VirtualAlloc
    test rax, rax
    jz .fail
    mov [arena], rax
    add rax, ARENA
    mov [arena_end], rax
    call init_constants
    ; this executable's own image, for the trailer check and for emit
    xor ecx, ecx
    lea rdx, [wbuf]
    mov r8d, 32767
    call GetModuleFileNameW
    lea rcx, [wbuf]
    call read_file_w
    mov [selfptr], rax
    mov [selflen], rdx
    ; the command line
    call GetCommandLineW
    mov rcx, rax
    lea rdx, [wargc]
    call CommandLineToArgvW
    test rax, rax
    jz .usage
    mov rbx, rax                ; argv
    ; a program embedded by emit? the file ends with [program][length][MAGIC]
    mov rax, [selflen]
    cmp rax, 16
    jb .notembedded
    mov rcx, [selfptr]
    mov rdx, [rcx+rax-8]
    mov r8, MAGIC
    cmp rdx, r8
    jne .notembedded
    mov r8, [rcx+rax-16]
    mov [srclen], r8
    sub rax, 16
    sub rax, r8
    add rax, rcx
    mov [srcptr], rax
    mov qword [titleptr], 0
    mov eax, [wargc]
    cmp eax, 2
    jl .go
    mov rax, [rbx+8]
    mov [titleptr], rax
    jmp .go
.notembedded:
    mov eax, [wargc]
    cmp eax, 2
    jl .usage
    ; "emit program.pmp output.exe"?
    mov rax, [rbx+8]
    lea rcx, [wemit]
    mov rdx, [rax]
    cmp rdx, [rcx]
    jne .interpret
    cmp word [rax+8], 0
    jne .interpret
    mov eax, [wargc]
    cmp eax, 4
    jl .usage
    jmp .emit
.interpret:
    mov rax, [rbx+8]
    mov [wpath], rax
    mov qword [titleptr], 0
    mov eax, [wargc]
    cmp eax, 3
    jl .haveargs
    mov rax, [rbx+16]
    mov [titleptr], rax
.haveargs:
    mov rcx, [wpath]
    call read_file_w
    test rax, rax
    jz .nofile
    mov [srcptr], rax
    mov [srclen], rdx
.go:
    call flatten_uses
    call tokenize
    call find_prog_end
    call run
    call emit_flush
    xor ecx, ecx
    call ExitProcess
.emit:
    mov rcx, [rbx+16]
    call read_file_w
    test rax, rax
    jz .nofile
    mov [srcptr], rax           ; the program with its libraries appended
    mov [srclen], rdx
    mov rax, [rbx+16]
    mov [wpath], rax
    call flatten_uses
    mov rax, [srcptr]
    mov rdx, [srclen]
    mov [rsp+88], rax           ; the program
    mov [rsp+96], rdx
    mov rcx, [rbx+24]
    mov edx, 0x40000000         ; GENERIC_WRITE
    xor r8d, r8d
    xor r9d, r9d
    mov qword [rsp+32], 2       ; CREATE_ALWAYS
    mov qword [rsp+40], 0x80
    mov qword [rsp+48], 0
    call CreateFileW
    cmp rax, -1
    je .nowrite
    mov [rsp+104], rax
    mov rcx, rax
    mov rdx, [selfptr]
    mov r8, [selflen]
    call write_all
    mov rcx, [rsp+104]
    mov rdx, [rsp+88]
    mov r8, [rsp+96]
    call write_all
    mov rax, [rsp+96]
    mov [rsp+64], rax
    mov rax, MAGIC
    mov [rsp+72], rax
    mov rcx, [rsp+104]
    lea rdx, [rsp+64]
    mov r8d, 16
    call write_all
    mov rcx, [rsp+104]
    call CloseHandle
    mov rcx, [rbx+24]
    call emit_utf16
    mov cl, ':'
    call emit_char
    mov cl, ' '
    call emit_char
    mov rcx, [selflen]
    add rcx, [rsp+96]
    add rcx, 16
    call emit_int
    lea rcx, [msg_bytes]
    mov edx, msg_bytes_len
    call emit_str
    call emit_flush
    xor ecx, ecx
    call ExitProcess
.usage:
    lea rcx, [msg_usage]
    mov edx, msg_usage_len
    call emit_str
    call emit_flush
    mov ecx, 1
    call ExitProcess
.nofile:
    lea rcx, [msg_nofile]
    mov edx, msg_nofile_len
    call emit_str
    call emit_flush
    mov ecx, 2
    call ExitProcess
.nowrite:
    lea rcx, [msg_nowrite]
    mov edx, msg_nowrite_len
    call emit_str
    call emit_flush
    mov ecx, 2
    call ExitProcess
.fail:
    mov ecx, 3
    call ExitProcess
