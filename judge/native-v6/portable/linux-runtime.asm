; Linux x64 syscall runtime for the direct core pmp compiler.
; Calls retain the compiler's rcx/rdx interface and preserve nonvolatile registers.
rt_frame_in:
    ret
rt_alloc:
    push rdi
    push rsi
    mov rsi, rcx
    test rsi, rsi
    jnz .size
    mov esi, 1
.size:
    xor edi, edi
    mov edx, 3
    mov r10d, 0x22
    mov r8, -1
    xor r9d, r9d
    mov eax, 9
    syscall
    pop rsi
    pop rdi
    cmp rax, -4095
    jb .ok
    lea rcx, [msg_alloc]
    mov rdx, msg_alloc_len
    call rt_line
    mov ecx, 2
    jmp rt_exit
.ok:
    ret
rt_out:
    push rsi
    push rdi
    mov rsi, rcx
    mov rax, [outpos]
    mov rcx, rax
    add rcx, rdx
    jc .fault
    cmp rcx, OUTSZ
    ja .fault
    mov [outpos], rcx
    lea rdi, [outbuf+rax]
    mov rcx, rdx
    rep movsb
    pop rdi
    pop rsi
    ret
.fault:
    pop rdi
    pop rsi
    mov ecx, 2
    jmp rt_exit
rt_line:
    call rt_out
    lea rcx, [nl]
    mov rdx, 1
    jmp rt_out
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
rt_flush:
    push rsi
    push rdi
    push rbx
    lea rsi, [outbuf]
    mov rbx, [outpos]
.write:
    test rbx, rbx
    jz .done
    mov eax, 1
    mov edi, 1
    mov rdx, rbx
    syscall
    cmp rax, -4
    je .write
    test rax, rax
    jle .done
    add rsi, rax
    sub rbx, rax
    jmp .write
.done:
    mov qword [outpos], 0
    pop rbx
    pop rdi
    pop rsi
    ret
rt_exit:
    push rcx
    call rt_flush
    pop rdi
    mov eax, 60
    syscall
    ud2
rt_checkfail:
    push rcx
    lea rcx, [msg_line]
    mov rdx, 5
    call rt_out
    pop rcx
    call rt_show_noline
    lea rcx, [msg_check]
    mov rdx, msg_check_len
    call rt_line
    mov ecx, 1
    jmp rt_exit
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
rt_arg:
    mov rax, [argv1]
    xor edx, edx
.len:
    cmp byte [rax+rdx], 0
    je .done
    inc rdx
    jmp .len
.done:
    ret
rt_read:
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    mov rsi, rcx
    cmp rdx, 4095
    ja .bad
    lea rdi, [pathbuf]
    mov rcx, rdx
    rep movsb
    mov byte [rdi], 0
    mov eax, 2
    lea rdi, [pathbuf]
    xor esi, esi
    xor edx, edx
    syscall
    test rax, rax
    js .bad
    mov rbx, rax
    mov eax, 8
    mov rdi, rbx
    xor esi, esi
    mov edx, 2
    syscall
    test rax, rax
    js .bad
    mov r13, rax
    lea rcx, [rax+1]
    call rt_alloc
    mov r12, rax
    mov eax, 8
    mov rdi, rbx
    xor esi, esi
    xor edx, edx
    syscall
    xor esi, esi
.read:
    cmp rsi, r13
    je .close
    mov rdx, r13
    sub rdx, rsi
    push rsi
    lea rsi, [r12+rsi]
    mov rdi, rbx
    xor eax, eax
    syscall
    pop rsi
    cmp rax, -4
    je .read
    test rax, rax
    jle .bad
    add rsi, rax
    jmp .read
.close:
    mov byte [r12+rsi], 0
    mov eax, 3
    mov rdi, rbx
    syscall
    mov rax, r12
    mov rdx, r13
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
    ret
.bad:
    lea rcx, [msg_open]
    mov rdx, msg_open_len
    call rt_line
    mov ecx, 2
    jmp rt_exit
