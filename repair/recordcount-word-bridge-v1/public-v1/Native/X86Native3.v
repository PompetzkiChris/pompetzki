(* CX4: integer-only operational semantics for the L4 native judge subset. *)
From Stdlib Require Import ZArith List Bool Lia FMapAVL OrderedTypeEx.
Import ListNotations.
Open Scope Z_scope.
Module ByteMap := FMapAVL.Make(Z_as_OT).
Definition W64 : Z := 18446744073709551616.
Definition w64 (x : Z) : Z := x mod W64.
Definition w8 (x : Z) : Z := x mod 256.
Definition signed64 (x : Z) : Z := if w64 x <? 9223372036854775808 then w64 x else w64 x - W64.
Definition sext (bits : Z) (x : Z) : Z := if x <? 2^(bits-1) then x else x-2^bits.
Inductive reg := RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
 | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15.
Definition reg_eqb (x y : reg) : bool :=
 match x,y with
 | RAX,RAX | RCX,RCX | RDX,RDX | RBX,RBX | RSP,RSP | RBP,RBP | RSI,RSI | RDI,RDI
 | R8,R8 | R9,R9 | R10,R10 | R11,R11 | R12,R12 | R13,R13 | R14,R14 | R15,R15 => true
 | _,_ => false end.
Definition regs := reg -> Z.
Definition setreg (rs : regs) (r : reg) (v : Z) : regs :=
 fun q => if reg_eqb q r then w64 v else rs q.
Record flags := Flags { cf : option bool; pf : option bool; af : option bool;
                       zf : option bool; sf : option bool; ofl : option bool }.
Record region := Region { lo : Z; hi : Z; readable : bool; writable : bool; executable : bool }.
Record memory := Memory { cells : ByteMap.t Z; regions : list region }.
Definition canonical (a : Z) : bool :=
 (0 <=? a) && (a <? W64) && ((a <? 140737488355328) || (18446603336221196288 <=? a)).
Definition allowed (perm : region -> bool) (m : memory) (a : Z) : bool :=
 canonical a && existsb (fun r => perm r && (lo r <=? a) && (a <? hi r)) (regions m).
Definition readbyte (m : memory) (a : Z) : option Z :=
 if allowed readable m a then Some (w8 (match ByteMap.find a (cells m) with Some b => b | None => 0 end)) else None.
Definition writebyte (m : memory) (a b : Z) : option memory :=
 if allowed writable m a then Some (Memory (ByteMap.add a (w8 b) (cells m)) (regions m)) else None.
Fixpoint loadn (n : nat) (m : memory) (a : Z) : option Z :=
 match n with
 | O => Some 0
 | S k => match readbyte m a, loadn k m (a+1) with
          | Some b, Some v => Some (b+256*v) | _,_ => None end end.
Fixpoint storen (n : nat) (m : memory) (a v : Z) : option memory :=
 match n with
 | O => Some m
 | S k => match writebyte m a v with
          | Some m' => storen k m' (a+1) (v/256) | None => None end end.
Record machine := Machine { registers : regs; rip : Z; status : flags;
                            rflags_other : Z; mem : memory }.
Definition getreg (s : machine) (r : reg) : Z := w64 (registers s r).
Definition updreg (s : machine) (r : reg) (v : Z) : machine :=
 Machine (setreg (registers s) r v) (rip s) (status s) (rflags_other s) (mem s).
Definition updmem (s : machine) (m : memory) : machine :=
 Machine (registers s) (rip s) (status s) (rflags_other s) m.
Definition updflags (s : machine) (f : flags) : machine :=
 Machine (registers s) (rip s) f (rflags_other s) (mem s).
Definition updpc (s : machine) (p : Z) : machine :=
 Machine (registers s) (w64 p) (status s) (rflags_other s) (mem s).
Inductive address := BaseDisp (r : reg) (d : Z) | Absolute (a : Z).
Definition ea (s : machine) (a : address) : Z :=
 match a with BaseDisp r d => w64 (getreg s r+d) | Absolute a => w64 a end.
Inductive operand := RegVal (r : reg) | ImmVal (n : Z).
Definition val (s : machine) (v : operand) : Z :=
 match v with RegVal r => getreg s r | ImmVal n => w64 n end.
Inductive alu := Add | Sub | Mul | And | Xor | Shl | Shr.
Inductive condition := Below | AboveEqual | Equal | NotEqual | BelowEqual | Above.
Inductive instruction :=
 | Push (r : reg) | Pop (r : reg) | MovRR (dst src : reg) | MovImm (dst : reg) (v : Z)
 | Load (dst : reg) (a : address) (n : nat)
 | Store (a : address) (src : reg) (n : nat)
 | ALU (op : alu) (dst : reg) (src : operand)
 | Compare (dst : reg) (src : operand) | Test (left right : reg)
 | Jmp (d : Z) | Jcc (c : condition) (d : Z) | Call (d : Z) | Ret (n : Z) | Syscall.
Definition byte_ok (x : Z) : bool := (0 <=? x) && (x <? 256).
Fixpoint immediate (n : nat) (bs : list Z) : option (Z * list Z) :=
 match n,bs with
 | O,_ => Some (0,bs)
 | S k,b::rest => if byte_ok b then
     match immediate k rest with Some (v,tail) => Some (b+256*v,tail) | None => None end
   else None
 | _,_ => None end.
Definition decoded := (instruction * nat * list Z)%type.
Definition immdec (n len : nat) (signed : bool) (make : Z -> instruction) (bs : list Z) : option decoded :=
 match immediate n bs with
 | Some (v,tail) => Some (make (if signed then sext (8*Z.of_nat n) v else v),len,tail)
 | None => None end.
Definition decode (bs : list Z) : option decoded :=
 match bs with
 | 80::t => Some (Push RAX,1%nat,t)
 | 85::t => Some (Push RBP,1%nat,t)
 | 88::t => Some (Pop RAX,1%nat,t)
 | 89::t => Some (Pop RCX,1%nat,t)
 | 93::t => Some (Pop RBP,1%nat,t)
 | 94::t => Some (Pop RSI,1%nat,t)
 | 95::t => Some (Pop RDI,1%nat,t)
 | 72::199::192::t => immdec 4 7 true (MovImm RAX) t
 | 72::184::t => immdec 8 10 false (MovImm RAX) t
 | 72::185::t => immdec 8 10 false (MovImm RCX) t
 | 72::137::193::t => Some (MovRR RCX RAX,3%nat,t)
 | 72::137::229::t => Some (MovRR RBP RSP,3%nat,t)
 | 72::137::236::t => Some (MovRR RSP RBP,3%nat,t)
 | 72::137::196::t => Some (MovRR RSP RAX,3%nat,t)
 | 72::137::194::t => Some (MovRR RDX RAX,3%nat,t)
 | 72::139::133::t => immdec 4 7 true (fun d => Load RAX (BaseDisp RBP d) 8) t
 | 72::137::133::t => immdec 4 7 true (fun d => Store (BaseDisp RBP d) RAX 8) t
 | 72::139::4::37::t => immdec 4 8 true (fun d => Load RAX (Absolute d) 8) t
 | 72::137::4::37::t => immdec 4 8 true (fun d => Store (Absolute d) RAX 8) t
 | 72::139::0::t => Some (Load RAX (BaseDisp RAX 0) 8,3%nat,t)
 | 72::15::182::0::t => Some (Load RAX (BaseDisp RAX 0) 1,4%nat,t)
 | 72::137::1::t => Some (Store (BaseDisp RCX 0) RAX 8,3%nat,t)
 | 136::1::t => Some (Store (BaseDisp RCX 0) RAX 1,2%nat,t)
 | 72::139::128::t => immdec 4 7 true (fun d => Load RAX (BaseDisp RAX d) 8) t
 | 72::137::129::t => immdec 4 7 true (fun d => Store (BaseDisp RCX d) RAX 8) t
 | 72::1::200::t => Some (ALU Add RAX (RegVal RCX),3%nat,t)
 | 72::41::200::t => Some (ALU Sub RAX (RegVal RCX),3%nat,t)
 | 72::15::175::193::t => Some (ALU Mul RAX (RegVal RCX),4%nat,t)
 | 72::33::200::t => Some (ALU And RAX (RegVal RCX),3%nat,t)
 | 72::49::200::t => Some (ALU Xor RAX (RegVal RCX),3%nat,t)
 | 72::211::224::t => Some (ALU Shl RAX (RegVal RCX),3%nat,t)
 | 72::211::232::t => Some (ALU Shr RAX (RegVal RCX),3%nat,t)
 | 72::5::t => immdec 4 6 true (fun v => ALU Add RAX (ImmVal v)) t
 | 72::129::236::t => immdec 4 7 true (fun v => ALU Sub RSP (ImmVal v)) t
 | 72::133::192::t => Some (Test RAX RAX,3%nat,t)
 | 72::57::193::t => Some (Compare RCX (RegVal RAX),3%nat,t)
 | 72::57::204::t => Some (Compare RSP (RegVal RCX),3%nat,t)
 | 72::61::t => immdec 4 6 true (fun v => Compare RAX (ImmVal v)) t
 | 233::t => immdec 4 5 true Jmp t
 | 232::t => immdec 4 5 true Call t
 | 15::130::t => immdec 4 6 true (Jcc Below) t
 | 15::131::t => immdec 4 6 true (Jcc AboveEqual) t
 | 15::132::t => immdec 4 6 true (Jcc Equal) t
 | 15::133::t => immdec 4 6 true (Jcc NotEqual) t
 | 15::134::t => immdec 4 6 true (Jcc BelowEqual) t
 | 15::135::t => immdec 4 6 true (Jcc Above) t
 | 194::t => immdec 2 3 false Ret t
 | 15::5::t => Some (Syscall,2%nat,t)
 | _ => None end.
Fixpoint decode_stream (fuel : nat) (bs : list Z) : option (list (instruction * nat)) :=
 match bs with [] => Some [] | _ =>
 match fuel with O => None | S k =>
 match decode bs with Some (i,n,rest) =>
 match decode_stream k rest with Some is => Some ((i,n)::is) | None => None end
 | None => None end end end.
Definition msb (x : Z) : bool := Z.testbit (w64 x) 63.
Definition parity (x : Z) : bool :=
 negb (fold_left xorb (map (fun i => Z.testbit x (Z.of_nat i)) (seq 0 8)) false).
Definition auxcarry (a b r : Z) : bool := Z.testbit (Z.lxor (Z.lxor a b) r) 4.
Definition resultflags (c a o : option bool) (r : Z) : flags :=
 Flags c (Some (parity r)) a (Some (Z.eqb (w64 r) 0)) (Some (msb r)) o.
Definition addflags (a b : Z) : flags :=
 let r := w64 (a+b) in resultflags (Some (W64 <=? a+b)) (Some (auxcarry a b r))
 (Some (negb (xorb (msb a) (msb b)) && xorb (msb a) (msb r))) r.
Definition subflags (a b : Z) : flags :=
 let r := w64 (a-b) in resultflags (Some (a <? b)) (Some (auxcarry a b r))
 (Some (xorb (msb a) (msb b) && xorb (msb a) (msb r))) r.
Definition logicflags (r : Z) : flags := resultflags (Some false) None (Some false) r.
Definition mulflags (a b : Z) : flags :=
 let p := signed64 a * signed64 b in
 let overflow := negb (Z.eqb (signed64 p) p) in
 Flags (Some overflow) None None None None (Some overflow).
Definition shiftflags (left : bool) (f : flags) (a count : Z) : flags :=
 let k := count mod 64 in
 if k =? 0 then f else
 let r := w64 (if left then Z.shiftl a k else Z.shiftr a k) in
 let c := Z.testbit a (if left then 64-k else k-1) in
 resultflags (Some c) None
 (if k =? 1 then Some (if left then xorb (msb r) c else msb a) else None) r.
Definition aluvalue (op : alu) (a b : Z) : Z := w64
 (match op with Add => a+b | Sub => a-b | Mul => a*b
 | And => Z.land a b | Xor => Z.lxor a b
 | Shl => Z.shiftl a (b mod 64) | Shr => Z.shiftr a (b mod 64) end).
Definition aluflags (op : alu) (f : flags) (a b : Z) : flags :=
 match op with Add => addflags a b | Sub => subflags a b | Mul => mulflags a b
 | And | Xor => logicflags (aluvalue op a b)
 | Shl => shiftflags true f a b | Shr => shiftflags false f a b end.
Definition optnot (b : option bool) := option_map negb b.
Definition optor (a b : option bool) : option bool :=
 match a,b with Some true,_ | _,Some true => Some true | Some false,Some false => Some false | _,_ => None end.
Definition condition_value (c : condition) (f : flags) : option bool :=
 match c with Below => cf f | AboveEqual => optnot (cf f)
 | Equal => zf f | NotEqual => optnot (zf f)
 | BelowEqual => optor (cf f) (zf f) | Above => optnot (optor (cf f) (zf f)) end.
Definition pushvalue (s : machine) (v : Z) : option machine :=
 let a := w64 (getreg s RSP-8) in
 match storen 8 (mem s) a v with
 | Some m => Some (updreg (updmem s m) RSP a) | None => None end.
Definition popvalue (s : machine) : option (Z * machine) :=
 match loadn 8 (mem s) (getreg s RSP) with
 | Some v => Some (v,updreg s RSP (getreg s RSP+8)) | None => None end.
Inductive outcome := Continue (s : machine) | EnterKernel (s : machine).
Definition branch_to (s : machine) (p : Z) : option outcome :=
 if canonical (w64 p) then Some (Continue (updpc s p)) else None.
Definition execute (i : instruction) (len : nat) (s : machine) : option outcome :=
 let next := w64 (rip s+Z.of_nat len) in
 let finish := fun t => Some (Continue (updpc t next)) in
 match i with
 | Push r => match pushvalue s (getreg s r) with Some t => finish t | None => None end
 | Pop r => match popvalue s with Some (v,t) => finish (updreg t r v) | None => None end
 | MovRR d r => finish (updreg s d (getreg s r))
 | MovImm d v => finish (updreg s d v)
 | Load d a n => match loadn n (mem s) (ea s a) with Some v => finish (updreg s d v) | None => None end
 | Store a r n => match storen n (mem s) (ea s a) (getreg s r) with Some m => finish (updmem s m) | None => None end
 | ALU op d src => let a := getreg s d in let b := val s src in
   finish (updflags (updreg s d (aluvalue op a b)) (aluflags op (status s) a b))
 | Compare d src => finish (updflags s (subflags (getreg s d) (val s src)))
 | Test a b => finish (updflags s (logicflags (Z.land (getreg s a) (getreg s b))))
 | Jmp d => branch_to s (next+d)
 | Jcc c d => match condition_value c (status s) with
     Some b => if b then branch_to s (next+d) else Some (Continue (updpc s next)) | None => None end
 | Call d => match pushvalue s next with Some t => branch_to t (next+d) | None => None end
 | Ret n => match popvalue s with Some (v,t) => branch_to (updreg t RSP (getreg t RSP+n)) v | None => None end
 | Syscall => Some (EnterKernel (updpc s next)) end.
(* Undefined status bits are resolved by a relation; None never means false. *)
Definition agrees (b : option bool) (v : bool) : Prop := match b with Some x => x=v | None => True end.
Definition resolves (f : flags) (v : Z) : Prop :=
 agrees (cf f) (Z.testbit v 0) /\ agrees (pf f) (Z.testbit v 2) /\
 agrees (af f) (Z.testbit v 4) /\ agrees (zf f) (Z.testbit v 6) /\
 agrees (sf f) (Z.testbit v 7) /\ agrees (ofl f) (Z.testbit v 11).
Definition concrete_flags (v : Z) : flags := Flags (Some (Z.testbit v 0)) (Some (Z.testbit v 2))
 (Some (Z.testbit v 4)) (Some (Z.testbit v 6)) (Some (Z.testbit v 7)) (Some (Z.testbit v 11)).
Definition status_mask : Z := 2261.
Definition resolves_rflags (s : machine) (v : Z) : Prop :=
 0 <= v < W64 /\ resolves (status s) v /\
 Z.land v (Z.lnot status_mask) = Z.land (rflags_other s) (Z.lnot status_mask).
Definition kernel_clobber (s : machine) (rf : Z) : machine :=
 updreg (updreg (updflags s (concrete_flags rf)) RCX (rip s)) R11 rf.
Fixpoint readbytes (n : nat) (m : memory) (a : Z) : option (list Z) :=
 match n with O => Some [] | S k => match readbyte m a,readbytes k m (a+1) with
 Some b,Some bs => Some (b::bs) | _,_ => None end end.
Fixpoint writebytes (bs : list Z) (m : memory) (a : Z) : option memory :=
 match bs with [] => Some m | b::bs => if byte_ok b then
 match writebyte m a b with Some m' => writebytes bs m' (a+1) | None => None end else None end.
Inductive io_event := ReadEvent (bs : list Z) | WriteEvent (bs : list Z)
 | ErrorEvent (nr fd err : Z) | ExitEvent (code : Z).
Inductive linux_step : machine -> io_event -> option machine -> Prop :=
 | LinuxRead s rf bs m : resolves_rflags s rf -> getreg s RAX=0 -> getreg s RDI=0 ->
   Z.of_nat (length bs) <= getreg s RDX -> Z.of_nat (length bs) < 9223372036854775808 ->
   writebytes bs (mem s) (getreg s RSI)=Some m ->
   linux_step s (ReadEvent bs) (Some (updreg (updmem (kernel_clobber s rf) m) RAX (Z.of_nat (length bs))))
 | LinuxWrite s rf n bs : resolves_rflags s rf -> getreg s RAX=1 -> getreg s RDI=1 ->
   Z.of_nat n <= getreg s RDX -> Z.of_nat n < 9223372036854775808 ->
   readbytes n (mem s) (getreg s RSI)=Some bs ->
   linux_step s (WriteEvent bs) (Some (updreg (kernel_clobber s rf) RAX (Z.of_nat n)))
 | LinuxError s rf err : resolves_rflags s rf -> (getreg s RAX=0 \/ getreg s RAX=1) ->
   -4095 <= err < 0 -> linux_step s (ErrorEvent (getreg s RAX) (getreg s RDI) err)
     (Some (updreg (kernel_clobber s rf) RAX err))
 | LinuxExit s : getreg s RAX=60 -> linux_step s (ExitEvent (getreg s RDI mod 256)) None.
Fixpoint fetchbytes (n : nat) (m : memory) (a : Z) : list Z :=
 match n with O => [] | S k => if allowed executable m a then
 match readbyte m a with Some b => b::fetchbytes k m (a+1) | None => [] end else [] end.
Definition step (s : machine) : option outcome :=
 match decode (fetchbytes 15 (mem s) (rip s)) with
 | Some (i,n,_) => execute i n s | None => None end.
Inductive transition : machine -> option io_event -> option machine -> Prop :=
 | InternalStep s t : step s=Some (Continue t) -> transition s None (Some t)
 | ResolvedInternalStep s rf t : resolves_rflags s rf ->
   step (updflags s (concrete_flags rf))=Some (Continue t) -> transition s None (Some t)
 | SystemStep s k e t : step s=Some (EnterKernel k) -> linux_step k e t -> transition s (Some e) t.
Lemma w64_bounds x : 0 <= w64 x < W64.
Proof. apply Z.mod_pos_bound. unfold W64; lia. Qed.
Lemma setreg_same rs r v : setreg rs r v r = w64 v.
Proof. destruct r; reflexivity. Qed.
Lemma writebyte_regions m a b m' : writebyte m a b=Some m' -> regions m'=regions m.
Proof. unfold writebyte. destruct (allowed writable m a); intro H; inversion H; reflexivity. Qed.
Lemma storen_regions n m a v m' : storen n m a v=Some m' -> regions m'=regions m.
Proof. revert m a v m'; induction n; intros m a v m' H; simpl in H.
 - inversion H; reflexivity.
 - destruct (writebyte m a v) as [m1|] eqn:E; try discriminate.
   transitivity (regions m1); [eapply IHn; exact H|eapply writebyte_regions; exact E]. Qed.
Lemma compare_preserves_registers d v n s t : execute (Compare d v) n s=Some (Continue t) -> registers t=registers s.
Proof. simpl. intro H; inversion H; reflexivity. Qed.
Lemma mov_preserves_flags d r n s t : execute (MovRR d r) n s=Some (Continue t) -> status t=status s.
Proof. simpl. intro H; inversion H; reflexivity. Qed.
Lemma zero_shift_preserves_flags left f a : shiftflags left f a 0=f.
Proof. reflexivity. Qed.
Lemma decoder_functional bs i n rest j k tail :
 decode bs=Some(i,n,rest) -> decode bs=Some(j,k,tail) -> i=j /\ n=k /\ rest=tail.
Proof. intros A B; rewrite A in B; inversion B; auto. Qed.
Print Assumptions w64_bounds.
Print Assumptions storen_regions.
Print Assumptions decoder_functional.
