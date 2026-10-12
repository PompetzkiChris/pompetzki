(* Parse.v - the kernel's formula texts (lib/zfc.pmp ZF_EXPAND): prefix notation, tokens separated by spaces;
   N a, I a b, A v a, E x y, = x y, and the abbreviations K a b = N I a N b, D a b = I N a b, Q a b = N I I a b N I b a,
   X v a = N A v N a; a predicate token begins with a capital letter and ends with its arity (one digit), followed by
   that many variables. Variables are resolved against the binders (innermost first) and then the free variables given;
   predicate names against a symbol table (their number is their position). *)
From Stdlib Require Import List Arith Bool PeanoNat String Ascii.
From Cohen Require Import Syn.
Import ListNotations.
Open Scope string_scope.

Fixpoint split_sp (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c r =>
      if Ascii.eqb c " "%char then EmptyString :: split_sp r
      else match split_sp r with
           | w :: ws => String c w :: ws
           | [] => [String c EmptyString]
           end
  end.

Definition toks (s : string) : list string := filter (fun w => negb (String.eqb w EmptyString)) (split_sp s).

Fixpoint idx (x : string) (l : list string) : option nat :=
  match l with
  | [] => None
  | y :: l' => if String.eqb x y then Some O else option_map S (idx x l')
  end.

Definition is_upper (c : ascii) : bool := let n := nat_of_ascii c in ((65 <=? n) && (n <=? 90))%nat.

Definition last_digit (s : string) : option nat :=
  match get (String.length s - 1)%nat s with
  | Some c => let n := nat_of_ascii c in if ((48 <=? n) && (n <=? 57))%nat then Some (n - 48)%nat else None
  | None => None
  end.

Fixpoint take_vars (k : nat) (ctx : list string) (ts : list string) : option (list nat * list string) :=
  match k with
  | O => Some ([], ts)
  | S k' =>
      match ts with
      | [] => None
      | t :: r =>
          match idx t ctx, take_vars k' ctx r with
          | Some i, Some (l, r') => Some (i :: l, r')
          | _, _ => None
          end
      end
  end.

Fixpoint parse (fuel : nat) (tab ctx : list string) (ts : list string) : option (form * list string) :=
  match fuel with
  | O => None
  | S fu =>
      let two (mk : form -> form -> form) (r : list string) :=
        match parse fu tab ctx r with
        | Some (a, r1) => match parse fu tab ctx r1 with Some (b, r2) => Some (mk a b, r2) | None => None end
        | None => None
        end in
      match ts with
      | [] => None
      | t :: r =>
          if String.eqb t "N" then
            match parse fu tab ctx r with Some (a, r1) => Some (Neg a, r1) | None => None end
          else if String.eqb t "I" then two Imp r
          else if String.eqb t "K" then two Kf r
          else if String.eqb t "D" then two Df r
          else if String.eqb t "Q" then two Qf r
          else if String.eqb t "A" then
            match r with
            | v :: r1 => match parse fu tab (v :: ctx) r1 with Some (a, r2) => Some (All a, r2) | None => None end
            | [] => None
            end
          else if String.eqb t "X" then
            match r with
            | v :: r1 => match parse fu tab (v :: ctx) r1 with Some (a, r2) => Some (Xf a, r2) | None => None end
            | [] => None
            end
          else if String.eqb t "E" then
            match r with
            | x :: y :: r1 => match idx x ctx, idx y ctx with Some i, Some j => Some (Mem i j, r1) | _, _ => None end
            | _ => None
            end
          else if String.eqb t "=" then
            match r with
            | x :: y :: r1 => match idx x ctx, idx y ctx with Some i, Some j => Some (Eqv i j, r1) | _, _ => None end
            | _ => None
            end
          else
            match get 0%nat t, last_digit t, idx t tab with
            | Some c, Some k, Some p =>
                if is_upper c then
                  match take_vars k ctx r with Some (a, r1) => Some (Pr p a, r1) | None => None end
                else None
            | _, _, _ => None
            end
      end
  end.

(* a whole text as one formula with the free variables frees (frees at 0, 1, ..) *)
Definition pstmt (tab frees : list string) (s : string) : option form :=
  let ts := toks s in
  match parse (S (List.length ts)) tab frees ts with
  | Some (f, []) => Some f
  | _ => None
  end.
