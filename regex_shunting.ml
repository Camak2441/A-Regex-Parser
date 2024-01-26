
type alternate = Alt of concat * alternate | S of concat
 and concat = Con of star * concat | S of star
 and star = Star of bracket | S of bracket
 and bracket = Bracket of regex | S of single
 and single = Char of char | Range of range
 and range = Single of char | Range of char * char | C_single of range * char | C_range of range * char * char
 and regex = R_alt of alternate | R_con of concat | R_star of star | R_brac of bracket| R_sing of single | Epsilon | Null;;

module RegSet = Set.Make (struct type t = regex let compare = compare end);;

let rec to_string = (function 
  | R_alt a      -> to_string_alt a
  | R_con c      -> to_string_con c
  | R_star s     -> to_string_star s
  | R_brac b  -> to_string_bracket b
  | R_sing s   -> to_string_single s
  | Epsilon       -> ""
  | Null          -> "{}")

and to_string_alt = (function
  | Alt (c, a)  -> to_string_con c ^ "|" ^ to_string_alt a 
  | S c   -> to_string_con c)

and to_string_con = (function
  | Con (s, c) -> to_string_star s ^ to_string_con c
  | S s  -> to_string_star s)

and to_string_star = (function
  | Star b      -> to_string_bracket b ^ "*"
  | S b  -> to_string_bracket b)

and to_string_bracket = (function
  | S s -> to_string_single s
  | Bracket r -> "(" ^ to_string r ^ ")")

and to_string_single = (function
  | Char c      -> String.make 1 c
  | Range r     -> "[" ^ to_string_range r ^ "]")

and to_string_range = (function
  | Single c        -> String.make 1 c
  | Range (s, e)    -> String.make 1 s ^ "-" ^ String.make 1 e
  | C_single (r, c)  -> to_string_range r ^ String.make 1 c
  | C_range (r, s, e)  -> to_string_range r ^ String.make 1 s ^ "-" ^ String.make 1 e);;

exception Convert_failure of string;;

let reg_to_alt r = match r with
  | R_alt a -> a
  | R_con c -> S c
  | R_star s -> S (S s)
  | R_brac b -> S (S (S b))
  | R_sing s -> S (S (S (S s)))
  | _ -> S (S (S (Bracket r)))

let reg_to_con r = match r with
  | R_con c -> c
  | R_star s -> S s
  | R_brac b -> S (S b)
  | R_sing s -> S (S (S s))
  | _ -> S (S (Bracket r))
  
let reg_to_star r = match r with
  | R_star s -> s
  | R_brac b -> (S b)
  | R_sing s -> (S (S s))
  | _ -> S (Bracket r);;

let reg_union r1 r2 = match (r1, r2) with 
  | (_, Null)     -> r1
  | (Null, _)     -> r2
  | _ -> R_alt(Alt(reg_to_con r1, reg_to_alt r2));;

let reg_concat r1 r2 = match (r1, r2) with 
  | (_, Null)     -> Null
  | (Null, _)     -> Null
  | (_, Epsilon)  -> r1
  | (Epsilon, _)  -> r2
  | _ -> R_con(Con(reg_to_star r1, reg_to_con r2));;

let rec reg_star r = match r with
  | R_alt a -> (match a with
    | Alt (a, c) -> R_star (Star (Bracket r))
    | S c -> reg_star (R_con c))
  | R_star s -> (match s with
    | Star b -> R_star s
    | S b -> R_star (Star b))
  | R_brac b -> R_star (Star b)
  | R_sing s -> R_star (Star (S s))
  | Epsilon -> Epsilon
  | Null -> Null
  | _ -> R_star(Star(Bracket r));

type reg_ret = { zero : bool; next : regex}

let rec match_regex r str = (input_match (Seq.fold_left (fun ret -> input_match ret.next) { zero = false; next = r } (String.to_seq str)).next '\x00').zero

and input_match r chr = (match r with
  | R_alt a   -> match_alt a chr
  | R_con c   -> match_con c chr
  | R_star s  -> match_star s chr
  | R_brac b  -> match_bracket b chr
  | R_sing s  -> match_single s chr
  | Epsilon   -> { zero = true; next = Null }
  | Null      -> { zero = false; next = Null })

and match_alt a chr = match a with
  | Alt (c, a)  -> 
    let cret = (match_con c chr) in
    let aret = (match_alt a chr) in 
    {
      zero = cret.zero || aret.zero; 
      next = reg_union cret.next aret.next 
    }
  | S c   -> match_con c chr

and match_con c chr = match c with
  | Con (s, c) -> 
    let sret = match_star s chr in
    if sret.zero
      then 
        let cret = match_con c chr in
        {
          zero = cret.zero; 
          next = (reg_union (reg_concat sret.next (R_con c)) (cret.next))
        }
      else {zero = false; next = reg_concat sret.next (R_con c)}
  | S s -> match_star s chr

and match_star s chr = match s with
  | Star b  -> 
    let bret = match_bracket b chr in
    { zero = true; next = reg_concat bret.next (R_star s)}
  | S b -> match_bracket b chr

and match_bracket b chr = match b with
  | S s  -> match_single s chr
  | Bracket r -> input_match r chr;

and match_single s chr = match s with
  | Char c  -> { zero = false; next = if c = chr then Epsilon else Null }
  | Range r -> { zero = false; next = if match_range r chr then Epsilon else Null }

and match_range r chr = match r with
  | Single c      -> c = chr
  | Range (s, e)  -> s <= chr && chr <= e
  | C_single (r, c)  -> (c = chr) || match_range r chr
  | C_range (r, s, e)  -> (s <= chr && chr <= e) || match_range r chr;;

type core_state = Start | Concat;;
type single_state = Range of core_state | Range_end of core_state;;
type parse_state = Core of core_state | Single of single_state | Esc of core_state | Esc_sing of single_state;;
type regex_op = Alt | Concat | Star | Bracket of core_state * regex list;;


let to_string_core_state = function | Start -> "Start" | Concat -> "Concat";;
let to_string_single_state = function 
  | Range s -> "Range(" ^ to_string_core_state s ^ ")" 
  | Range_end s -> "Range_end(" ^ to_string_core_state s ^ ")";;
let to_string_parse_state = function 
  | Core s -> to_string_core_state s
  | Single s -> to_string_single_state s
  | Esc s -> to_string_core_state s
  | Esc_sing s -> to_string_single_state s;;


let to_string_op = function
  | Alt -> "Alt"
  | Concat -> "Concat"
  | Star -> "Star"
  | Bracket (s, _) -> "Bracket(" ^ to_string_core_state s ^ ")";;

  
let precedence op = match op with
  | Alt -> 0
  | Concat -> 1
  | Star -> 2
  | Bracket _ -> 3;;

type parse_stack = {regs: regex list; ops: regex_op list; range: range option; state: parse_state};;

exception Invalid_regex of string;;
exception Parser_error of string;;

let comp g f = fun x -> (g (f x));;
let to_string_list conv x = 
  (String.of_seq (List.fold_left Seq.append (String.to_seq "[") (
    List.mapi (fun i x -> String.to_seq ((match i with | 0 -> "" | _ -> ", ") ^ (conv x))) x
  ))) ^ "]";;

let to_string_reg_stack = to_string_list to_string;;
let to_string_op_stack = to_string_list to_string_op;;

let print_reg_stack x = x |> to_string_reg_stack |> print_endline;;
let print_op_stack x = x |> to_string_op_stack |> print_endline;;

let to_string_stack x = 
  "regs: " ^ to_string_reg_stack x.regs ^ 
  "\nops: " ^ to_string_op_stack x.ops ^
  "\nrange: " ^ (match x.range with | Some r -> to_string_range r | None -> "()") ^
  "\nstate: " ^ to_string_parse_state x.state;;

let print_stack x = x |> to_string_stack |> print_endline;;

(*Stack is the stack state of the parser
  We have two stacks: one for the stack of regexes, and one for the stack of operators*)
let rec parse_char stack chr = match stack.state with
  | Core s -> (match chr with
    | '\\' -> {stack with state = Esc s}
    | '|' -> (match s with | Start -> stack | Concat -> add_op Alt {stack with state = Core Start})
    | '*' -> (match s with | Start -> raise (Invalid_regex "Star at the start of Regex") | Concat -> add_op Star stack)
    | '(' -> add_op (Bracket (s, stack.regs)) {stack with regs = []; state = Core Start}
    | ')' -> close_bracket stack
    | '[' -> (match stack.range with | Some _ -> raise (Parser_error "Uncleared range") | None -> {stack with state = Single (Range s)})
    | ']' -> raise (Invalid_regex"Mismatched bracket ]")
    | _ -> (match s with
      | Start -> Fun.id
      | Concat -> add_op Concat) {stack with regs = R_sing (Char chr) :: stack.regs; state = Core Concat})
  | Single s -> (match s with 
    | Range sr -> (match chr with
      | '\\' -> {stack with state = Esc_sing s}
      | '[' -> raise (Invalid_regex "Disallowed range within range")
      | ']' -> (match sr with
        | Start -> Fun.id
        | Concat -> add_op Concat) {
            regs = (match stack.range with | Some r -> R_sing (Range r) | None -> Null) :: stack.regs; 
            ops = stack.ops; 
            range = None; 
            state = Core Concat
          }
      | '-' -> {stack with state = Single (Range_end sr)}
      | _ -> {stack with range = Some (match stack.range with | Some r -> C_single (r, chr) | None -> Single chr); state = Single s})
    | Range_end sr -> (match chr with
      | '\\' -> {stack with state = Esc_sing s}
      | '[' -> raise (Invalid_regex "Disallowed range within range")
      | ']' -> raise (Invalid_regex "Char range ended without end char");
      | '-' -> raise (Invalid_regex "Char range started without finishing previous range")
      | _ -> (match stack.range with
        | Some r -> (match r with
          | Single c -> {stack with range = Some (Range (c, chr)); state = Single (Range sr)}
          | C_single (r, c) -> {stack with range = Some (C_range (r, c, chr)); state = Single (Range sr)}
          | _ -> raise (Invalid_regex "Char range started without start char"))
        | None -> raise (Invalid_regex "Char range started without start char"))))
  | Esc s -> {regs = R_sing (Char chr) :: stack.regs; range = stack.range; ops = stack.ops; state = Core Concat}
  | Esc_sing s -> (match s with
    | Range sr -> 
      {stack with range = Some  (match stack.range with | Some r -> C_single (r, chr) | None -> Single chr); state = Single s}
    | Range_end sr -> (match stack.range with
      | Some r -> (match r with
        | Single c -> {stack with range = Some (Range (c, chr)); state = Single (Range sr)}
        | C_single (r, c) -> {stack with range = Some (C_range (r, c, chr)); state = Single (Range sr)}
        | _ -> raise (Invalid_regex "Char range started without start char"))
      | None -> raise (Invalid_regex "Char range started without start char")))

and add_op op stack = if op = Star 
  then match stack.regs with
    | r::rt -> {stack with regs = reg_star r :: rt}
    | _ -> raise (Parser_error ("Missing arguments for star when adding " ^ to_string_op op))
  else
    match stack.ops with
    | x::xt -> (match precedence x > precedence op with
      | true -> (match x with
        | Alt -> (match stack.regs with
          | r2::r1::rt -> add_op op {stack with regs = reg_union r1 r2 :: rt; ops = xt}
          | _ -> raise (Parser_error ("Missing arguments for alt when adding " ^ to_string_op op)))
        | Concat -> (match stack.regs with
          | r2::r1::rt -> add_op op {stack with regs = reg_concat r1 r2 :: rt; ops = xt}
          | _ -> raise (Parser_error ("Missing arguments for concat when adding " ^ to_string_op op)))
        | Star -> (match stack.regs with
          | r::rt -> add_op op {stack with regs = reg_star r :: rt; ops = xt}
          | _ -> raise (Parser_error ("Missing arguments for star when adding " ^ to_string_op op)))
        | Bracket _ -> {stack with ops = op::stack.ops})
      | false -> {stack with ops = op::stack.ops})
    | [] -> {stack with ops = op::[]}

and close_bracket stack = match stack.ops with 
  | x::xt -> (match x with
    | Alt -> (match stack.regs with
      | r2::r1::rt -> close_bracket {stack with regs = reg_union r1 r2 :: rt; ops = xt}
      | l -> close_bracket {stack with regs = l; ops = xt})
    | Concat -> (match stack.regs with
      | r2::r1::rt -> close_bracket {stack with regs = reg_concat r1 r2 :: rt; ops = xt}
      | _ -> raise (Parser_error "Missing arguments for concat when closing bracket"))
    | Star -> (match stack.regs with
      | r::rt -> close_bracket {stack with regs = reg_star r :: rt; ops = xt}
      | _ -> raise (Parser_error "Missing arguments for star when closing bracket"))
    | Bracket (s, r) -> (match s with | Start -> Fun.id | Concat -> add_op Concat) {
      stack with 
      regs = (match stack.regs with 
        | x::[] -> x::r 
        | [] -> Null::r 
        | _ -> raise (Parser_error ("Final stack has " ^ string_of_int (List.length stack.regs) ^ " items when closing bracket"))); 
      ops = xt; 
      state = Core Concat
      })
  | [] -> raise (Invalid_regex "Mismatched bracket )")

and close_regex stack = (match stack.state with
    | Esc s -> raise (Invalid_regex "EoF when parsing escaped character")
    | Esc_sing s -> raise (Invalid_regex "EoF when parsing escaped character")
    | _ -> ()); match stack.ops with
  | x::xt -> (match x with
    | Alt -> (match stack.regs with
      | r2::r1::rt -> close_regex {stack with regs = reg_union r1 r2 :: rt; ops = xt}
      | l -> close_regex {stack with regs = l; ops = xt})
    | Concat -> (match stack.regs with
      | r2::r1::rt -> close_regex {stack with regs = reg_concat r1 r2 :: rt; ops = xt}
      | _ -> raise (Parser_error "Missing arguments for concat when closing regex"))
    | Star -> (match stack.regs with
      | r::rt -> close_regex {stack with regs = reg_star r :: rt; ops = xt}
      | _ -> raise (Parser_error "Missing arguments for star when closing regex"))
    | Bracket _ -> raise (Invalid_regex "Mismatched bracket (")) 
  | [] -> stack;;

(**)
let rec parse str = 
  let stack = close_regex (Seq.fold_left parse_char {regs = []; ops = []; range = None; state = Core Start} (String.to_seq str)) in
  match stack.regs with
  | r::[] -> r
  | [] -> Null
  | _ -> raise (Parser_error ("Final stack has " ^ string_of_int (List.length stack.regs) ^ " items when closing regex"));;

type verbose_state = {line_num: int; char_num: int; stack: parse_stack};;

let verbose_string str stack s =
  "line " ^ string_of_int stack.line_num ^
  " at character " ^ string_of_int stack.char_num ^ ": " ^
  s ^ "\n" ^
  List.nth (String.split_on_char '\n' str) (stack.line_num - 1) ^ "\n" ^
  String.make (stack.char_num - 1) ' ' ^ "^"
  

let verbose_parse_char str stack chr = 
  {
    line_num = (match chr with | '\n' -> stack.line_num + 1 | _ -> stack.line_num);
    char_num = (match chr with | '\n' -> 1 | _ -> stack.char_num + 1);
    stack = try parse_char stack.stack chr with 
      | Parser_error s -> print_stack stack.stack; raise (Parser_error ("Parser error on " ^ verbose_string str stack s))
      | Invalid_regex s -> raise (Invalid_regex ("Error on " ^ verbose_string str stack s))
  };;

let rec verbose_parse str = 
  let verbose_stack = Seq.fold_left (verbose_parse_char str) 
    {line_num = 1; char_num = 1; stack = {regs = []; ops = []; range = None; state = Core Start}} 
    (String.to_seq str) in
  let stack = try close_regex verbose_stack.stack with
    | Parser_error s -> print_stack verbose_stack.stack; raise (Parser_error ("Parser error on " ^ verbose_string str verbose_stack s))
    | Invalid_regex s -> raise (Invalid_regex ("Error on " ^ verbose_string str verbose_stack s)) in
  match stack.regs with
    | r::[] -> r
    | [] -> Null
    | _ -> print_stack stack; raise (Parser_error (
      "Parser error on " ^ 
      verbose_string str verbose_stack ("Final stack has " ^ string_of_int (List.length stack.regs) ^ " items when closing regex")
      ));;

let parser = verbose_parse in

let reg = ref (parser (read_line ())) in
comp print_endline to_string !reg;
let input = ref (read_line ()) in
while (String.trim !input <> "quit") do
  if (String.trim !input = "reset") then begin
    reg := (parser (read_line ()));
    comp print_endline to_string !reg;
    input := read_line ();
  end;
  if (String.trim !input <> "quit" && String.trim !input <> "reset") then begin
    print_endline (match match_regex !reg !input with
      | true -> "true"
      | false -> "false");
    input := read_line ();
  end;
done
