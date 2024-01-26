
type alt  = Alt of con * alt'
 and alt' = Alt of con * alt' | Eps
 and con  = Con of ksr * con'
 and con' = Con of ksr * con' | Eps
 and ksr  = Ksr of bkt | Kbt of bkt
 and bkt  = Bkt of alt | Bsg of sng
 and sng  = Chr of char | Lst of lst
 and lst  = Lst of rng * lst'
 and lst' = Lst of rng * lst' | Eps
 and rng  = Sng of char | Rng of char * char;;

type loc = {line_num: int; char_num: int};;

let inc_char_num loc = {loc with char_num = loc.char_num + 1};;
let inc_line_num loc = {line_num = loc.line_num + 1; char_num = 1};;

type token = 
  | CHAR of loc * char
  | PIPE of loc
  | STAR of loc
  | O_ROUND of loc
  | C_ROUND of loc
  | O_SQUARE of loc
  | C_SQUARE of loc
  | DASH of loc;;

let string_of_token = function 
  | CHAR (_, c) -> String.make 1 c
  | PIPE _ -> "|"
  | STAR _ -> "*"
  | O_ROUND _ -> "("
  | C_ROUND _ -> ")"
  | O_SQUARE _ -> "["
  | C_SQUARE _ -> "]"
  | DASH _ -> "-";;


type tokeniser_state = 
  | START of loc * token list
  | ESC of loc * token list;;

exception Invalid_regex of string;;

let tokenise str = 
  let tokenstep state chr = match state with
    | START (l, t) -> (match chr with
      | '\\'  -> ESC (inc_char_num l, t)
      | '|'   -> START (inc_char_num l, PIPE l :: t)
      | '*'   -> START (inc_char_num l, STAR l :: t)
      | '('   -> START (inc_char_num l, O_ROUND l :: t)
      | ')'   -> START (inc_char_num l, C_ROUND l :: t)
      | '['   -> START (inc_char_num l, O_SQUARE l :: t)
      | ']'   -> START (inc_char_num l, C_SQUARE l :: t)
      | '-'   -> START (inc_char_num l, DASH l :: t)
      | '\n'  -> START (inc_line_num l, CHAR (l, chr) :: t)
      | _     -> START (inc_char_num l, CHAR (l, chr) :: t))
    | ESC (l, t) -> (match chr with
      | 'r'   -> START (inc_char_num l, CHAR (l, '\r') :: t)
      | 't'   -> START (inc_char_num l, CHAR (l, '\t') :: t)
      | 'n'   -> START (inc_char_num l, CHAR (l, '\n') :: t)
      | '\n'  -> START (inc_line_num l, CHAR (l, chr) :: t)
      | _     -> START (inc_char_num l, CHAR (l, chr) :: t)) in
  let state = Seq.fold_left 
    tokenstep 
    (START ({line_num = 1; char_num = 1}, [])) 
    (String.to_seq str) in
  match state with
    | START (l, t) -> List.rev t
    | ESC _ -> raise (Invalid_regex "End-of-file when parsing escaped character");;

let parse tokens = 
  let rec f_alt  s = 
    let (toks, c) = f_con s in
    let (toks, a) = f_alt' toks in
    (toks, Alt (c, a))
  and     f_alt' s = match s with
    | PIPE _ :: toks -> 
      let (toks, c) = f_con toks in
      let (toks, a) = f_alt' toks in
      (toks, Alt(c, a))
    | toks -> (toks, Eps)
  and     f_con  s = 
    let (toks, k) = f_ksr s in
    let (toks, c) = f_con' toks in
    (toks, Con(k, c))
  and     f_con' s = match s with
    | [] -> (s, Eps)
    | PIPE _ :: _ -> (s, Eps)
    | C_ROUND _ :: _ -> (s, Eps)
    | toks -> 
      let (toks, k) = f_ksr toks in
      let (toks, c) = f_con' toks in
      (toks, Con(k, c))
  and     f_ksr  s = 
    let (toks, b) = f_bkt s in
    match toks with
    | STAR _ :: toks -> (toks, Ksr b)
    | toks -> (toks, Kbt b)
  and     f_bkt  s = match s with
    | O_ROUND _ :: toks -> 
      let (toks, a) = f_alt toks in
      (match toks with
      | C_ROUND _ :: toks -> (toks, Bkt a)
      | _ -> raise (Invalid_regex "Mismatched bracket"))
    | toks -> 
      let (toks, s) = f_sng toks in
      (toks, Bsg s)
  and     f_sng  s = match s with
    | CHAR (_, c) :: toks -> (toks, Chr c)
    | O_SQUARE _ :: toks -> 
      let (toks, l) = f_lst toks in
      (toks, Lst l)
    | _ -> raise (Invalid_regex (string_of_token (List.hd s)))
  and     f_lst  s = 
    let (toks, r) = f_rng s in
    let (toks, l) = f_lst' toks in
    (toks, Lst(r, l))
  and     f_lst' s = match s with
    | [] -> ([], Eps)
    | C_SQUARE _ :: toks -> (toks, Eps)
    | _ -> 
      let (toks, r) = f_rng s in
      let (toks, l) = f_lst' toks in
      (toks, Lst (r, l)) 
  and     f_rng  s = match s with
    | CHAR (_, s) :: DASH _ :: CHAR (_, e) :: toks -> (toks, Rng(s, e))
    | CHAR (_, c) :: toks -> (toks, Sng c)
    | _ -> raise (Invalid_regex "") in
  let (toks, tree) = f_alt tokens in
  tree;;

let string_of_cst a = 
  let rec f_alt  = function Alt (c, a) -> f_con c ^ f_alt' a
  and     f_alt' = function
    | Alt (c, a) -> "|" ^ f_con c ^ f_alt' a
    | Eps -> ""
  and     f_con  = function Con (k, c) -> f_ksr k ^ f_con' c
  and     f_con' = function
    | Con (k, c) -> f_ksr k ^ f_con' c
    | Eps -> ""
  and     f_ksr  = function
    | Ksr b -> f_bkt b ^ "*"
    | Kbt b -> f_bkt b
  and     f_bkt  = function
    | Bkt a -> "(" ^ f_alt a ^ ")"
    | Bsg s -> f_sng s
  and     f_sng  = function
    | Chr c -> String.make 1 c
    | Lst l -> "[" ^ f_lst l ^ "]"
  and     f_lst  = function Lst (r, l) -> f_rng r ^ f_lst' l
  and     f_lst' = function
    | Lst (r, l) -> f_rng r ^ f_lst' l
    | Eps -> ""
  and     f_rng  = function 
    | Sng c -> String.make 1 c
    | Rng (s, e) -> String.make 1 s ^ "-" ^ String.make 1 e in
  f_alt a;;

type ast = 
  | ALT of ast * ast
  | CON of ast * ast
  | STR of ast
  | SNG of char
  | LST of (char * char) list
  | EPS
  | NULL;;

let ast_alt a1 a2 = match (a1, a2) with
  | NULL, _ -> a2
  | _, NULL -> a1
  | _, _ -> ALT (a1, a2);;

let ast_con a1 a2 = match (a1, a2) with
  | NULL, _ -> NULL
  | _, NULL -> NULL
  | _, _ -> CON (a1, a2);;

let ast_star = function
  | NULL -> NULL
  | EPS -> EPS
  | a -> STR a;;

let ast_of_cst a = 
  let rec f_alt  = function Alt (c, a) -> ast_alt (f_con c) (f_alt' a)
  and     f_alt' = function
    | Alt (c, a) -> ast_alt (f_con c) (f_alt' a)
    | Eps -> NULL
  and     f_con  = function Con (k, c) -> ast_con (f_ksr k) (f_con' c)
  and     f_con' = function
    | Con (k, c) -> ast_con (f_ksr k) (f_con' c)
    | Eps -> EPS
  and     f_ksr  = function
    | Ksr b -> ast_star (f_bkt b)
    | Kbt b -> f_bkt b
  and     f_bkt  = function
    | Bkt a -> f_alt a
    | Bsg s -> f_sng s
  and     f_sng  = function
    | Chr c -> SNG c
    | Lst l -> f_lst l
  and     f_lst  = function
    | Lst (r, l) -> LST (f_rng r :: f_lst' l)
  and     f_lst' = function
    | Lst (r, l) -> f_rng r :: f_lst' l
    | Eps -> []
  and     f_rng  = function 
    | Sng c -> (c, c) 
    | Rng (s, e) -> (s, e) in
  f_alt a;;

let rec string_of_ast = function
  | ALT (r1, r2) -> "(" ^ string_of_ast r1 ^ "|" ^ string_of_ast r2 ^ ")"
  | CON (r1, r2) -> "(" ^ string_of_ast r1 ^ string_of_ast r2 ^ ")"
  | STR r -> "(" ^ string_of_ast r ^ "*" ^ ")"
  | SNG c -> String.make 1 c
  | LST l -> List.fold_left (fun str -> function (s, e) -> 
    match s = e with 
    | true -> str ^ String.make 1 s 
    | false -> str ^ String.make 1 s ^ "-" ^ String.make 1 e) "[" l ^ "]"
  | EPS -> ""
  | NULL -> "{}"

type match_ret = {zero: bool; next: ast};;

let match_regex r str = 
  let rec match_chr r chr = match r with
    | ALT (r1, r2) -> 
      let ret1 = match_chr r1 chr in 
      let ret2 = match_chr r2 chr in
      {zero = ret1.zero || ret2.zero; next = ast_alt ret1.next ret2.next}
    | CON (r1, r2) ->
      let ret1 = match_chr r1 chr in
      (match ret1.zero with
      | true -> 
        let ret2 = match_chr r2 chr in
        {zero = ret2.zero; next = ast_alt (ast_con ret1.next r2) ret2.next}
      | false -> {zero = false; next = ast_con ret1.next r2})
    | STR rs -> 
      let ret = match_chr rs chr in
      {zero = true; next = ast_con ret.next r}
    | SNG c -> (match c = chr with 
      | true -> {zero = false; next = EPS}
      | false -> {zero = false; next = NULL})
    | LST l -> (match List.exists (function (s, e) -> s <= chr && chr <= e) l with
      | true -> {zero = false; next = EPS}
      | false -> {zero = false; next = NULL})
    | EPS -> {zero = true; next = NULL}
    | NULL -> {zero = false; next = NULL} in
  (match_chr (Seq.fold_left (fun ret -> match_chr ret.next) {zero = false; next = r} (String.to_seq str)).next '\x00').zero;;
    

let tokeniser = tokenise in
let parser = parse in

let cst = ref (parser (tokeniser (read_line ()))) in
print_endline (string_of_cst !cst);
let ast = ref (ast_of_cst !cst) in
print_endline (string_of_ast !ast);
let input = ref (read_line ()) in
while (String.trim !input <> "quit") do
  if (String.trim !input = "reset") then begin
    cst := (parser (tokeniser (read_line ())));
    print_endline (string_of_cst !cst);
    ast := ast_of_cst !cst;
    print_endline (string_of_ast !ast);
    input := read_line ();
  end;
  if (String.trim !input <> "quit" && String.trim !input <> "reset") then begin
    print_endline (match match_regex !ast !input with
      | true -> "true"
      | false -> "false");
    input := read_line ();
  end;
done
