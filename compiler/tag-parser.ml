(* pc.ml
 * A parsing-combinators package for ocaml
 *
 * Prorammer: Mayer Goldberg, 2018
 *)

(* general list-processing procedures *)

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;

module PC = struct

(* the parsing combinators defined here *)
  
exception X_not_yet_implemented;;

exception X_no_match;;

let const pred =
  function 
  | [] -> raise X_no_match
  | e :: s ->
     if (pred e) then (e, s)
     else raise X_no_match;;

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

let nt_epsilon s = ([], s);;

let caten_list nts =
  List.fold_right
    (fun nt1 nt2 ->
     pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
    nts
    nt_epsilon;;

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_no_match -> (nt2 s);;

let nt_none _ = raise X_no_match;;
  
let disj_list nts = List.fold_right disj nts nt_none;;

let delayed thunk s =
  thunk() s;;

let nt_end_of_input = function
  | []  -> ([], [])
  | _ -> raise X_no_match;;

let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with X_no_match -> ([], s);;

let plus nt =
  pack (caten nt (star nt))
       (fun (e, es) -> (e :: es));;

let guard nt pred s =
  let ((e, _) as result) = (nt s) in
  if (pred e) then result
  else raise X_no_match;;
  
let diff nt1 nt2 s =
  match (let result = nt1 s in
	 try let _ = nt2 s in
	     None
	 with X_no_match -> Some(result)) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let not_followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     None
	 with X_no_match -> (Some(result))) with
  | None -> raise X_no_match
  | Some(result) -> result;;
	  
let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

(* useful general parsers for working with text *)

let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;

let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
	       (lowercase_ascii ch2));;

let make_word char str = 
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))
    nt_epsilon;;

let word = make_word char;;

let word_ci = make_word char_ci;;

let make_one_of char str =
  List.fold_right
    disj
    (List.map char (string_to_list str))
    nt_none;;

let one_of = make_one_of char;;

let one_of_ci = make_one_of char_ci;;

let nt_whitespace = const (fun ch -> ch <= ' ');;

let make_range leq ch1 ch2 (s : char list) =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2)) s;;

let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;

let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

let nt_any (s : char list) = const (fun ch -> true) s;;

let trace_pc desc nt s =
  try let ((e, s') as args) = (nt s)
      in
      (Printf.printf ";;; %s matched the head of \"%s\", and the remaining string is \"%s\"\n"
		     desc
		     (list_to_string s)
		     (list_to_string s') ;
       args)
  with X_no_match ->
    (Printf.printf ";;; %s failed on \"%s\"\n"
		   desc
		   (list_to_string s) ;
     raise X_no_match);;

(* testing the parsers *)

let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

end;; (* end of struct PC *)

(* end-of-input *)

 open PC
 
 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
   
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 
 let rec sexpr_eq s1 s2 =
   match s1, s2 with
   | Bool(b1), Bool(b2) -> b1 = b2
   | Nil, Nil -> true
   | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
   | Number(Int n1), Number(Int n2) -> n1 = n2
   | Char(c1), Char(c2) -> c1 = c2
   | String(s1), String(s2) -> s1 = s2
   | Symbol(s1), Symbol(s2) -> s1 = s2
   | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
   | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
   | _ -> false;;
   
 module Reader: sig
   val read_sexpr : string -> sexpr
   val read_sexprs : string -> sexpr list
 end
 = struct
 let normalize_scheme_symbol str =
   let s = string_to_list str in
   if (andmap
   (fun ch -> (ch = (lowercase_ascii ch)))
   s) then str
   else Printf.sprintf "|%s|" str;;
 
   let caten_and_forget_left nt1 nt2 = pack (caten nt1 nt2) (fun (s1, s2) -> s2) ;;
   let caten_and_forget_right nt1 nt2 = pack (caten nt1 nt2) (fun (s1, s2) -> s1) ;;
   let caten_and_forget_sides nt1 nt2 nt3 = caten_and_forget_left nt1 (caten_and_forget_right nt2 nt3) ;;
   
   let rec read_sexpr s =
   let (e, s) = all_sexprs (string_to_list s) in e
   (*  *)
   
   and non_symbols s =
     let nt = disj_list [nt_bool; nt_number; nt_char; nt_string; nt_sequences; nt_quotes] in
     nt s
     (*  *)
   
   and all_sexprs s =
     let nt_raw_sexpr = disj_list [nt_symbol; non_symbols; nt_list_3dot] in
     let nt = caten_and_forget_sides nt_skipable nt_raw_sexpr nt_skipable in
     nt s
   
   and all_sexprs_in_three_dots_only s =
     let nt_raw_sexpr = disj nt_symbol non_symbols in
     let nt = caten_and_forget_sides nt_skipable nt_raw_sexpr nt_skipable in
     nt s
     
   and nt_comment_line s =
     let nt_start = char ';' in
     let nt_eol = char '\n' in
     let nt_eoi = pack nt_end_of_input (fun _ -> '\n') in
     let nt_end = disj nt_eol nt_eoi in
     let nt_comment_digits = diff nt_any nt_end in
     let nt_comment = caten nt_start (caten (star nt_comment_digits) nt_end) in
     let nt = pack nt_comment (fun _ -> "") in
     nt s
     (*  *)
   
   and nt_comment_sexpr s =
     let nt_start = word "#;" in
     let nt = caten nt_start (caten nt_skipable all_sexprs) in
     let nt = pack nt (fun _ -> "") in
     nt s
     (*  *)
   
   and nt_quotes s =
     let meta str_c str_s =
       let nt_str = word str_c in
       let nt = caten nt_str all_sexprs in
       pack nt (fun (_, expr) -> Pair(Symbol str_s, Pair(expr, Nil))) in
     let nt = disj_list [(meta "\'" "quote"); (meta "`" "quasiquote"); (meta ",@" "unquote-splicing");(meta "," "unquote")] in
     nt s
     (*  *)
   
   and nt_single_skipable s =
     let nt_newlines = pack (char '\n') (fun _ -> "") in
     let nt_spaces = pack nt_whitespace (fun _ -> "") in
     let nt_comment_lines = pack nt_comment_line (fun _ -> "") in
     let nt_comment_sexprs = pack nt_comment_sexpr (fun _ -> "") in
     let nt = disj_list [nt_spaces; nt_comment_lines; nt_comment_sexprs; nt_newlines] in
     let nt = pack nt (fun _ -> "") in
     nt s
     (*  *)
   
   and nt_skipable s =
     let nt = star nt_single_skipable in
     let nt = pack nt (fun _ -> "") in
     nt s
     (*  *)
   
   and nt_bool s =
     let nt_true = word_ci "#t" in
     let nt_false = word_ci "#f" in
     let nt = disj nt_true nt_false in
     let nt = pack nt (function
     | [_;'t'] | [_;'T'] -> Bool true; 
     | [_;'f'] | [_;'F'] -> Bool false;
     | _ -> raise X_no_match) in
     nt s 
     (* *)
   
   and nt_number s =
     let caten_strings nt1 nt2 = pack (caten nt1 nt2) (fun (s1,s2) -> s1^s2) in
   
     let nt_hexadecimal_prefix	= word_ci "#x" in
     let nt_float_notation = char '.' in
     let nt_scientific_notation = word_ci "e" in
     let nt_plus_sign	= char '+' in
     let nt_minus_sign = char '-' in
     let nt_decimal_digits = range '0' '9' in
     let nt_hexadecimal_letters = disj (range_ci 'a' 'f') nt_decimal_digits in
   
     let nt_number_sign = maybe (disj nt_plus_sign nt_minus_sign) in
     let nt_number_sign = pack nt_number_sign (function
       | Some('+') | None -> ""
       | Some(sign_multiplier) -> String.make 1 sign_multiplier) in
   
     let nt_hexadecimal_prefix = pack nt_hexadecimal_prefix (function
       | [_;'x'] | [_;'X'] -> "0x"
       | _ -> raise X_no_match) in
   
     let nt_float_notation = pack nt_float_notation (String.make 1) in
   
   
     let nt_decimal_integer = pack (plus nt_decimal_digits) (fun s -> String.concat "" (List.map (String.make 1) s)) in 
     let nt_hexadecimal_integer = pack (plus nt_hexadecimal_letters) (fun s -> String.concat "" (List.map (String.make 1) s)) in
   
   
     let nt_signed_decimal_integer = caten nt_number_sign nt_decimal_integer in 
     let nt_signed_decimal_integer = pack nt_signed_decimal_integer (fun (sign_multiplier, absolute_number) -> sign_multiplier ^ absolute_number) in
   
     let nt_signed_hexadecimal_integer = caten nt_number_sign nt_hexadecimal_integer in
     let nt_signed_hexadecimal_integer = caten nt_hexadecimal_prefix nt_signed_hexadecimal_integer in
     let nt_signed_hexadecimal_integer = pack nt_signed_hexadecimal_integer (fun (hexadecimal_prefix, (sign_multiplier, absolute_number)) -> sign_multiplier ^ hexadecimal_prefix ^ absolute_number) in
   
   
     let nt_decimal_float = caten_strings nt_float_notation nt_decimal_integer in 
     let nt_signed_decimal_float = caten_strings nt_signed_decimal_integer nt_decimal_float in 
   
     let nt_hexadecimal_float = caten_strings nt_float_notation nt_hexadecimal_integer in
     let nt_signed_hexadecimal_float = caten_strings nt_signed_hexadecimal_integer nt_hexadecimal_float in
   
     let nt_integer_scientific = caten nt_scientific_notation nt_signed_decimal_integer in
     let nt_integer_scientific = pack nt_integer_scientific (fun (scientific_notation, exponent) -> (list_to_string scientific_notation) ^ exponent) in
     let nt_integer_scientific = caten nt_signed_decimal_integer nt_integer_scientific in
     let nt_integer_scientific = pack nt_integer_scientific (fun (base, notation_and_exponent) -> (string_of_float(float_of_int(int_of_string base))) ^ notation_and_exponent) in
   
     let nt_float_scientific = caten nt_scientific_notation nt_signed_decimal_integer in
     let nt_float_scientific = pack nt_float_scientific (fun (scientific_notation, exponent) -> (list_to_string scientific_notation) ^ exponent) in 
     let nt_float_scientific = caten nt_signed_decimal_float nt_float_scientific in 
     let nt_float_scientific = pack nt_float_scientific (fun (base, notation_and_exponent) -> base ^ notation_and_exponent) in 
   
     let nt_integer = disj nt_signed_hexadecimal_integer nt_signed_decimal_integer in
     let nt_integer = pack nt_integer (fun int_string -> Int (int_of_string int_string)) in
   
     let nt_float = disj nt_signed_hexadecimal_float nt_signed_decimal_float in
     let nt_float = pack nt_float (fun float_string -> Float (float_of_string float_string)) in
   
     let nt_scientific = disj nt_float_scientific nt_integer_scientific in
     let nt_scientific = pack nt_scientific (fun scientific_string -> Float (float_of_string scientific_string)) in
   
   
     let nt_number = disj_list [nt_scientific; nt_float; nt_integer] in 
     let nt = pack nt_number (fun num -> Number (num)) in
     nt s
     (*  *)
   
   and nt_symbol s =
     let nt_digits = range '0' '9' in
     let nt_letters = range 'a' 'z' in
     let nt_letters_capital = range 'A' 'Z' in
     let nt_letters_capital = pack nt_letters_capital (fun c -> Char.lowercase c) in
     let nt_punctuations = one_of "!$^*-_=+<>/?:" in
     let nt_symbol_char = disj_list [nt_digits; nt_letters; nt_letters_capital; nt_punctuations] in
     let nt_symbol = pack (plus nt_symbol_char) list_to_string in
     let nt_symbol = pack nt_symbol (fun s -> Symbol s) in
     let nt = diff nt_symbol nt_number in
     nt s
     (*  *)
   
   and nt_meta_character s =
     let meta_char str chr = pack (word_ci str) (fun _ -> chr) in
     let nt = disj_list [(meta_char "\\\\" (Char.chr 92)); (meta_char "\\\"" (Char.chr 34)); (meta_char "\\n" (Char.chr 10)); (meta_char "\\r" (Char.chr 13)); (meta_char "\\t" (Char.chr 9)); (meta_char "\\f" (Char.chr 12))] in
     nt s
     (*  *)
   
   and nt_hex_character s =
     let nt_hex_digit = disj (range '0' '9') (range_ci 'a' 'f') in
     let nt_hex_character = caten (word_ci "\\x") (plus nt_hex_digit) in
     let nt_hex_character = caten nt_hex_character (char ';') in
     let nt_hex_character = pack nt_hex_character (fun ((_,hexa_char), _) -> "0x" ^ list_to_string hexa_char ) in
     let nt = pack nt_hex_character (fun (hex_char) -> char_of_int (int_of_string hex_char)) in
     nt s
     (*  *)
   
   and nt_string s =
     let nt_quote = char '\"' in
     let nt_str_chr = diff nt_any (one_of "\"") in 
     let nt_str_chr = disj_list [nt_hex_character; nt_meta_character; nt_str_chr] in 
   
     let nt_str = star nt_str_chr in
     let nt = caten nt_quote (caten nt_str nt_quote) in
     let nt = pack nt (fun (_, (str, _)) -> String (list_to_string str)) in
     nt s 
     (*  *)
   
   and nt_char s =
     let nt_newline = pack (word_ci "newline") (fun _ -> Char.chr 10) in
     let nt_return = pack (word_ci "return") (fun _ -> Char.chr 13) in
     let nt_tab = pack (word_ci "tab") (fun _ -> Char.chr 9) in
     let nt_formfeed = pack (word_ci "page") (fun _ -> Char.chr 12) in
     let nt_space = pack (word_ci "space") (fun _ -> Char.chr 32) in
     let nt_nul = pack (word_ci "nul") (fun _ -> Char.chr 0) in
   
     let nt_named_chars = disj_list [nt_newline; nt_return; nt_tab; nt_formfeed; nt_space ; nt_nul] in
   
     let nt_visible_simple_chars = pack nt_any (function 
     | c when Char.code c > 32 -> c
     | _ -> raise X_no_match) in
   
     let nt_hex_digit = disj (range '0' '9') (range_ci 'a' 'f') in
     let nt_hex_char = caten (char_ci 'x') (plus nt_hex_digit) in
     let nt_hex_char = pack nt_hex_char (fun (_,hex_char) -> "0x" ^ (list_to_string hex_char) ) in 
     let nt_hex_char = pack nt_hex_char (function (hex_char) -> char_of_int (int_of_string hex_char)) in
   
     let nt_char_prefix = word "#\\" in
   
     let nt_char =  disj_list [nt_named_chars; nt_hex_char; nt_visible_simple_chars] in
   
     let nt = caten nt_char_prefix nt_char in
     let nt = pack nt (fun (_, c) -> Char c) in
     nt s
     (*  *)
   
   and nt_sequences s =
     let rec make_proper_list = function
       | [] -> Nil
       | car::cdr -> Pair (car , make_proper_list cdr) in
     let rec make_improper_list = function
       | [] -> Nil
       | car::cdr::[] -> Pair (car, cdr)
       | car::cdr -> Pair (car , make_improper_list cdr) in
     let rec vector_from_pairs = function
       | Nil -> []
       | Pair (car, Pair (cadr, cddr)) -> car::(vector_from_pairs (Pair (cadr, cddr)))
       | Pair (car, Nil) -> [car]
       | Pair (car, cdr) -> car::[cdr]
       | _ -> raise X_this_should_not_happen in
   
     let nt_DOT = caten_and_forget_sides nt_skipable (char '.') nt_skipable in
     let nt_PL = caten_and_forget_right (char '(') nt_skipable in
     let nt_PR = caten_and_forget_left nt_skipable (char ')') in
     let nt_BL = caten_and_forget_right (char '[') nt_skipable in
     let nt_BR = caten_and_forget_left nt_skipable (char ']') in
   
     let nt_plus = plus all_sexprs in
     let nt_star = star all_sexprs in
   
     let parenthesize pc = pc nt_PL nt_PR in
     let bracketize   pc = pc nt_BL nt_BR in
   
     let nt_abstract_proper_list nt_L nt_R = caten_and_forget_sides nt_L nt_star nt_R in
     let nt_abstract_improper_list nt_L nt_R =
       let nt_awkward_improper_list =
         caten_and_forget_left nt_L 
         (caten nt_plus
         (caten_and_forget_left nt_DOT
         (caten_and_forget_right all_sexprs nt_R))) in 
       pack nt_awkward_improper_list (fun (sexprs, last_sexpr) -> sexprs @ [last_sexpr]) in
   
     let nt_abstract_list nt_abstract_type_list = disj (bracketize nt_abstract_type_list) (parenthesize nt_abstract_type_list) in
   
     let nt_proper_list   = pack (nt_abstract_list nt_abstract_proper_list)   make_proper_list in
     let nt_improper_list = pack (nt_abstract_list nt_abstract_improper_list) make_improper_list in
   
     let nt_list = disj_list[nt_proper_list; nt_improper_list] in
   
     let nt_vector = caten (char '#') (diff nt_list nt_improper_list) in
     let nt_vector = pack nt_vector (fun (_, lst) -> Vector (vector_from_pairs lst)) in
   
     let nt = disj_list [nt_list; nt_vector] in
     nt s
     (*  *)
     
   (* ********** operator "..." ********** *)
   and nt_list_3dot s =
     let rec make_proper_list = function
       | [] -> Nil
       | car::cdr -> Pair (car , make_proper_list cdr) in
     let rec make_improper_list = function
       | [] -> Nil
       | car::cdr::[] -> Pair (car, cdr)
       | car::cdr -> Pair (car , make_improper_list cdr) in
     let rec vector_from_pairs = function
       | Nil -> []
       | Pair (car, Pair (cadr, cddr)) -> car::(vector_from_pairs (Pair (cadr, cddr)))
       | Pair (car, Nil) -> [car]
       | Pair (car, cdr) -> car::[cdr]
       | _ -> raise X_this_should_not_happen in
   
     let nt_DOT = caten_and_forget_sides nt_skipable (char '.') nt_skipable in
     let nt_PL = caten_and_forget_right (char '(') nt_skipable in
     let nt_PR = caten_and_forget_left nt_skipable (char ')') in
     let nt_BL = caten_and_forget_right (char '[') nt_skipable in
     let nt_BR = caten_and_forget_left nt_skipable (char ']') in
   
     let nt_plus = plus all_sexprs_in_three_dots_only in
     let nt_star = star all_sexprs_in_three_dots_only in
     
     let nt_3dot = word "..." in
   
     let rec nt_abstract_proper_list_3dot_single_beginning nt_L =
       let nt_recursive_element =
         let nt_awkward_recursive_element = caten nt_star nt_list_3dot_beginning in (* importanto *)
       pack nt_awkward_recursive_element (fun (sexprs, last_sexpr) -> sexprs @ [last_sexpr]) in
       caten_and_forget_left nt_L
       (disj nt_recursive_element nt_star) (* mucho-mucho importanto! *)
     and nt_proper_list_3dot_single_beginning s = (pack 
       (disj (nt_abstract_proper_list_3dot_single_beginning nt_PL) (nt_abstract_proper_list_3dot_single_beginning nt_BL))
       make_proper_list) s
   
     and nt_abstract_improper_list_3dot_single_beginning nt_L =
       let nt_awkward_improper_list_of left right = 
         caten_and_forget_left nt_L 
         (caten left
         (caten_and_forget_left nt_DOT right)) in 
       let nt_awkward_improper_list = nt_awkward_improper_list_of nt_plus (disj nt_list_3dot_beginning all_sexprs_in_three_dots_only) in (* importanto *)
       pack nt_awkward_improper_list (fun (sexprs, last_sexpr) -> sexprs @ [last_sexpr])
     and nt_improper_list_3dot_single_beginning s = (pack
         (disj (nt_abstract_improper_list_3dot_single_beginning nt_PL) (nt_abstract_improper_list_3dot_single_beginning nt_BL))
         make_improper_list) s
   
     and nt_list_3dot_beginning s = (disj nt_improper_list_3dot_single_beginning nt_proper_list_3dot_single_beginning) s in (* ay-ay-ayyy! *)
   
     let nt = caten_and_forget_right nt_list_3dot_beginning nt_3dot in
     nt s;;
   (* ********** operator "..." ********** *)
   
   let read_sexprs s =
     let nt_3dot = pack (word "...") (fun _ -> "") in
     let nt_single_skipable_3dot s =
       let nt = disj nt_single_skipable nt_3dot in
       let nt = pack nt (fun _ -> "") in
       nt s in
   
     let nt_skipable_3dot s =
       let nt = star nt_single_skipable_3dot in
       let nt = pack nt (fun _ -> "") in
       nt s in
   
   let nt = star (caten_and_forget_sides nt_skipable_3dot all_sexprs nt_skipable_3dot) in
   let (e, s) = nt (string_to_list s) in
   e;;
   
 end;; (* struct Reader *)
 

(* **************** TODO: uncomment "#use ..." and delete everything above this line including this line **************** *)
(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 (* #use "reader.ml";; *)
(* ********************************************************************************************************************** *)

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let string_of_symbol = function
  | Symbol s -> s 
  | _ -> raise X_this_should_not_happen

let rec list_of_propList = function
  | Pair (head, tail) -> head :: list_of_propList tail
  | Nil -> []
  | _ -> raise X_this_should_not_happen

let rec propList_of_list = function
  | head :: tail -> Pair (head, propList_of_list tail)
  | [] -> Nil

let rec tag_parse_expression sexpr =
  let exprList_of_propList lst = List.map
    tag_parse_expression (list_of_propList lst) in
  
  let strList_of_propList sexprPropList = List.map
    string_of_symbol (list_of_propList sexprPropList) in
  
  let rec strList_str_of_sexprList = function
    | Pair (Symbol cur, rest) -> let (args, arg_opt) = (strList_str_of_sexprList rest) in (cur :: args, arg_opt)
    | Symbol arg_opt -> ([], arg_opt)
    | _ -> raise X_this_should_not_happen in

  let beginize_implicit_seq seq = (Pair (Symbol "begin", seq)) in

  match sexpr with
  (* Constants *)
  | Bool _ | Number _ | Char _ | String _ -> Const (Sexpr sexpr)
  | Pair (Symbol "quote", quoted_form) -> Const (Sexpr quoted_form)

  (* Variables *)
  | Symbol var when List.for_all (fun x -> x != var) reserved_word_list -> Var var

  (* Conditionals *)
  | Pair (Symbol "if", Pair (_if, Pair(_then, Pair(_else, Nil)))) ->
    If (tag_parse_expression _if, tag_parse_expression _then, tag_parse_expression _else)
  | Pair (Symbol "if", Pair (_if, Pair(_then, Nil))) ->
    If (tag_parse_expression _if, tag_parse_expression _then, Const Void)
  
  (* Lambda Expressions *)
  | Pair (Symbol "lambda", Pair (sexpr_args_list, body)) ->
    (try
    LambdaSimple (strList_of_propList sexpr_args_list, tag_parse_expression (beginize_implicit_seq body))
    with X_this_should_not_happen ->
    let (args, arg_opt) = strList_str_of_sexprList sexpr_args_list in
    LambdaOpt (args, arg_opt, tag_parse_expression (beginize_implicit_seq body)))
  
  (* Disjunctions *)
  | Pair (Symbol "or", args) -> Or (exprList_of_propList args)

  (* Definitions *)
  | Pair (Symbol "define", Pair (Pair(name, args), Pair(body, Nil))) ->
    tag_parse_expression (Pair (Symbol "define", Pair (name, Pair (Symbol "lambda", Pair (args, Pair (body, Nil))))))
  | Pair (Symbol "define", Pair (name, Pair(value, Nil))) -> Def (tag_parse_expression name, tag_parse_expression value)

  (* Assignments *)
  | Pair (Symbol "set!", Pair (variable, Pair (value, Nil))) -> Set (tag_parse_expression variable, tag_parse_expression value)

  (* Sequences *)
  | Pair (Symbol "begin", Nil) -> Const Void
  | Pair (Symbol "begin", Pair(element, Nil)) -> tag_parse_expression element
  | Pair (Symbol "begin", elements) -> Seq (exprList_of_propList elements)

  (* quasiquote expansion *)
  | Pair (Symbol "quasiquote", sexpr) ->
    let rec quasiquote_expand = function 
      | Pair (Symbol "unquote", Pair (sexpr, Nil)) -> sexpr
      | Pair (Symbol "unquote-splicing", Pair (sexpr, Nil)) -> raise X_syntax_error
      | Symbol _ | Nil as x -> Pair (Symbol "quote", Pair (x, Nil))
      | Bool _ | Number _ | Char _ | String _ as x -> x
      | Vector sexprList -> Pair(Symbol "vector", propList_of_list (List.map quasiquote_expand sexprList))
      | Pair (Pair (Symbol "unquote-splicing", Pair (sexpr, Nil)), b) ->
        Pair (Symbol "append", Pair (sexpr, Pair (quasiquote_expand b, Nil)))
      | Pair (a, Pair (Symbol "unquote-splicing", Pair (sexpr, Nil))) ->
        Pair (Symbol "cons", Pair (quasiquote_expand a, Pair (sexpr, Nil)))
      | Pair (a, b) -> Pair (Symbol "cons", Pair (quasiquote_expand a, Pair (quasiquote_expand b, Nil)))
    in
    tag_parse_expression (quasiquote_expand sexpr)

  (* cond expantion *)
  | Pair (Symbol "cond", ribs) ->
    let rec cond_expand = function
      | Pair(Pair(expr, Pair(Symbol "=>", Pair(exprF, Nil))), ribs) ->
        Pair(Symbol "let", Pair(
          Pair(
            Pair(Symbol "value", Pair(expr, Nil)),
            Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(exprF, Nil))), Nil)), Nil)
          ),
          Pair(Pair(Symbol "if",
          Pair(Symbol "value",
          Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(cond_expand ribs, Nil)))), Nil)))
      | Pair(Pair(Symbol "else", exprs), _) -> Pair(Symbol "begin", exprs)
      | Pair(Pair(expr, exprs), ribs) ->
        Pair(Symbol "if", Pair(expr, Pair(Pair(Symbol "begin", exprs), Pair(cond_expand ribs, Nil)))) 
      | _ -> raise X_syntax_error in
    tag_parse_expression (cond_expand ribs)

  (* let expansion *)
  | Pair(Symbol "let", Pair(def_ribs, body)) -> 
    let get_var_from_rib = function 
      | Pair(var, Pair(_, Nil)) -> var
      | _ -> raise X_syntax_error in
    let get_val_from_rib = function 
      | Pair(_, Pair(value, Nil)) -> value
      | _ -> raise X_syntax_error in
    let def_ribs_vars = 
      propList_of_list (List.map get_var_from_rib (list_of_propList def_ribs)) in
    let def_ribs_vals = 
      propList_of_list (List.map get_val_from_rib (list_of_propList def_ribs)) in
    tag_parse_expression (Pair(Pair(Symbol "lambda", Pair(def_ribs_vars, body)), def_ribs_vals))

  (* Applications *)
  | Pair (f, args) -> Applic (tag_parse_expression f, exprList_of_propList args)

  | _ -> raise X_not_yet_implemented;;



let tag_parse_expressions sexpr = raise X_not_yet_implemented;;


  
end;; (* struct Tag_Parser *)
