
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;
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
