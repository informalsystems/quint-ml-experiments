module Quint.Show

open FStar.Tactics.Typeclasses

class show (a:Type) = {
  to_string : a -> string
}

// instance show_fallback #a : show a = {
//   to_string = fun _ -> "<opaque>"
// }

instance show_int : show int = {
  to_string = Prims.string_of_int
}

instance show_string : show string = {
  to_string = fun x -> "\"" ^ x ^ "\""
}

let rec list_to_string_aux #a (f : a -> string) : list a -> string = function
 | [] -> "[]"
 | [x] -> f x ^ " ]"
 | x::xs -> f x ^ "; " ^ list_to_string_aux f xs

let list_to_string #a (f : a -> string) (l:list a) : string =
  "[ " ^ list_to_string_aux f l

instance show_list #a {|show a|} : show (list a) = {
  to_string = list_to_string to_string
}

instance show_pair #a #b {|show a|} {|show b|} : show (a * b) = {
  to_string = fun (x, y) -> "(" ^ to_string x ^ ", " ^ to_string y ^ ")"
}

private
let f #a {| show a |} (x:a) = to_string x

private
let _exv = [f 1; f "foo"; f [1;2;3]; f ("fii", 3)]

private
let _exs = assert_norm (
  _exv
  =

  ["1"; "\"foo\""; "[ 1; 2; 3 ]"; "(\"fii\", 3)"]
)
