open Js_of_ocaml
(* open Js_of_ocaml_lwt *)

module Html = Dom_html

open Lwt.Syntax
let _ =
  Lwt.async (fun () ->
      let+ m = Um_quint.Run.ex in
      print_endline m
    )
