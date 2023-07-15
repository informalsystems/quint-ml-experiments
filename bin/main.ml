(* module TicTacToe = struct *)
(*   type player = X | O *)
(*   module Board = Map.Make (Pair) *)
(*   type state = *)
(*     { board : *)
(*     ; nextTurn : player *)
(*     } *)
(* end *)

let main = Lwt_io.(write_line stdout "Hello, World!")

let () = Lwt_main.run main
