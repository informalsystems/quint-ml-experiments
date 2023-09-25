open Containers

(* TODO Set formation DSL *)
(* TODO Set literal syntax *)
(* TODO Abstract interface to interactivity *)

module Set = struct
  include Set

  module type S = sig
    include S
    val one_of : t -> elt
  end

  module Make (O : Set.OrderedType) : S with type elt = O.t = struct
    include Make (O)

    let one_of : t -> elt =
      fun s -> to_list s |> Random.pick_list |> Random.run
  end
end

module Pair = struct
  module Make (A : Map.OrderedType) (B : Map.OrderedType) = struct
    type t = (A.t, B.t) Pair.t
    let compare = Pair.compare A.compare B.compare
  end
  include Pair
end

(* Actions *)
(* TODO Try using qcheck as basis? *)
module Action = struct
  type 'state t =
    { require : 'state -> bool
    ; ensure : 'state -> 'state
    }

  let def ?(require=Fun.const true) ?(ensure=Fun.id) () : 'state t =
    { require
    ; ensure
    }

  let chk : ('state -> bool) -> 'state t = fun require ->
    { require
    ; ensure = Fun.id
    }

  let chk_not : ('state -> bool) -> 'state t = fun require ->
    { require = (fun st -> not (require st))
    ; ensure = Fun.id
    }

  let upd : ('state -> 'state) -> 'state t = fun ensure ->
    { require = Fun.const true
    ; ensure }

  let app : ('state  -> 'state t) -> 'state t = fun f ->
    { require = (fun st -> (f st).require st)
    ; ensure = (fun st -> (f st).ensure st)
    }

  let (&&): 'state t -> 'state t -> 'state t = fun a b ->
    let require st = a.require st && b.require st in
    let ensure st = a.ensure st |> b.ensure in
    { require ; ensure }

  (* Ensure the same state vars cannot be updated twice? *)
  let all : 'state t list -> 'state t = fun actions ->
    let require st = List.for_all (fun act -> act.require st) actions in
    let ensure st = List.fold_left (fun st' act -> act.ensure st') st actions in
    {require; ensure}

  let any : 'state t list -> 'state t = fun actions ->
    app @@ fun st ->
           match List.filter (fun act -> act.require st) actions with
           | [] -> def ~require:(Fun.const false) ()
           | enabled -> Random.(pick_list enabled |> run)

  let do_first : 'state t list -> 'state t = fun actions ->
    app @@ fun st ->
           match List.find_opt (fun act -> act.require st) actions with
           | Some action -> action
           | None -> { require = Fun.const false
                     ; ensure = Fun.id }

  let tick : 'state t -> 'state -> 'state option = fun act st ->
    if act.require st then
      Some (act.ensure st)
    else
      None
end

module TicTacToe = struct
  module Coord = struct
    module T = Pair.Make (Int) (Int)
    module Set = Set.Make (T)
    include T
  end

  (* A map (int * int) -> player *)
  module Board = Map.Make (Coord)

  module Player = struct
    type t = X | O [@@deriving eq, show { with_path = false }]
  end

  (* TODO Use state management _effect_ to record trace *)
  type state =
    { board : Player.t Board.t
    ; next_turn : Player.t
    } [@@deriving eq]

  let show {board; next_turn} =
    Seq.(
      product (1 -- 3) (1 -- 3)
      |> sort ~cmp:Coord.compare
      |> group (fun (x, _) (x', _) -> x = x')
      |> iter (fun row ->
             Printf.printf "|";
             row |> iter (fun coord ->
                        Board.get coord board
                        |> Option.map Player.show
                        |> Option.value ~default:" "
                        |> Printf.printf" %s |");
             Printf.printf "\n"
           )
    );
    Printf.printf "turn: %s\n" (Player.show next_turn)

  let board_coordinates =
    Seq.(product (1 -- 3) (1 -- 3))
    |> Coord.Set.of_seq

  module Patterns = struct
    include Set.Make (Coord.Set)
    let winning =
      (* Horizontal wins *)
      [ [ (1,1); (1,2); (1,3) ]
      ; [ (2,1); (2,2); (2,3) ]
      ; [ (3,1); (3,2); (3,3) ]
      (* Vertical wins *)
      ; [ (1,1); (2,1); (3,1) ]
      ; [ (1,2); (2,2); (3,2) ]
      ; [ (1,3); (2,3); (3,3) ]
      (* Diagonal wins *)
      ; [ (1,1); (2,2); (3,3) ]
      ; [ (3,1); (2,2); (1,3) ]
      ]
      |> List.map Coord.Set.of_list
      |> of_list
  end

  let corners =
    Coord.Set.of_list
      [ 1,1
      ; 3,1
      ; 1,3
      ; 3,3
      ]

  let is_occupied_by_player st player coord =
    match Board.get coord st.board with
    | None   -> false
    | Some p -> Player.equal p player

  let is_empty coord st =
    Board.get coord st.board |> Option.is_none

  let next_turn_is player st = Player.equal (st.next_turn) player

  let board_empty st = Board.is_empty st.board

  (* TODO Wouldn't a subset check be better here? *)
  let has_won player st =
    Patterns.(winning |> exists (Coord.Set.for_all (is_occupied_by_player st player)))

  let board_is_full st =
    Board.cardinal st.board = Coord.Set.cardinal board_coordinates

  let at_stalemate st =
    board_is_full st && not (has_won X st || has_won O st)

  let game_over st = has_won X st || has_won O st || board_is_full st

  let x_can_win_with_pattern st pattern : bool =
    let occupied_by_X, rest = pattern |> Coord.Set.partition (is_occupied_by_player st X) in
    Coord.Set.cardinal occupied_by_X = 2
    &&
    (* Rest must be a singleton set *)
    Coord.Set.for_all (fun coord -> is_empty coord st) rest

  let x_can_block_with_pattern st pattern : bool =
    let occupied_by_O, rest = pattern |> Coord.Set.partition (is_occupied_by_player st O) in
    Coord.Set.cardinal occupied_by_O = 2
    &&
    (* Rest must be a singleton set *)
    Coord.Set.for_all (fun coord -> is_empty coord st) rest

  let x_can_set_up_win_with_pattern st pattern : bool =
    let occupied_by_X, rest = pattern |> Coord.Set.partition (is_occupied_by_player st X) in
    Coord.Set.cardinal occupied_by_X = 1
    &&
    Coord.Set.for_all (fun coord -> is_empty coord st) rest

  let x_can_win st = Patterns.(winning |> exists (x_can_win_with_pattern st))
  let x_can_block st = Patterns.(winning |> exists (x_can_block_with_pattern st))
  let can_take_center st = is_empty (2,2) st
  let x_can_set_up_win st = Patterns.(winning |> exists (x_can_set_up_win_with_pattern st))

  let move player coord =
    Action.(
      all [ chk @@ is_empty coord
          ; upd @@ fun st -> {st with board = Board.add coord player st.board } ]
    )

  let choose_move_by_strategy player ~require ~strat =
    Action.(
      all [ chk require
          ; app @@ fun st ->
                   let pattern = Patterns.(one_of @@ (winning |> filter (strat st))) in
                   let coord = Coord.Set.one_of @@ (pattern |> Coord.Set.filter (fun xy -> is_empty xy st)) in
                   move player coord
        ]
    )

  let win = choose_move_by_strategy X ~require:x_can_win ~strat:x_can_win_with_pattern

  let block = choose_move_by_strategy X ~require:x_can_block ~strat:x_can_block_with_pattern

  let take_center = Action.(chk board_empty && move X (2, 2))

  let set_up_win = choose_move_by_strategy X ~require:x_can_set_up_win ~strat:x_can_set_up_win_with_pattern

  let move_to_empty player =
    Action.(
      chk_not @@ game_over
      &&
      app @@ fun st ->
             let coord = Coord.Set.one_of @@ (board_coordinates |> Coord.Set.filter (fun xy -> is_empty xy st)) in
             move player coord
    )

  let start_in_corner =
    Action.(chk board_empty && move X (Coord.Set.one_of corners))

  let next_turn =
    Action.def
      ~require:(fun st -> not (board_is_full st))
      ~ensure:(fun st -> {st with next_turn = if Player.equal st.next_turn X then O else X} )
      ()

  let move_x =
    Action.(
      all [ chk @@ next_turn_is X
          ; chk_not @@ has_won O
          ; do_first [ start_in_corner
                     ; win
                     ; block
                     ; take_center
                     ; set_up_win
                     ; move_to_empty X ]
          ; next_turn ]
    )

  let move_o =
    Action.(
      all [ chk @@ next_turn_is O
          ; chk_not @@ has_won X
          ; move_to_empty O
          ; next_turn
        ]
    )

  let init : state =
    { next_turn = X
    ; board = Board.empty
    }

  let step =
    Action.(
      any [ move_x
          ; move_o
        ]
    )

  let run st steps =
    let rec loop st = function
      | 0 -> Printf.printf "finished all steps\n"
      | n ->
      match Action.tick step st with
      | None -> Printf.printf "deadlock\n"
      | Some st' -> show st'; loop st' (pred n)
    in
    show init;
    loop st steps

end

(* let main = Lwt_io.(write_line stdout "Hello, World!") *)

(* let () = Lwt_main.run main *)

let () = TicTacToe.(run init 100)
