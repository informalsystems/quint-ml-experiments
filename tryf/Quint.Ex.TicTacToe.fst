
module Quint.Ex.TicTacToe

open FStar.Order
open Quint.Ordered

module Map = Quint.Map

module Set = Quint.Set
let set #a {| ordered a |} (l: list a) = Set.set l

let ( |> ) x f = f x

type player =
  | O
  | X

type coord = nat * nat

// instance ordered_coord : ordered coord = Set.ordered_set #(nat * nat) #(ordered_pair #nat #nat #ordered_nat #ordered_nat)

type board = Map.t coord player

type state =
  { board : board
  ; next_turn : player
  }

let board_coordinates =
  Set.product (Set.range 1 3) (Set.range 1 3)

let winning_patterns : Set.t (Set.t coord) =
       (* Horizontal wins *)
    set[ set [ (1,1); (1,2); (1,3) ]
       ; set [ (2,1); (2,2); (2,3) ]
       ; set [ (3,1); (3,2); (3,3) ]
       (* Vertical wins *)
       ; set [ (1,1); (2,1); (3,1) ]
       ; set [ (1,2); (2,2); (3,2) ]
       ; set [ (1,3); (2,3); (3,3) ]
       (* Diagonal wins *)
       ; set [ (1,1); (2,2); (3,3) ]
       ; set [ (3,1); (2,2); (1,3) ]
       ]

let corners : Set.t coord =
  set [ 1,1
      ; 3,1
      ; 1,3
      ; 3,3
      ]

let is_occupied_by_player (b:board) (p:player) (c:coord) : bool =
  match Map.get c b with
  | None    -> false
  | Some p' -> p = p'

let is_empty (b:board) (c:coord) : bool =
  Map.get c b |> None?

let next_turn_is (p:player) (s:state) : bool =
  s.next_turn = p

let board_is_empty (b:board) : bool = b =
  Set.empty

let has_won (p:player) (b:board) : bool =
  winning_patterns |> Set.for_some (Set.for_all (is_occupied_by_player b p))

let board_is_full (b:board) : bool =
  Set.size b = Set.size board_coordinates

let at_stalemate (b:board) : bool =
  board_is_full b && not (has_won X b || has_won O b)

let game_over (b:board) : bool =
  has_won X b || has_won O b || board_is_full b

let x_can_win_with_pattern (b:board) (pattern:Set.t coord) : bool =
  let occupied_by_X, rest = pattern |> Set.partition (is_occupied_by_player b X) in
  Set.size occupied_by_X = 2
  &&
  Set.for_all (is_empty b) rest

let x_can_block_with_pattern (b:board) (pattern:Set.t coord) : bool =
  let occupied_by_O, rest = pattern |> Set.partition (is_occupied_by_player b O) in
  Set.size occupied_by_O = 2
  &&
  (* Rest must be a singleton set *)
  Set.for_all (is_empty b) rest

let x_can_set_up_win_with_pattern (b:board) (pattern:Set.t coord) : bool =
  let occupied_by_X, rest = pattern |> Set.partition (is_occupied_by_player b X) in
  Set.size occupied_by_X = 1
  &&
  Set.for_all (is_empty b) rest

let x_can_win (b:board) = winning_patterns |> Set.for_some (x_can_win_with_pattern b)
let x_can_block (b:board) = winning_patterns |> Set.for_some (x_can_block_with_pattern b)
let can_take_center (b:board) = is_empty b (2,2)
let x_can_set_up_win (b:board) = winning_patterns |> Set.for_some (x_can_set_up_win_with_pattern b)
