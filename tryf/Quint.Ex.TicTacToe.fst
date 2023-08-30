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

let is_occupied_by_player
  (b:board) (c:coord) (p:player)
  : bool
  = match Map.get c b with
  | None    -> false
  | Some p' -> p = p'

let is_empty
  (c:coord) (b:board)
  : bool
  = Map.get c b |> None?

let next_turn_is
  (p:player) (s:state)
  : bool
  = s.next_turn = p

let board_is_empty
  (b:board)
  : bool
  = b = Set.empty

let has_won
  (p:player) (b:board)
  : bool
  =
