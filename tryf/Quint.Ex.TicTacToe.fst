module Quint.Ex.TicTacToe

open FStar.Order
open Quint.Ordered

module Map = Quint.Map
module Ordered = Quint.Ordered
module State = Quint.State
module Set = Quint.Set

open Quint.State.Sig
open Quint.Util

let set #a {| ordered a |} (l: list a): s:Set.t a{Set.preserves_nonempty l s.ls} = Set.set l


/// DATA

type player =
  | O
  | X

type coord = nat * nat

type board = Map.t coord player

let board_coordinates : Set.t coord =
  Set.product (Set.range 1 3) (Set.range 1 3)

let winning_patterns : Set.non_empty (Set.t coord) =
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

let corners : Set.non_empty coord =
  set [ 1,1
      ; 3,1
      ; 1,3
      ; 3,3
      ]


/// PURE FUNCTIONS

let is_occupied_by_player (b:board) (p:player) (c:coord) : bool =
  match Map.get c b with
  | None    -> false
  | Some p' -> p = p'

let is_empty (b:board) (c:coord) : bool =
  Map.get c b |> None?

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

open Quint.Rng.Ops

let winning_move_for_player (p:player) (b:board) : State.nondet (option( c:coord{is_empty b c})) =
  let? pattern = State.one_of winning_patterns in
  let occupied_by_p, rest = pattern |> Set.partition (is_occupied_by_player b p) in
  if Set.size occupied_by_p = 2 then
    Set.find (is_empty b) rest
  else
    None

let blocking_move_for_player (p:player) (b:board) : State.nondet (option( c:coord{is_empty b c})) =
  let? pattern = State.one_of winning_patterns in
  let occupied_by_opponent, rest = pattern |> Set.partition
      (fun c -> not (is_occupied_by_player b p c) && not (is_empty b c)) in
  if Set.size occupied_by_opponent = 2 then
    Set.find (is_empty b) rest
  else
    None

let set_up_win_for_player (p:player) (b:board) : State.nondet (option coord) =
  State.one_of winning_patterns >>= (fun pattern ->
  let occupied_by_p, rest = pattern |> Set.partition (is_occupied_by_player b p) in
  if Set.size rest = 2 && Set.for_all (is_empty b) rest then
    let? c' = State.one_of rest in
    Some c'
  else
    return None
  )

let free_space (p:player) (b:board) : State.nondet (option coord) =
  let free_spaces = Set.filter (is_empty b) board_coordinates in
  if Set.size free_spaces > 0 then
    let? c = State.one_of free_spaces in
    Some c
  else
    return None


/// STATE

type vars = | Board | Next_turn
instance state_sig : sig = {
   vars = vars;
   types = (function
         | Board -> board
         | Next_turn -> player)
}
let state = State.state

open Quint.State
open Quint.Rng.Ops

/// ACTIONS

let move (p:player) (c:coord) : action [Board] = !@ (
  let! b = !Board in
  (  chk (is_empty b c)
  &@ Board @= Map.put c p b
  )
)

let move_to_win (p:player) : nondet (action [Board]) = !? (
  let! b = !Board in
  let? copt = winning_move_for_player p b in
  match copt with
  | Some c -> move p c
  | None   -> fail
)

let move_to_block (p:player) : nondet (action [Board]) = !? (
  let! b = !Board in
  let? copt = blocking_move_for_player p b in
  match copt with
  | Some c -> move p c
  | None   -> fail
)

// NOTE: The mode annotation can be inferred
let move_to_center (p:player) = !@ (
  let! b = !Board in
  (  chk (board_is_empty b)
  &@ move p (2, 2))
)

let move_to_set_up_win (p:player) : nondet (action [Board]) = !? (
  let! b = !Board in
  let? copt = set_up_win_for_player p b in
  match copt with
  | Some c -> move p c
  | None   -> fail
)

let move_to_empty (p:player) : nondet (action [Board]) = !? (
  let! b = !Board in
  match? free_space p b with
  | Some c -> move p c
  | None   -> fail
)

let move_to_corner (p:player) : nondet (action [Board]) = !? (
  let! b = !Board in
  let? corner = one_of corners in
  (  chk (board_is_empty b)
  &@ move p corner)
)

let next_turn : action [Next_turn] = !@ (
  let! b = !Board
  and! p = !Next_turn
  in
  (  chk (not (board_is_full b))
  &@ (if p = X then
        Next_turn @= O
      else
        Next_turn @= X)
  )
)

// TODO Need to integrate nondet within action state
let move_player (p:player) : nondet (action [Board; Next_turn]) = !? (
  let! b = !Board
  and! p' = !Next_turn
  in
  // TODO This can be removed by integrating nondet as an effect alongside reads and updates
  let? corner = move_to_corner p
  and? win = move_to_win p
  and? block = move_to_block p
  and? set_up_win = move_to_set_up_win p
  and? empty = move_to_empty p
  in
  (  chk (p = p')
  &@ chk (not (game_over b))
  &@ next_turn
  &@ (  corner
     |@ win
     |@ block
     |@ move_to_center p
     |@ set_up_win
     |@ empty )
  )
)
