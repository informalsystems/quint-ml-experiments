/// An adaptation of https://github.com/informalsystems/quint/blob/main/examples/puzzles/tictactoe/tictactoe.qnt
module Quint.Ex.TicTacToe

open FStar.Order
open Quint.Ordered

module Map = Quint.Map
module Ordered = Quint.Ordered
module State = Quint.State
module Set = Quint.Set
module IO = FStar.IO

open Quint.Util

// Just a helper to expose the set constructor
let set #a {| ordered a |} (l: list a): s:Set.t a{Set.preserves_nonempty l s.ls} = Set.set l



/// DATA

type player =
  | O
  | X

let player_to_string : player -> string = function
  | X -> "X"
  | O -> "O"

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
  None? (Map.get c b)

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



/// NONDET FUNCTIONS

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

instance state_sig : State.sig = State.state_signature
  /// State variables
  [ "board"
  ; "next turn" ]
  /// State variable types
  (function
  | "board"     -> board
  | "next turn" -> player)

open Quint.State
open Quint.Rng.Ops

// Short hands for read and action annotations
let action = State.action #state_sig
let read   = State.read #state_sig



/// ACTIONS

let move (p:player) (c:coord) : action ["board"] = !@ (
  // Read a state variable
  let! b = !"board" in
  // Perform an action
  (  chk (is_empty b c)        // Check a pure boolean molds
  &@ "board" @= Map.put c p b  // Update the "board" state variable
  )
)

let move_to_win (p:player) : nondet (action ["board"]) = !? (
  let! b = !"board" in
  let? copt = winning_move_for_player p b in
  match copt with
  | Some c -> move p c
  | None   -> fail
)

let move_to_block (p:player) : nondet (action ["board"]) = !? (
  let! b = !"board" in
  let? copt = blocking_move_for_player p b in
  match copt with
  | Some c -> move p c
  | None   -> fail
)

// NOTE: The mode annotation can be inferred
let move_to_center (p:player) = !@ (
  let! b = !"board" in
  (  chk (board_is_empty b)
  &@ move p (2, 2))
)

let move_to_set_up_win (p:player) : nondet (action ["board"]) = !? (
  let! b = !"board" in
  let? copt = set_up_win_for_player p b in
  match copt with
  | Some c -> move p c
  | None   -> fail
)

let move_to_empty (p:player) : nondet (action ["board"]) = !? (
  let! b = !"board" in
  match? free_space p b with
  | Some c -> move p c
  | None   -> fail
)

let move_to_corner (p:player) : nondet (action ["board"]) = !? (
  let! b = !"board" in
  let? corner = one_of corners in
  (  chk (board_is_empty b)
  &@ move p corner)
)

let next_turn : action ["next turn"] = !@ (
  let! b = !"board"
  and! p = !"next turn"
  in
  (  chk (not (board_is_full b))
  &@ (if p = X then
        "next turn" @= O
      else
        "next turn" @= X)
  )
)

// TODO Need to integrate nondet within action state
let move_player (p:player) : nondet (action ["board"; "next turn"]) = !? (
  let! b = !"board" in
  // TODO This can be removed by integrating nondet as an effect alongside reads and updates
  let? corner = move_to_corner p
  and? win = move_to_win p
  and? block = move_to_block p
  and? set_up_win = move_to_set_up_win p
  and? empty = move_to_empty p
  in
  (  chk (not (game_over b))
  &@ (  corner
     |@ win
     |@ block
     |@ move_to_center p
     |@ set_up_win
     |@ empty )
  &@ next_turn)
)

let step : nondet transition = !? (
  let! p = !"next turn" in
  let? move = move_player p
  in
  move
)

let init : State.init_t #state_sig  = function
  | "board"     -> Map.empty #coord #player
  | "next turn" -> X



// Utilities for running and printing the compiled executable

module List = FStar.List.Tot

module DM = FStar.DependentMap

let pos_to_string : option player -> string = function
  | Some p -> player_to_string p
  | None   -> " "

let rec aux (m:board) : l:list coord -> Tot (string) (decreases l) = function
  | [] -> ""
  | xy0 :: xy1 :: xy2 :: rest ->
    "" ^ pos_to_string (Map.get xy0 m) ^ "|" ^ pos_to_string (Map.get xy1 m) ^ "|" ^ pos_to_string (Map.get xy2 m) ^ "" ^ "\n-----\n" ^ aux m rest
  | _ ::  [] -> ""
  | _ :: _ :: [] -> ""

// TODO: Print functions for board
let board_to_string : board -> string =
  fun m ->
  "\n-----\n" ^
  aux m board_coordinates.ls

let state_to_string : s:state #state_sig{is_updated s} -> string =
  fun s ->
  "board:\n" ^
  board_to_string (Some?.v (DM.sel s "board"))
  ^ "\nnext player: " ^ player_to_string (Some?.v (DM.sel s "next turn")) ^ "\n"

let debug_trace steps seed =
  let trace = State.run steps init step seed in
  List.fold_left (fun acc s -> acc ^ "\n=========\n" ^ state_to_string s) "" trace



// Example of an inline test of a trace using a give seed (0)
let _ex_run_1  = normalize_term (
  debug_trace 2 0
  =
  "=========
board:

-----
 | |
-----
 | |
-----
 | |
-----

next player: X

=========
board:

-----
X| |
-----
 | |
-----
 | |
-----

next player: O

=========
board:

-----
X|O|
-----
 | |
-----
 | |
-----

next player: X"
)
