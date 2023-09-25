module State = Lang.Quint_State
module Ex = Lang.Quint_Ex_TicTacToe

let trace_tic_tac_toe ?(seed=0) ?(steps=10) () =
  let steps = Prims.of_int steps in
  let seed = Prims.of_int seed in
  Ex.debug_trace steps seed
