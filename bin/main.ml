let usage_msg = "quint-ml-demo [-s seed] [-l length]"
let seed = ref (-1)
let steps = ref 10

let speclist =
  [("-seed", Arg.Set_int seed, "The seed to use for the RNG (defaults to a randomly selected seed)");
   ("-steps", Arg.Set_int steps, "The length of steps to run the simulation for")]

let () =
  Random.self_init ();
  Arg.parse speclist (fun _ -> ()) usage_msg;
  let seed = match !seed with
    | -1 -> Random.full_int max_int
    | n -> n
  in
  Printf.printf "Seed: %i" seed;
  print_endline (Quint_ml.Fdep.trace_tic_tac_toe ~seed ~steps:(!steps) ())
