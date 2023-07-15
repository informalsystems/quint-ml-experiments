module Type = struct
  type t =
    | Bool
    | Int
    | Str
    | Var of string
end

module Functional = struct
  let c = 2
end
