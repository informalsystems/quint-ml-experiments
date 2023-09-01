module Quint.Util

let ( |> ) #a #b (x:a) (f:a -> b a) : b a = f x
