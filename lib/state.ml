type 'a loc = [>] as 'a

let empty : 'a loc list = []

let var (v : 'a) (vs : 'b loc list) : 'b loc list = v :: vs

class type st = object
  method x : int
end

class type st' = object
  inherit st

  method y : string
end
