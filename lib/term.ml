open Containers

type 'a set = S : 'a set
type ('k, 'v) map = M : ('k, 'v) map

type _ t =
  | Int : int -> int t
  | Str : string -> string t
  | Lst : 'a t list -> 'a list t
  | Set : 'a t list -> 'a set t
  | Map : ('k t * 'v t) list -> ('k, 'v) map t

let rec compare : type a. a t -> a t -> int =
 fun a b ->
  match (a, b) with
  | Int a, Int b -> Int.compare a b
  | Str a, Str b -> String.compare a b
  | Lst a, Lst b -> List.compare compare a b
  | Set a, Set b -> List.compare compare a b
  | Map a, Map b -> List.compare (Pair.compare compare compare) a b

let rec equal : type a. a t -> a t -> bool = fun a b -> compare a b = 0
let int : int -> int t = fun i -> Int i
let str : string -> string t = fun i -> Str i

let list : type a. (a -> a t) -> a list -> a list t =
 fun typ ls -> Lst (List.map typ ls)

let set : type a b. (a -> b t) -> a list -> b set t =
 fun typ ls -> Set (List.map typ ls |> List.sort_uniq ~cmp:compare)

let map :
    type k k' v v'. (k -> k' t) -> (v -> v' t) -> (k * v) list -> (k', v') map t
    =
 fun fk fv entries -> Map (List.map (fun (k, v) -> (fk k, fv v)) entries)

let get : type k v. k t -> (k, v) map t -> v t option =
 fun k (Map entries) ->
  let f (k', v) =
    if equal k k' then
      Some v
    else
      None
  in
  List.find_map f entries

let (_ : int set t) = set int [ 1; 2; 3 ]
let (_ : int list set t) = set (list int) [ [ 1 ] ]
let (_ : int set set t) = set (set int) [ [ 1 ] ]

let m : (int, string) map t =
  map int str [ (1, "one"); (2, "two"); (3, "three") ]

let (_ : string t option) = get (int 1) m
