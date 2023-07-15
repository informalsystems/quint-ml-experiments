module type State = sig
  type t
end

module type Scheduler = functor (S : State) -> sig
  type 'a t
  val any : S.t t list -> S.t t
  val all : S.t t list -> S.t list t
end

module Simulate  : Scheduler = functor (S : State) -> struct
  type 'a t = 'a
  let any ls = List.hd ls
  let all ls = ls
end

module Execute : Scheduler = functor (S : State) -> struct
  type 'a t = 'a Lwt.t
  let any = Lwt.pick
  let all = Lwt.all
end

let ex = Lwt.pick [Lwt.return "fii"; Lwt.return "fart"]
