
type t = {
  a : int;
  b : bool;
} deriving (Record, Record_functor)

module Record :
  Deriving_Record.Record
    with
      type a = t and
      type 'res record_fun = a:int -> b:bool -> 'res =
  Record_t

module Functor :
  Deriving_Record.Functor.Functor
    with
      type a = t and
      type 'a field = 'a Record_t.field =
  Functor_t

module A = struct type 'a t = A of 'a end
module Codomain :
  Deriving_Record.Functor.S
    with
      type a = t and
      type 'a field = 'a Record_t.field =
  Functor_t.Make (A)
