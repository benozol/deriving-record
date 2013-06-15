
module type T = sig
  type 'a t
end

module type Record = sig
  type a
  type 'res record_fun
  val record : (a -> 'res) -> 'res record_fun
  type 'a field
  type any_field = Any : _ field -> any_field
  val get : a -> 'a field -> 'a
  val fields : any_field list
end

module type Fields = sig
  type a
end

(* module type Codomain = sig *)
(*   type a        (\* original type *\) *)
(*   type t        (\* functor's codomain type *\) *)
(*   type 'a f     (\* functor per field with type 'a *\) *)
(*   type 'a field (\* original type's field *\) *)
(*   val get : t -> 'a field -> 'a f *)
(* end *)

module type S = sig
  type a
  type 'f field
  type t
  type 'a f
  type 'res record_fun
  val record : (t -> 'res) -> 'res record_fun
  val unrecord : t -> ('res record_fun) -> 'res
  type field_init = { field_init : 'a . 'a field -> 'a f }
  val init : field_init -> t
  val get : t -> 'a field -> 'a f
end

module type Functor = sig

  type a
  type 'a field

  module Make : functor (F : T) -> S with type a = a and type 'a field = 'a field

  module Map : functor (Domain : S) -> functor (Codomain : S with type a = Domain.a and type 'a field = 'a Domain.field) -> sig
    type field_map = { field_map : 'a . 'a field -> 'a Domain.f -> 'a Codomain.f }
    val map : field_map -> Domain.t -> Codomain.t
  end
end
