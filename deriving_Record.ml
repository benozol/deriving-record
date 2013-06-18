
module type T = sig
  type 'a t
end

module type Record = sig
  type a
  type 'res record_fun
  val record : (a -> 'res) -> 'res record_fun
  type 'a field
  type any_field = Any_field : _ field -> any_field
  val get : 'a field -> a -> 'a
  val fields : any_field list
end

module Identity = struct
  type 'a t = 'a
end

module Functor = struct

  module type S = sig
    type a
    type 'f field
    type t
    type 'a f
    type 'res record_fun
    val record : (t -> 'res) -> 'res record_fun
    type init_field = { init_field : 'a . 'a field -> 'a f }
    val init : init_field -> t
    val get : 'a field -> t -> 'a f
  end

  module type Functor = sig
    type a
    type 'a field
    module Make : functor (F : T) -> S with type a = a and type 'a f = 'a F.t and type 'a field = 'a field
    module Identity : sig
      include S with type a = a and type 'a f = 'a and type 'a field = 'a field
      val import : a -> t
    end
  end

  module Map
    (Domain : S)
    (Codomain : S with type a = Domain.a and type 'a field = 'a Domain.field) =
  struct
    type map_field = { map_field : 'f . 'f Domain.field -> 'f Domain.f -> 'f Codomain.f }
    let map =
      fun map_field record ->
        Codomain.init
          { Codomain.init_field = fun field ->
              map_field.map_field field (Domain.get field record) }
  end

  module Import (Record : Record) (Functor : Functor with type a = Record.a and type 'a field = 'a Record.field) :
  sig
    val import : Record.a -> Functor.Make (Identity).t
  end =
  struct
    module Identity = Functor.Make (Identity)
    let import record =
      Identity.init
        { Identity.init_field = fun field ->
            Record.get field record }
  end
end
