
open Pa_deriving_common
open Utils

let (@) f x = f x
let (@@) = List.append
let (-|) f g = fun x -> f (g x)
let flip f x y = f y x
let flip2 f x y z = f z x y

module Aux (Description : Defs.ClassDescription) (Loc : Defs.Loc) = struct

  open Loc
  open Camlp4.PreCast
  open Description

  let names_types fields =
    List.split @
      flip List.map fields @ function
        | name, (params, typ), _ ->
          if params <> [] then
            raise @ Base.Underivable (classname^" only derivible for nullary polymorphic variants");
          name, typ

  let type_a cname =
    <:str_item<
      type a = $lid:cname$
    >>

  let res =
    <:ctyp< 'res >>

  let k = "k"
  let lid_pattern x = <:patt< $lid:x$ >>
  let lid_expr x = <:expr< $lid:x$ >>

  let field_variant cname upper_name =
    <:ident< $uid:"Record_"^cname$ . $uid:upper_name$ >>

  let record_fun_types names types res =
    let folder name typ sofar =
      <:ctyp< $lid:name$:$typ$ -> $sofar$ >>
    in
    List.fold_right2 folder names types res

  let pattern names =
    let fields =
      flip List.map names @ fun name ->
        <:patt< $lid:name$ = $lid:name$ >>
    in
    <:patt< { $Ast.paSem_of_list fields$ } >>

  let record names =
    let fields =
      Ast.rbSem_of_list @
        flip List.map names @ fun name ->
          <:rec_binding< $lid:name$ = $lid:name$ >>
    in
    <:expr<
      { $fields$ }
    >>

  let record_fun names initial =
    let folder name sofar =
      <:expr< fun ~ $lid:name$ -> $sofar$ >>
    in
    <:expr<
      $List.fold_right folder names initial$
    >>

  let for_record classname f : Pa_deriving_common.Type.decl list -> Camlp4.PreCast.Ast.str_item =
    let for_decl = function
      | cname, params, `Fresh (_, Type.Record fields, _), constraints, _  ->
        f ~cname ~params ~fields ~constraints
      | _ ->
        raise @ Base.Underivable (classname^" only derivible for records")
    in
    Camlp4.PreCast.Ast.stSem_of_list -| List.map for_decl
end

module Record = struct

  module Description : Defs.ClassDescription = struct
    let classname = "Record"
    let runtimename = "Deriving_Record.Record"
    let default_module = None
    let alpha = None
    let allow_private = true
    let predefs = []
    let depends = []
  end

  module Builder (Loc : Defs.Loc) = struct

    module Helpers = Base.AstHelpers(Loc)
    module Generator = Base.Generator(Loc)(Description)

    include Aux (Description) (Loc)

    open Loc
    open Camlp4.PreCast
    open Description

    let generate =
      for_record classname @ fun ~cname ~params ~fields ~constraints ->
        let names, types = names_types fields in
        let upper_names = List.map String.uppercase names in
        let type_record_fun =
          let types = List.map Helpers.Untranslate.expr types in
          <:str_item<
            type 'res record_fun = $record_fun_types names types res$
          >>
        in
        let val_record =
          let k_res = <:expr< $lid_expr k$ $record names$ >> in
          <:str_item<
            let record $lid_pattern k$ = $record_fun names k_res$
          >>
        in
        let type_field =
          let variants =
            flip2 List.map2 upper_names types @ fun name typ ->
              Ast.(TyCol (_loc,
                          TyId (_loc, IdUid (_loc, name)),
                          <:ctyp< $Helpers.Untranslate.expr typ$ field >>))
          in
          <:str_item<
            type _ field = $Ast.TySum (_loc, Ast.tyOr_of_list variants)$
          >>
        in
        let type_any_field =
          <:str_item<
            type any_field = Any_field : _ field -> any_field
          >>
        in
        let val_get =
          let cases =
            flip2 List.map2 names upper_names @ fun name upper_name ->
              <:match_case< $uid:upper_name$ -> record.$lid:name$ >>
          in
          <:str_item<
            let get record (type x) : x field -> x = function $Ast.mcOr_of_list cases$
          >>
        in
        let val_fields =
          let exprs =
            flip List.map upper_names @ fun upper_name ->
              <:expr< Any_field $uid:upper_name$ >>
          in
          <:str_item<
            let fields = $Helpers.expr_list exprs$
          >>
        in
        <:str_item<
          module $uid:"Record_"^cname$ = struct
            $Ast.stSem_of_list [
              type_a cname ; type_record_fun ; val_record ;
                type_field ; type_any_field ; val_fields ; val_get ]$

          end
        >>

    let generate_sigs _ = <:sig_item< >>

  end

  module Record = Base.Register (Description) (Builder)

end

module Functor = struct

  module Description : Defs.ClassDescription = struct
    let classname = "Record_functor"
    let runtimename = "Deriving_Record.Functor"
    let default_module = None
    let alpha = None
    let allow_private = true
    let predefs = []
    let depends = []
  end

  module Builder (Loc : Defs.Loc) = struct

    module Helpers = Base.AstHelpers(Loc)
    module Generator = Base.Generator(Loc)(Description)

    include Aux (Description) (Loc)

    open Loc
    open Camlp4.PreCast
    open Description

    let generate =
      for_record classname @ fun ~cname ~params ~fields ~constraints ->
        let names, types = names_types fields in
        let upper_names = List.map String.uppercase names in
        let f_types =
          flip List.map types @ fun typ ->
            <:ctyp< $Helpers.Untranslate.expr typ$ F.t >>
        in
        let module_make =
          let type_t =
            let fields =
              Ast.record_type_of_list @
                flip2 List.map2 names f_types @ fun name typ ->
                  _loc, name, false, typ
            in
            <:str_item<
              type t = { $fields$ }
            >>
          in
          let type_f =
            <:str_item<
              type 'a f = 'a F.t
            >>
          in
          let type_record_fun =
            <:str_item<
              type 'res record_fun = $record_fun_types names f_types res$
            >>
          in
          let val_record_fun =
            let k_res = <:expr< $lid_expr k$ $record names$ >> in
            <:str_item<
              let record $lid_pattern k$ = $record_fun names k_res$
            >>
          in
          let type_field_init =
            <:str_item<
              type field_init = { field_init : 'a . 'a $uid:"Record_"^cname$.field -> 'a F.t }
            >>
          in
          let val_init =
            let fields =
              Ast.rbSem_of_list @
                flip2 List.map2 names upper_names @ fun name upper_name ->
                  <:rec_binding<
                    $lid:name$ = f.field_init $id:field_variant cname upper_name$
                  >>
            in
            <:str_item<
              let init f = { $fields$ }
            >>
          in
          let val_get =
            let cases =
              flip2 List.map2 upper_names names @ fun upper_name name ->
                <:match_case< $uid:"Record_"^cname$.$uid:upper_name$ -> record . $lid:name$ >>
            in
            <:str_item<
              let get (type x) record : x $uid:"Record_"^cname$.field -> x F.t = function $Ast.mcOr_of_list cases$
            >>
          in
          <:str_item<
            module Make (F : Deriving_Record.T) = struct
              $Ast.stSem_of_list [ type_t ; type_f ; val_get ;
                                   type_record_fun ; val_record_fun ;
                                   type_field_init ; val_init ]$
            end
          >>
        in
        let module_map =
          let map_expr =
            <:expr<
              fun field_map record ->
                Codomain.init
                  { Codomain.field_init = fun field ->
                      field_map.field_map (Domain.get record field) field }
            >>
          in
          <:str_item<
            module Map (Domain : Deriving_Record.Functor.S with type 'a field = 'a $uid:"Record_"^cname$.field)
              (Codomain : Deriving_Record.Functor.S with type a = Domain.a and type 'a field = 'a $uid:"Record_"^cname$.field) =
            struct
              type field_map = { field_map : 'a . 'a Domain.f -> 'a $uid:"Record_"^cname$.field -> 'a Codomain.f }
              let map = $map_expr$
            end
          >>
        in
        <:str_item<
          module $uid:"Functor_"^cname$ = struct
            $type_a cname$ ;;
            type 'a field = 'a $uid:"Record_"^cname$.field ;;
            $Ast.stSem_of_list [ module_make ; module_map ]$
          end
        >>

    let generate_sigs _ = <:sig_item< >>
  end

  module Functor = Base.Register (Description) (Builder)

end

(* module Builder (Loc : Defs.Loc) = struct *)

(*   module Helpers = Base.AstHelpers(Loc) *)
(*   module Generator = Base.Generator(Loc)(Description) *)

(*   open Loc *)
(*   open Camlp4.PreCast *)
(*   open Description *)

(*   let for_sum variants cname names = *)
(*     let lower_names = List.map String.lowercase names in *)
(*     let cols vars = *)
(*       let f name var = *)
(*         Ast.TyCol (_loc, <:ctyp< $lid:name$ >>, <:ctyp< '$var$ >>) *)
(*       in *)
(*       Ast.tySem_of_list @ *)
(*         List.map2 f lower_names vars *)
(*     in *)
(*     let res = <:ctyp< 'res >> in *)
(*     let record = *)
(*       let ctyp = *)
(*         Ast.record_type_of_list @ *)
(*           flip List.map lower_names @ fun name -> *)
(*             _loc, name, false, <:ctyp< '$name$ >> *)
(*       in *)
(*       <:str_item< type record 'a = { $ctyp$ } constraint 'a = < $cols lower_names$ > >> *)
(*     in *)
(*     let record_fun_type = *)
(*       let ctyp = *)
(*         let label name sofar = *)
(*           <:ctyp< $lid:name$:'$name$ -> $sofar$ >> *)
(*         in *)
(*         List.fold_right label lower_names res *)
(*       in *)
(*       <:str_item< type record_fun 'a $res$ = ('a record -> 'res) -> $ctyp$ constraint 'a = < $cols lower_names$ > >> *)
(*     in *)
(*     let mono = *)
(*       let aaa = *)
(*         Array.to_list @ *)
(*           Array.make (List.length names) "a" *)
(*       in *)
(*       <:str_item< type 'a mono = < $cols aaa$ > record >> *)
(*     in *)
(*     let record_fun = *)
(*       let folder name sofar = *)
(*         <:expr< fun ~ $lid:String.lowercase name$ -> $sofar$ >> *)
(*       in *)
(*       let fields = *)
(*         Ast.rbSem_of_list @ *)
(*           flip List.map lower_names @ fun name -> *)
(*             <:rec_binding< $lid:name$ = $lid:name$ >> *)
(*       in *)
(*       let expr = *)
(*         List.fold_right folder lower_names <:expr< k { $fields$ } >> *)
(*       in *)
(*       <:str_item< let record k = $expr$ >> *)
(*     in *)
(*     let get_fun = *)
(*       let cases = *)
(*         flip List.map names @ fun name -> *)
(*           let pattern = *)
(*             match variants with *)
(*               | `Variant -> <:patt< `$name$ >> *)
(*               | `Sum -> <:patt< $uid:name$ >> *)
(*           in *)
(*           <:match_case< $pattern$ -> record . $lid:String.lowercase name$ >> *)
(*       in *)
(*       <:str_item< let get record = function $Ast.mcOr_of_list cases$ >> *)
(*     in *)
(*     <:str_item< *)
(*       module $uid:"Record_"^cname$ = struct *)
(*         $Ast.stSem_of_list [ record ; record_fun_type ; record_fun ; mono ; get_fun ]$ *)
(*       end *)
(*     >> *)

(*   let for_record ~cname ~params ~fields ~constraints ~bool = *)
(*     let funct = *)
(*       let decl : Type.decl = *)
(*         let fields' = *)
(*           flip List.map fields @ fun (name, (params, expr), mutability) -> *)
(*             let expr' = *)
(*               `Constr (["F";"t"], [ expr ]) *)
(*             in *)
(*             name, (params, expr'), mutability *)
(*         in *)
(*         "t", params, `Fresh (None, Type.Record fields', `Public), constraints, bool *)
(*       in *)
(*       <:str_item< *)
(*         module Functor (F : sig type 'a t end) = struct *)
(*           type $Helpers.Untranslate.decl decl$ *)
(*         end *)
(*       >> *)
(*     in *)
(*     let alias : Type.decl = *)
(*       let expr : Type.rhs = *)
(*         let params' : Type.expr list = List.map (fun param -> `Param param) params in *)
(*         `Expr (`Constr ([cname], params')) *)
(*       in *)
(*       "a", params, expr, [], bool *)
(*     in *)
(*     <:str_item< *)
(*       module $uid:"Record_"^cname$ = struct *)
(*         type $Helpers.Untranslate.decl alias$ *)
(*         $funct$ *)
(*       end *)
(*     >> *)
(*   let generate = *)
(*     let for_decl : Type.decl -> Ast.str_item = function *)
(*       | cname, _, `Variant (_, tags), _, _ -> *)
(*         let names = *)
(*           flip List.map tags @ function *)
(*             | Type.Tag (name, []) -> name *)
(*             | Type.Tag (name, _) -> *)
(*               raise @ Base.Underivable (classname^" cannot be derived because the tag "^name^" is not nullary") *)
(*             | Type.Extends _ -> *)
(*               raise @ Base.Underivable (classname^" cannot be derived from variant extension") *)
(*         in *)
(*         for_sum `Variant cname names *)
(*       | cname, _, `Fresh (_, Type.Sum summands, _), _, _ -> *)
(*         let names = *)
(*           flip List.map summands @ function *)
(*             | (name, []) -> name *)
(*             | (name, _::_) -> *)
(*               raise @ Base.Underivable (classname^" cannot be derived because the tag "^name^" is not nullary") *)
(*         in *)
(*         for_sum `Sum cname names *)
(*       | cname, params, `Fresh (_, Type.Record fields, _), constraints, bool -> *)
(*         for_record ~cname ~params ~fields ~constraints ~bool *)
(*       | _ -> *)
(*         raise @ Base.Underivable (classname^" only derivible for nullary polymorphic variants") *)
(*     in *)
(*     fun decls -> *)
(*       Ast.stSem_of_list *)
(*         (List.map for_decl decls) *)

(*   let generate_sigs _ = <:sig_item< >> *)

(* end *)

(* module Record = Base.Register (Description) (Builder) *)
