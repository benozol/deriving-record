
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
      flip List.map names @ fun name ->
        <:rec_binding< $lid:name$ = $lid:name$ >>
    in
    <:expr<
      { $Ast.rbSem_of_list fields$ }
    >>

  let record_fun names initial =
    let folder name sofar =
      <:expr< fun ~ $lid:name$ -> $sofar$ >>
    in
    List.fold_right folder names initial

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
              type_field ; type_any_field ; val_fields ;
              val_get ]$
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
              flip2 List.map2 names f_types @ fun name typ ->
                _loc, name, false, typ
            in
            <:str_item<
              type t = { $Ast.record_type_of_list fields$ }
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
              let get (type x) record : x $uid:"Record_"^cname$.field -> x F.t =
                function $Ast.mcOr_of_list cases$
            >>
          in
          <:str_item<
            module Make (F : Deriving_Record.T) = struct
              $Ast.stSem_of_list
                [ type_t ; type_f ; val_get ;
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
            module Map (Domain : Deriving_Record.Codomain with type 'a field = 'a $uid:"Record_"^cname$.field)
              (Codomain : Deriving_Record.Codomain with type a = Domain.a and type 'a field = 'a $uid:"Record_"^cname$.field) =
            struct
              type field_map = { field_map : 'a . 'a Domain.f -> 'a $uid:"Record_"^cname$.field -> 'a Codomain.f }
              let map = $map_expr$
            end
          >>
        in
        let type_field =
          <:str_item<
            type 'a field = 'a $uid:"Record_"^cname$.field ;;
          >>
        in
        <:str_item<
          module $uid:"Functor_"^cname$ = struct
            $Ast.stSem_of_list
              [ type_a cname ; type_field ;
                module_make ; module_map ]$
          end
        >>

    let generate_sigs _ = <:sig_item< >>
  end

  module Functor = Base.Register (Description) (Builder)

end
