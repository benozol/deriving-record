
open Pa_deriving_common
open Utils

let (@) f x = f x
let (@@) = List.append
let (-|) f g = fun x -> f (g x)
let flip f x y = f y x
let flip2 f x y z = f z x y

module Aux (Description : Defs.ClassDescription) (Loc : Defs.Loc) = struct

  module Helpers = Base.AstHelpers(Loc)

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
  let record_lid = "record"
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

    include Aux (Description) (Loc)
    module Generator = Base.Generator(Loc)(Description)

    open Loc
    open Camlp4.PreCast
    open Description

    let generate =
      for_record classname @ fun ~cname ~params ~fields ~constraints ->
        let names, types = names_types fields in
        let upper_names = List.map String.capitalize names in
        let ast_types = List.map Helpers.Untranslate.expr types in
        let field_variants =
          let variants =
            flip2 List.map2 upper_names types @ fun name typ ->
              Ast.(TyCol (_loc,
                          TyId (_loc, IdUid (_loc, name)),
                          <:ctyp< $Helpers.Untranslate.expr typ$ field >>))
          in
          Ast.TySum (_loc, Ast.tyOr_of_list variants)
        in
        let any_field_variant =
          <:ctyp<
            | Any_field : _ field -> any_field
          >>
        in
        let val_get_cases record =
          flip2 List.map2 names upper_names @ fun name upper_name ->
            <:match_case< $uid:upper_name$ -> $record$.$lid:name$ >>
        in
        let field_exprs =
          flip List.map upper_names @ fun upper_name ->
            <:expr< Any_field $uid:upper_name$ >>
        in
        (* let with_constr = *)
        (*   <:with_constr< *)
        (*     type a = $lid:cname$ and *)
        (*     type 'res record_fun = $record_fun_types names ast_types res$ *)
        (*   >> *)
        (* in *)
        let k_res = <:expr< $lid_expr k$ $record names$ >> in
        let get_fun =
          <:expr<
            fun field $lid_pattern record_lid$ ->
              match field with
                | $Ast.mcOr_of_list (val_get_cases (lid_expr record_lid))$
          >>
        in
        <:str_item<
          module $uid:"Record_"^cname$ (* : Deriving_Record.Record with $with_constr$ *) =
          struct
            type a = $lid:cname$
            type record_fun $res$ = $record_fun_types names ast_types res$ ;;
            type _ field = $field_variants$
            type any_field = $any_field_variant$
            let record $lid_pattern k$ = $record_fun names k_res$
            let fields = $Helpers.expr_list field_exprs$
            let get : type f . f field -> a -> f = $get_fun$
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

    module Generator = Base.Generator(Loc)(Description)

    include Aux (Description) (Loc)

    open Loc
    open Camlp4.PreCast
    open Description

    let generate =
      for_record classname @ fun ~cname ~params ~fields ~constraints ->
        let names, types = names_types fields in
        let upper_names = List.map String.capitalize names in
        let f_types =
          flip List.map types @ fun typ ->
            <:ctyp< $Helpers.Untranslate.expr typ$ F.t >>
        in
        let type_t =
          let fields =
            Ast.record_type_of_list @
              flip2 List.map2 names f_types @ fun name typ ->
                _loc, name, false, typ
          in
          <:ctyp< { $fields$ } >>
        in
        let record_fun_expr =
          let k_res = <:expr< $lid_expr k$ $record names$ >> in
          <:expr<
            fun $lid_pattern k$ -> $record_fun names k_res$
          >>
        in
        let type_init_field =
          <:ctyp<
            { init_field : 'a . 'a $uid:"Record_"^cname$.field -> 'a F.t }
          >>
        in
        let init_expr =
          let fields =
            Ast.rbSem_of_list @
              flip2 List.map2 names upper_names @ fun name upper_name ->
                <:rec_binding<
                  $lid:name$ = init_field.init_field $id:field_variant cname upper_name$
                >>
          in
          <:expr<
            fun init_field -> { $fields$ }
          >>
        in
        let get_expr =
          let cases =
            flip2 List.map2 upper_names names @ fun upper_name name ->
              <:match_case< $uid:"Record_"^cname$.$uid:upper_name$ -> record . $lid:name$ >>
          in
          <:expr<
            fun field record ->
              match field with
                | $Ast.mcOr_of_list cases$
          >>
        in
        (* let with_constr = *)
        (*   <:with_constr< *)
        (*     type t = $type_t$ and *)
        (*     type 'a f = 'a F.t and *)
        (*     type 'res record_fun = $record_fun_types names f_types res$ and *)
        (*     type init_field = $type_init_field$ *)
        (*   >> *)
        (* in *)
        <:str_item<
          module $uid:"Functor_"^cname$ = struct
            type a = $lid:cname$
            type 'a field = 'a $uid:"Record_"^cname$.field
            module Make (F : Deriving_Record.T) = struct
              type a = $lid:cname$
              type t = $type_t$
              type 'a f = 'a F.t
              type 'a field = 'a $uid:"Record_"^cname$.field
              type record_fun $res$ = $record_fun_types names f_types res$
              type init_field = $type_init_field$
              let record = $record_fun_expr$
              let init = $init_expr$
              let get : type x . x field -> t -> x f = $get_expr$
            end
            module Identity = struct
                include Make (struct type 'a t = 'a end)
                let import record =
                  init
                    { init_field = fun field ->
                        $uid:"Record_"^cname$.get field record }
            end
          end
        >>

    let generate_sigs _ = <:sig_item< >>
  end

  module Functor = Base.Register (Description) (Builder)

end
