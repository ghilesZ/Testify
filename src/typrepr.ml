open Migrate_parsetree
open Ast_410
open Parsetree
open Helper
open Location

(** {1 Internal representation of an OCaml type} *)

type t =
  { id: string
  ; boltz: (Boltz.t, string) Result.t
        (** Combinatorial specification of the type *)
  ; of_arbogen: (expression, string) Result.t
        (** AST of a function that converts an arbogen tree to the current
            type *)
  ; tag: int option
  ; collector: expression option
        (** AST of a function collecting values subject to a global
            constraint in an inhabitant of the type. *)
  ; spec: expression option  (** AST of a predicate over the current type *)
  ; gen: expression option
        (** AST of a random sampler for the current type *)
  ; card: Card.t  (** Cardinality of the type *)
  ; print: expression  (** AST of a pretty-printer for the type *) }

(** {2 Printing} *)

let print fmt {id; gen; spec; card; print; boltz; of_arbogen; collector; _} =
  Format.fprintf fmt "- type %s\n" id ;
  let print_expr fmt =
    Format.fprintf fmt "\n```ocaml@,%a```\n" print_expression
  in
  let print_opt f fmt = function
    | None -> Format.fprintf fmt "none"
    | Some e -> f fmt e
  in
  let print_res f fmt = function
    | Ok x -> f fmt x
    | Error msg -> Format.fprintf fmt "Absent because: %s" msg
  in
  Format.fprintf fmt "- Cardinality: %a\n" Card.pp card ;
  Format.fprintf fmt "- Printer:\n%a\n" print_expr print ;
  Format.fprintf fmt
    "@[<v 2><details>@,<summary>Collector</summary>@,%a\n</details>@]\n"
    (print_opt print_expr) collector ;
  Format.fprintf fmt "- Specification:\n%a\n" (print_opt print_expr) spec ;
  Format.fprintf fmt
    "@[<v 2><details>@,\
     <summary>Boltzmann specification</summary>@,\
     %a\n\
     </details>@]\n"
    (print_res Boltz.markdown)
    boltz ;
  Format.fprintf fmt
    "@.@[<v 2><details>@,<summary>Of_arbogen</summary>@,%a\n</details>@]\n"
    (print_res print_expr) of_arbogen ;
  Format.fprintf fmt "- Generator:\n%a\n" (print_opt print_expr) gen

(** {2 Constructors} *)

let empty loc (name : string) =
  let error args = Format.ksprintf Result.error args in
  { id= name
  ; boltz= error "No Boltzmann spec for type \"%s\"" name
  ; of_arbogen= error "No of_arbogen function for type \"%s\"" name
  ; gen= None
  ; spec= None
  ; card= Unknown
  ; print= [%expr fun _ -> "<...>"]
  ; collector= None
  ; tag= None }

let add_printer info p = {info with print= p}

let add_generator info g = {info with gen= Some g}

let add_specification info s = {info with spec= Some s}

let free id bs g c p of_arbogen col =
  { id
  ; boltz= Ok bs
  ; print= p
  ; gen= Some g
  ; spec= None
  ; card= c
  ; of_arbogen
  ; collector= Some col
  ; tag= None }

let make id boltz print gen spec card of_arbogen collector =
  {id; boltz; gen; spec; card; print; of_arbogen; collector; tag= None}

let end_module name typ =
  { typ with
    gen= Option.map (let_open name) typ.gen
  ; spec= Option.map (let_open name) typ.spec
  ; print= let_open name typ.print
  ; of_arbogen= Result.map (let_open name) typ.of_arbogen
  ; collector= Option.map (let_open name) typ.collector }

(** {2 Predefined types} *)

(** {3 Non-parametric types}*)
let unit =
  free "unit" Boltz.epsilon
    (exp_id "QCheck.Gen.unit")
    (Finite Z.one)
    (exp_id "QCheck.Print.unit")
    (Ok (exp_id "Testify_runtime.Arbg.to_unit"))
    (exp_id "Testify_runtime.Collect.unit")

let bool =
  free "bool" Boltz.epsilon
    (exp_id "QCheck.Gen.bool")
    (Card.of_int 2) (exp_id "string_of_bool")
    (Ok (exp_id "Testify_runtime.Arbg.to_bool"))
    (exp_id "Testify_runtime.Collect.bool")

let char =
  free "char" Boltz.epsilon
    (exp_id "QCheck.Gen.char")
    (Card.of_int 256) (exp_id "string_of_char")
    (Error "Not of_arbogen function for the type `char`")
    (exp_id "Testify_runtime.Collect.char")

let int =
  free "int" Boltz.epsilon (exp_id "QCheck.Gen.int")
    (Z.pow (Z.of_int 2) (Sys.int_size - 1) |> Card.finite)
    (exp_id "string_of_int")
    (Ok (exp_id "Testify_runtime.Arbg.to_int"))
    (exp_id "Testify_runtime.Collect.int")

let float =
  free "float" Boltz.epsilon
    (exp_id "QCheck.Gen.float")
    (Z.pow (Z.of_int 2) 64 |> Card.finite)
    (exp_id "string_of_float")
    (Ok (exp_id "Testify_runtime.Arbg.to_float"))
    (exp_id "Testify_runtime.Collect.float")

(** {3 Parametric types} *)

(** {4 constructors} *)
let param list = List.map (fun s -> (Typ.var s, Asttypes.Invariant)) list

let ptype ?manifest name params kind =
  { ptype_name= def_loc name
  ; ptype_params= List.map (fun s -> (Typ.var s, Asttypes.Invariant)) params
  ; ptype_cstrs= []
  ; ptype_kind= kind
  ; ptype_private= Asttypes.Public
  ; ptype_manifest= manifest
  ; ptype_attributes= []
  ; ptype_loc= !current_loc }

(** {2 Polymorphic types} *)

type param = {vars: string list; body: type_declaration}

let option_ =
  let vars = ["a"] in
  let alpha = [Typ.var "a"] in
  let body =
    let none = Type.constructor_s "None" in
    let some = Type.constructor_s ~args:(Pcstr_tuple alpha) "Some" in
    let kind = Ptype_variant [none; some] in
    ptype ~manifest:(Typ.constr_s "option" alpha) "option" vars kind
  in
  {vars; body}

let ref_ =
  let vars = ["a"] in
  let alpha = Typ.var "a" in
  let body =
    let contents = Type.field_s ~mut:Mutable "contents" alpha in
    let kind = Ptype_record [contents] in
    ptype ~manifest:(Typ.constr_s "ref" [alpha]) "ref" vars kind
  in
  {vars; body}

let result_ =
  let vars = ["a"; "b"] in
  let alpha = Typ.var "a" in
  let beta = Typ.var "b" in
  let body =
    let ok = Type.constructor ~args:(Pcstr_tuple [alpha]) (def_loc "Ok") in
    let error =
      Type.constructor ~args:(Pcstr_tuple [beta]) (def_loc "Error")
    in
    let kind = Ptype_variant [ok; error] in
    ptype ~manifest:(Typ.constr_s "result" [alpha; beta]) "result" vars kind
  in
  {vars; body}

let list_ =
  let vars = ["a"] in
  let alpha = Typ.var "a" in
  let alpha_list = Typ.constr_s "list" [alpha] in
  let body =
    let cons =
      Type.constructor ~args:(Pcstr_tuple [alpha; alpha_list]) (def_loc "::")
    in
    let empty = Type.constructor (def_loc "[]") in
    let kind = Ptype_variant [empty; cons] in
    ptype ~manifest:(Typ.constr_s "list" [alpha]) "list" vars kind
  in
  {vars; body}

(** {1 Type combinators} *)

(** {2 Recursive types} *)

module Rec = struct
  let make typ_name =
    { id= typ_name
    ; print= exp_id ("print_" ^ typ_name)
    ; gen= Some (exp_id ("gen_" ^ typ_name))
    ; spec= Some (exp_id ("spec_" ^ typ_name))
    ; card= Infinite
    ; boltz= Ok (Boltz.ref typ_name)
    ; of_arbogen= Ok (exp_id ("of_arbogen_" ^ typ_name))
    ; collector= Some (exp_id ("collect_" ^ typ_name))
    ; tag= None }

  (* XXX. Get rid of this *)
  let lift_opt opt =
    Option.fold ~some:Result.ok ~none:(Result.error "Option is none") opt

  let make_generator (global : GlobalConstraint.t list) typs =
    let+ grammar =
      let+ grammars =
        List.map_result
          (fun (name, typ) -> Boltz.as_grammar name <$> typ.boltz)
          typs
      in
      List.flatten grammars
    in
    let wg = Boltz.compile grammar in
    fun name of_arbogen ->
      let loc = !current_loc in
      let value_provider =
        match global with
        | [] -> [%expr fun _ -> []]
        | [e] -> [%expr fun n -> [|[%e e.value_provider loc] n|]]
        | h :: _tl -> [%expr fun n -> [|[%e h.value_provider loc] n|]]
      in
      [%expr
        fun rs ->
          let wg = [%e wg] in
          let tree = Testify_runtime.Arbg.generate wg [%e string_ name] rs in
          let nb_collect = Testify_runtime.Arbg.count_collect tree in
          let queue = [%e value_provider] nb_collect in
          [%e of_arbogen] tree queue rs]

  let make_glob_spec (global : GlobalConstraint.t list) collect =
    let loc = !current_loc in
    let check e = e.GlobalConstraint.checker loc in
    let collect g =
      let i = g.GlobalConstraint.group |> int_ in
      apply_nolbl collect [i]
    in
    match global with
    | h :: tl ->
        List.fold_left
          (fun expr g -> [%expr [%e expr] && [%e check g |><| collect g] x])
          [%expr [%e check h |><| collect h] x]
          tl
        |> lambda_s "x"
    | _ -> failwith "Found no global contraints but i was expecting one"

  let rec_def header get_field typs =
    let+ bodies =
      List.map_result
        (fun (id, typ) ->
          let+ field = get_field typ in
          (header ^ "_" ^ id, field) )
        typs
    in
    let_rec_and bodies

  let make_mutually_rec header typs get_field =
    List.map_result
      (fun (name, _) ->
        let+ f = rec_def header get_field typs in
        f (exp_id (header ^ "_" ^ name)) )
      typs

  let finish (global : GlobalConstraint.t list) typs =
    let printers =
      make_mutually_rec "print" typs (fun typ -> Ok typ.print)
      |> Result.get_ok
    in
    let specs =
      make_mutually_rec "spec" typs (fun typ -> lift_opt typ.spec)
    in
    let of_arbogen =
      make_mutually_rec "of_arbogen" typs (fun typ -> typ.of_arbogen)
      |> Result.fold ~ok:(List.map Result.ok) ~error:(fun msg ->
             List.map (fun _ -> Result.error msg) typs )
    in
    let collector =
      make_mutually_rec "collect" typs (fun typ -> lift_opt typ.collector)
    in
    let specs : (expression option list, string) result =
      Result.map
        (fun _specs ->
          List.map
            (fun (name, _) ->
              let pre expr =
                match
                  rec_def "collect" (fun t -> lift_opt t.collector) typs
                with
                | Ok f -> Some (f expr)
                | Error msg ->
                    Log.warn "Conversion from (Error _) to None: %s" msg ;
                    None
              in
              match global with
              | [] -> None
              | _ -> pre (make_glob_spec global (exp_id ("collect_" ^ name)))
              )
            typs )
        specs
    in
    let generators =
      let* make_gen = make_generator global typs in
      List.map_result
        (fun (name, t) ->
          Result.map
            (fun _arbg ->
              let pre expr =
                match
                  rec_def "of_arbogen" (fun typ -> typ.of_arbogen) typs
                with
                | Ok f -> Some (f expr)
                | Error msg ->
                    Log.warn "Conversion from (Error _) to None: %s" msg ;
                    None
              in
              pre (make_gen name (exp_id ("of_arbogen_" ^ name))) )
            t.of_arbogen )
        typs
    in
    let generators =
      Result.fold ~ok:Fun.id
        ~error:(fun msg ->
          Log.warn "Unable to derive Boltzmann sampler: %s" msg ;
          List.map (fun _ -> None) typs )
        generators
    in
    let specs =
      Result.fold ~ok:Fun.id
        ~error:(fun msg ->
          Log.warn "Unable to derive specification: %s" msg ;
          List.map (fun _ -> None) typs )
        specs
    in
    (* XXX. Get rid of this *)
    let convert res =
      Result.fold ~ok:(List.map Option.some)
        ~error:(fun msg ->
          Log.warn "Conversion from (Error _) to list of None: %s" msg ;
          List.map (fun _ -> None) typs )
        res
    in
    List.map6
      (fun print gen spec (name, typ) of_arbogen collector ->
        (name, {typ with print; gen; spec; of_arbogen; collector}) )
      printers generators specs typs of_arbogen (convert collector)
end

(** {2 Infinite types} *)

(** Functions specific to infinite types, regardless of their shape. *)
module Infinite = struct
  let generator name boltz =
    let wg = Boltz.compile (Boltz.as_grammar name boltz) in
    let loc = !current_loc in
    [%expr
      fun rs ->
        let sicstus_something _ = assert false in
        let of_arbogen _ _ = assert false in
        let wg = [%e wg] in
        let tree = Testify_runtime.Arbg.generate wg [%e string_ name] rs in
        let nb_collect = Testify_runtime.Arbg.count_collect tree in
        let vals = sicstus_something nb_collect in
        of_arbogen vals tree]
end

(** {2 Type composition} *)

(** tuples *)
module Product = struct
  let gen_body typs =
    List.map
      (function
        | {gen= Some g; _} -> apply_nolbl g [exp_id "rs"] | _ -> raise Exit
        )
      typs
    |> tuple

  let generator typs =
    try gen_body typs |> lambda_s "rs" |> Option.some with Exit -> None

  let specification typs =
    match typs with
    | [] -> assert false
    | _ when List.for_all (fun t -> t.spec = None) typs -> None
    | _ ->
        let get_name = id_gen_gen () in
        let compose (pats, body) p =
          match (body, p.spec) with
          | x, None -> (Pat.of_string "_" :: pats, x)
          | None, Some p ->
              let name, id = get_name () in
              let app = apply_nolbl p [id] in
              (Pat.of_string name :: pats, Some app)
          | Some p', Some p ->
              let name, id = get_name () in
              let app = apply_nolbl p [id] in
              (Pat.of_string name :: pats, Some (p' &&@ app))
        in
        let pats, body = List.fold_left compose ([], None) typs in
        Option.map (lambda (Pat.tuple (List.rev pats))) body

  let cardinality typs = List.map (fun t -> t.card) typs |> Card.product

  let printer typs =
    let get_name = id_gen_gen () in
    let np p =
      let n, id = get_name () in
      (apply_nolbl p.print [id], Pat.of_string n)
    in
    let names, pats = List.split (List.map np typs) in
    let b = string_concat ~sep:", " names in
    let b' = string_concat [string_ "("; b; string_ ")"] in
    lambda (Pat.tuple pats) b'

  let arbogen_body args_arbg =
    let get_name = id_gen_gen () in
    let np of_arbogen =
      let n, id = get_name () in
      let loc = !Helper.current_loc in
      ([%expr [%e of_arbogen] [%e id] queue rs], n)
    in
    let bodies, pats = List.map np args_arbg |> List.split in
    List.fold_left2
      (fun acc p body ->
        let pat = Pat.of_string p in
        let_pat pat body acc )
      (tuple (List.map exp_id pats))
      (List.rev pats) (List.rev bodies)

  let arbogen args_arbg =
    let loc = !Helper.current_loc in
    [%expr fun queue rs -> [%e arbogen_body args_arbg]]

  let boltzmann_specification typs =
    let+ args = List.map_result (fun typ -> typ.boltz) typs in
    Boltz.product args

  let collector typs =
    let get_name = id_gen_gen () in
    let np = function
      | {collector= Some c; _} ->
          let n, id = get_name () in
          (apply_nolbl c [exp_id "n"; id], Pat.of_string n)
      | {collector= None; _} -> raise Exit
    in
    try
      let names, pats = List.split (List.map np typs) in
      let b = list_of_list names in
      lambda_s "n"
        (lambda (Pat.tuple pats) (apply_nolbl_s "List.flatten" [b]))
      |> Option.some
    with Exit -> None

  let make id typs : t =
    let of_arbogen =
      let+ args_arbg = List.map_result (fun typ -> typ.of_arbogen) typs in
      arbogen args_arbg
    in
    make id
      (boltzmann_specification typs)
      (printer typs) (generator typs) (specification typs) (cardinality typs)
      of_arbogen (collector typs)
end

(** ADTs *)
module Sum = struct
  type variants =
    (string * (t * int option) (* id of collect if present *) list) list

  let cardinality : variants -> Card.t =
    let rec sum acc = function
      | [] -> Card.finite acc
      | (_, args) :: variants -> (
        match args |> List.map fst |> Product.cardinality with
        | Finite n -> sum (Z.add acc n) variants
        | (Infinite | Unknown) as c -> c )
    in
    sum Z.zero

  let constr_generator constr args =
    let constr = construct constr in
    match args with
    | [] -> lambda_s "_" (constr None) |> Option.some
    | [({gen= Some g; _}, _)] ->
        lambda_s "rs" (constr (Some (apply_nolbl g [exp_id "rs"])))
        |> Option.some
    | [({gen= None; _}, _)] -> raise Exit
    | l -> (
      try
        lambda_s "rs" (constr (Some (l |> List.map fst |> Product.gen_body)))
        |> Option.some
      with Exit -> None )

  let generator (variants : variants) totalcard =
    try
      let weight c =
        Q.div (Q.of_bigint c) (Q.of_bigint totalcard)
        |> Q.to_float |> Helper.float_
      in
      apply_runtime "weighted"
        [ list_of_list
            (List.map
               (fun (constr, typs) ->
                 let card =
                   typs |> List.map fst |> Product.cardinality |> Card.as_z
                 in
                 Helper.pair (weight card)
                   (constr_generator constr typs |> Option.get) )
               variants )
        ; exp_id "rs" ]
      |> lambda_s "rs" |> Option.some
    with Exit | Invalid_argument _ -> None

  let pat_exp p id =
    List.map
      (fun _ ->
        let p, e = id () in
        (Pat.of_string p, e) )
      p
    |> List.split

  let constr_printer txt typs =
    let id = id_gen_gen () in
    let constr pat = Pat.construct_s txt pat in
    match typs with
    | [] -> case (constr None) (string_ txt)
    | [{print; _}] ->
        let pat, expr = id () in
        case
          (constr (Some (Pat.of_string pat)))
          (string_concat
             [string_ (txt ^ "("); apply_nolbl print [expr]; string_ ")"] )
    | p ->
        let pat, exp = pat_exp p id in
        case
          (constr (Some (Pat.tuple pat)))
          (string_concat
             [string_ txt; apply_nolbl (Product.printer p) [tuple exp]] )

  let printer (variants : variants) =
    let cases =
      List.map
        (fun (constr, args) -> constr_printer constr (List.map fst args))
        variants
    in
    function_ cases

  let constr_spec txt args =
    let id = id_gen_gen () in
    let constr pat = Pat.construct_s txt pat in
    match args with
    | [] -> (constr None, None)
    | [last] ->
        let prop = Option.get last.spec in
        let p, e = id () in
        let pat = constr (Some (Pat.of_string p)) in
        (pat, case pat (apply_nolbl prop [e]) |> Option.some)
    | p ->
        let pat, exp = pat_exp p id in
        let pat = Pat.tuple pat in
        ( pat
        , Option.map
            (fun spec ->
              case (constr (Some pat)) (apply_nolbl spec [tuple exp]) )
            (args |> Product.specification) )

  let specification (variants : variants) =
    try
      let cases =
        List.map (fun (c, a) -> constr_spec c (List.map fst a)) variants
      in
      if List.for_all (fun (_, c) -> c = None) cases then None
      else
        Some
          (function_
             (List.map
                (function p, None -> case p true_ | _, Some c -> c)
                cases ) )
    with Exit | Invalid_argument _ -> None

  let boltzmann_specification : variants -> (Boltz.t, string) result =
    let variant_spec (name, args) =
      let+ args_spec =
        match args with
        | [] -> Ok Boltz.epsilon
        | _ ->
            let+ args =
              List.map_result
                (fun (t, collect) ->
                  (* XXX. This assumes that [@collect] occurs only on atomic types *)
                  if Option.is_some collect then Ok (Boltz.ref "@collect")
                  else t.boltz )
                args
            in
            Boltz.product args
      in
      Boltz.(product [z; indirection name args_spec])
    in
    function
    | [] -> Result.error "Empty sum type"
    | variants ->
        let+ args = List.map_result variant_spec variants in
        Boltz.union args

  let constr_arbg name args =
    let id = id_gen_gen () in
    let loc = !Helper.current_loc in
    let constr pats =
      [%pat? Arbogen.Tree.Label ([%p Pat.string name], [%p Pat.list pats])]
    in
    match args with
    | [] -> case (constr []) [%expr [%e construct name None]]
    | [of_arbogen] ->
        case
          (constr [[%pat? x1]])
          [%expr
            let x1' = [%e of_arbogen] x1 queue rs in
            [%e construct name (Some [%expr x1'])]]
    | _ :: _ :: _ ->
        let pat, exp = pat_exp args id in
        let pat_c = constr pat in
        let of_arbogen = Product.arbogen args in
        let body =
          [%expr
            let [%p Pat.tuple pat] = [%e of_arbogen] queue rs in
            [%e construct name (Some (tuple exp))]]
        in
        case pat_c body

  let arbogen name variants =
    let loc = !Helper.current_loc in
    let cases = List.map (fun (c, a) -> constr_arbg c a) variants in
    let default =
      case [%pat? _] [%expr failwith "Ill-formed arbogen tree"]
    in
    [%expr
      fun arbg queue rs ->
        match arbg with
        | Arbogen.Tree.Label ([%p Pat.string name], [Tuple []; child]) ->
            [%e match_ [%expr child] (cases @ [default])]
        | _ -> failwith "Ill-formed arbogen tree"]

  let constr_collect name args =
    let id = id_gen_gen () in
    match args with
    | [] -> case (Pat.construct_s name None) empty_list_exp
    | [x] ->
        let col = Option.get x.collector in
        let p, e = id () in
        let pat = Pat.construct_s name (Some (Pat.of_string p)) in
        case pat (apply_nolbl col [exp_id "n"; e])
    | p ->
        let pat, exp = pat_exp p id in
        let tup =
          apply_nolbl
            (Product.collector args |> Option.get)
            [exp_id "n"; tuple exp]
        in
        case (Pat.construct_s name (Some (Pat.tuple pat))) tup

  let collector variants =
    try
      let cases =
        List.map (fun (c, a) -> constr_collect c (List.map fst a)) variants
      in
      Some (lambda_s "n" (function_ cases))
    with Exit | Invalid_argument _ -> None

  let make name (variants : variants) : t =
    let print = printer variants in
    let card = cardinality variants in
    let boltz = boltzmann_specification variants in
    let gen =
      match card with
      | Infinite ->
          Result.fold
            ~ok:(Infinite.generator name >>> Option.some)
            ~error:(fun _ -> None)
            boltz
      | Finite n -> generator variants n
      | Unknown -> None
    in
    let spec = specification variants in
    let of_arbogen =
      (* Only retain useful information *)
      let+ variants =
        List.map_result
          (fun (cname, cargs) ->
            let+ cargs =
              List.map_result (fun (typ, _) -> typ.of_arbogen) cargs
            in
            (cname, cargs) )
          variants
      in
      (* Actual code generation *)
      arbogen name variants
    in
    make name boltz print gen spec card of_arbogen (collector variants)
end

module Record = struct
  let cardinality fields = fields |> List.map snd |> Product.cardinality

  let generator fields =
    let field (n, t) =
      (lid_loc n, apply_nolbl (t.gen |> Option.get) [exp_id "rs"])
    in
    try record (List.map field fields) None |> lambda_s "rs" |> Option.some
    with _ -> None

  let printer fields =
    let field (n, t) =
      let field = apply_nolbl t.print [exp_id n] in
      let field_name = n ^ " = " in
      (field_name, field, (lid_loc n, Pat.of_string n))
    in
    match fields with
    | [] -> assert false
    | h :: tl ->
        let n, rhd, pat = field h in
        let fields, pat =
          List.fold_left
            (fun (rhd, pat) f ->
              let n', rhd', pat' = field f in
              (rhd' :: string_ ("; " ^ n') :: rhd, pat' :: pat) )
            ([rhd; string_ ("{" ^ n)], [pat])
            tl
        in
        let app = string_concat (List.rev fields) in
        let app = string_concat [app; string_ "}"] in
        lambda (Pat.record_closed (List.rev pat)) app

  let specification fields =
    let field (n, t) =
      ( apply_nolbl (t.spec |> Option.get) [exp_id n]
      , (lid_loc n, Pat.of_string n) )
    in
    try
      let fields = List.map field fields in
      let fields, pat = List.split fields in
      match fields with
      | h :: tl ->
          List.fold_left ( &&@ ) h tl
          |> lambda (Pat.record_closed pat)
          |> Option.some
      | _ -> (*record with 0 field*) assert false
    with _ -> None

  let boltzmann_specification fields =
    fields |> List.map snd |> Product.boltzmann_specification

  let arbogen fields =
    let get_name = id_gen_gen () in
    let loc = !Helper.current_loc in
    let np (field, p) =
      let _, id = get_name () in
      let+ of_arbogen = p.of_arbogen in
      (lid_loc field, [%expr [%e of_arbogen] [%e id] queue rs])
    in
    let+ fields = List.map_result np fields in
    [%expr fun queue rs -> [%e record fields None]]

  let make id fields =
    let c = cardinality fields in
    let g = generator fields in
    let p = printer fields in
    let s = specification fields in
    let arbg = arbogen fields in
    make id (boltzmann_specification fields) p g s c arbg None
end

module Constrained = struct
  (*TODO: complete *)
  let rec unify_patterns p p' =
    match (p.ppat_desc, p'.ppat_desc) with
    | Ppat_any, _ -> Some p'
    | _, Ppat_any -> Some p
    | Ppat_var s, Ppat_var s' -> if s.txt = s'.txt then Some p else None
    | Ppat_tuple t, Ppat_tuple t' -> (
      try
        Some
          ( List.map2 (fun e1 e2 -> Option.get (unify_patterns e1 e2)) t t'
          |> Pat.tuple )
      with Invalid_argument _ -> None )
    | Ppat_record (r1, c), Ppat_record (r2, _) -> (
      try
        Some
          (Pat.record
             (List.map2
                (fun (l1, p1) (l2, p2) ->
                  if l1.txt = l2.txt then
                    (l1, Option.get (unify_patterns p1 p2))
                  else
                    Format.asprintf "label %a and %a not in same order"
                      print_longident l1.txt print_longident l2.txt
                    |> invalid_arg )
                r1 r2 )
             c )
      with Invalid_argument msg ->
        Format.eprintf "%s\n%!" msg ;
        None )
    | _ -> None

  let compose_properties p p' =
    match (p.pexp_desc, p'.pexp_desc) with
    | Pexp_fun (_, _, pat, expr), Pexp_fun (_, _, pat', expr') -> (
      match unify_patterns pat pat' with
      | None ->
          lambda_s "x"
            (apply_nolbl p [exp_id "x"] &&@ apply_nolbl p' [exp_id "x"])
      | Some pat ->
          let newexpr = expr &&@ expr' in
          let newp = lambda pat newexpr in
          lambda_s "x" (apply_nolbl newp [exp_id "x"]) )
    | _ ->
        lambda_s "x"
          (apply_nolbl p [exp_id "x"] &&@ apply_nolbl p' [exp_id "x"])

  let rejection pred gen = apply_runtime "reject" [pred; gen]

  let make ct typ e =
    let spec =
      match typ.spec with Some p -> compose_properties p e | None -> e
    in
    let default =
      { typ with
        gen= Option.map (rejection spec) typ.gen
      ; spec= Some spec
      ; card= Unknown }
    in
    match Gegen.solve_ct ct spec with
    | Some (gen, card) -> {default with gen= Some gen; card= Finite card}
    | _ -> default

  let make_td td typ e =
    let spec =
      match typ.spec with Some p -> compose_properties p e | None -> e
    in
    let default =
      { typ with
        gen= Option.map (rejection e) typ.gen
      ; spec= Some spec
      ; card= Unknown }
    in
    match Gegen.solve_td td e with
    | Some (gen, card) -> {default with gen= Some gen; card= Finite card}
    | _ -> default

  let make_td td typ e =
    match GlobalConstraint.search e with
    | [] -> make_td td typ e
    | _ ->
        if Card.is_finite typ.card then
          failwith "global constraints only allowed on recursive types"
        else typ
end

(* generators for function 'a -> 'b are synthetized using only the 'b
   generator, i.e : let fun_gen = fun _ -> gen_b (). Generators are memoized
   to behave as mathematical functions *)
module Arrow = struct
  let generator =
    Option.map (fun g ->
        lambda_s "rs"
          (apply_runtime "memo" [lambda_s "_" (apply_nolbl g [exp_id "rs"])]) )

  let printer = lambda_s "_" (string_ "(_ -> _)")

  let make id _input output =
    let bs = Result.error "Arrow types not supported" in
    let c = Card.Unknown in
    let g = generator output.gen in
    make id bs printer g None c
      (Result.error "No of_arbogen function for arrow types")
      None
end

module Collect = struct
  let make t tag =
    let collector =
      Option.map
        (fun c ->
          let loc = !current_loc in
          [%expr
            fun n -> if n = [%e int_ tag] then [%e c] n else fun _ -> []] )
        t.collector
    in
    {t with tag= Some tag; collector}
end
