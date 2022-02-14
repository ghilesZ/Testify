(* This module provides helpers for ast building (and other stuff) *)

(* keep this before open as module Parse is shadowed by open
   Migrate_parsetree *)
let lparse s =
  try Parse.longident (Lexing.from_string s)
  with _ ->
    (* for operators *)
    Parse.longident (Lexing.from_string ("( " ^ s ^ " )"))

open Migrate_parsetree
open Ast_410
open Parsetree
open Asttypes
open Ast_helper

let current_loc = ref Location.none

let update_loc l = current_loc := l

(* same as mkloc but with optional argument; default is Location.none*)
let def_loc ?loc s =
  let loc = match loc with None -> !current_loc | Some loc -> loc in
  Location.mkloc s loc

(* builds a Longident.t Location.t from a string *)
let lid_loc ?loc id = def_loc ?loc (lparse id)

module Pat = struct
  include Pat

  (* pattern of string *)
  let of_string = function
    | "_" -> Pat.any ~loc:!current_loc ()
    | "()" -> Pat.construct (lid_loc "()") None
    | s -> Pat.var (def_loc s)

  let tuple = Pat.tuple ~loc:!current_loc

  let pair a b = tuple [a; b]

  let construct_s str = Pat.construct ~loc:!current_loc (lid_loc str)

  let record list = Pat.record ~loc:!current_loc list

  let record_closed list = Pat.record ~loc:!current_loc list Closed

  let string s = Pat.constant ~loc:!current_loc (Const.string s)

  let rec list = function
    | [] -> construct_s "[]" None
    | a :: t -> construct_s "::" (Some (tuple [a; list t]))
end

(* given a string [name], builds the identifier [name] *)
let exp_id name = lid_loc name |> Exp.ident ~loc:!current_loc

(* same as apply but argument are not labelled *)
let apply_nolbl f args =
  Exp.apply ~loc:!current_loc f (List.map (fun a -> (Nolabel, a)) args)

(* same as apply_nolbl but function name is a string *)
let apply_nolbl_s s = apply_nolbl (exp_id s)

let capitalize_first_char str =
  let b = Bytes.of_string str in
  Bytes.set b 0 (Char.uppercase_ascii str.[0]) ;
  Bytes.to_string b

(* calls a function defined in the runtime *)
let apply_runtime s = apply_nolbl_s ("Testify_runtime." ^ s)

(* Same as Exp.fun_ *)
let lambda = Exp.fun_ ~loc:!current_loc Nolabel None

(* Same as lambda with string instead of pattern *)
let lambda_s s = lambda (Pat.of_string s)

(* function composition at ast level *)
let ( |><| ) f g = lambda_s "x" (apply_nolbl f [apply_nolbl g [exp_id "x"]])

(* double application *)
let ( @@@ ) f g e = apply_nolbl f [apply_nolbl g e]

let constant = Exp.constant ~loc:!current_loc

let record = Exp.record ~loc:!current_loc

let construct name = Exp.construct ~loc:!current_loc (lid_loc name)

(* boolean expressions *)
let true_ = construct "true" None

let false_ = construct "false" None

(* && over ast *)
let ( &&@ ) a b = apply_nolbl_s " (&&) " [a; b]

(* ^ over ast *)
let ( ^@ ) a b = apply_nolbl_s " (^) " [a; b]

(* useful constructors *)
let int_ x =
  if x = min_int then exp_id "min_int"
  else if x = max_int then exp_id "max_int"
  else if x < -4096 || x > 4096 then
    let x = Format.asprintf "0x%x" x in
    constant (Pconst_integer (x, None))
  else constant (Const.int x)

let one = int_ 1

let float_ x =
  Format.(
    if x < -4096. || x > 4096. then asprintf "%h" x
    else asprintf "%a" pp_print_float x)
  |> Const.float |> constant

let string_ x = constant (Const.string x)

let unit = construct "()" None

let tuple = Exp.tuple ~loc:!current_loc

let pair a b = tuple [a; b]

(* value binding with string *)
let vb_s id exp = Vb.mk ~loc:!current_loc (Pat.of_string id) exp

let letunit exp = Str.value ~loc:!current_loc Nonrecursive [vb_s "()" exp]

let let_pat pats exp in_ =
  Exp.let_ ~loc:!current_loc Nonrecursive
    [Vb.mk ~loc:!current_loc pats exp]
    in_

let let_ id exp in_ =
  Exp.let_ ~loc:!current_loc Nonrecursive [vb_s id exp] in_

let let_rec id exp in_ =
  Exp.let_ ~loc:!current_loc Recursive [vb_s id exp] in_

let let_rec_and vb in_ =
  Exp.let_ ~loc:!current_loc Recursive
    (List.map (fun (s, e) -> vb_s s e) vb)
    in_

let case = Exp.case

let function_ = Exp.function_ ~loc:!current_loc

let match_ = Exp.match_ ~loc:!current_loc

(* ast for lists *)
let empty_list_exp = construct "[]" None

let cons_exp h t = construct "( :: )" (Some (tuple [h; t]))

let list_of_list l = List.fold_right cons_exp l empty_list_exp

(* opens locally the module "Name" and builds the expression *)
let let_open mod_ =
  let w = PStr [Str.eval (string_ "-33")] in
  let mod_ = capitalize_first_char mod_ in
  Exp.open_
    ~attrs:[Attr.mk (def_loc "warning") w]
    ~loc:!current_loc
    (Opn.mk ~loc:!current_loc (Mod.ident ~loc:!current_loc (lid_loc mod_)))

(* fresh identifier generator generator *)
let id_gen_gen () =
  let cpt = ref 0 in
  fun () ->
    incr cpt ;
    let s = "x" ^ string_of_int !cpt in
    (s, exp_id s)

(* string concat with separator over ast expressions *)
let string_concat ?(sep = "") = function
  | [] -> string_ ""
  | [s] -> s
  | h :: tl ->
      List.fold_left
        (if sep = "" then ( ^@ ) else fun acc e -> acc ^@ string_ sep ^@ e)
        h tl

(* printing *)

module Conv = Convert (OCaml_410) (OCaml_current)

let file_to_string filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch ; s

let print_expression fmt e =
  let oc = open_out "raw.ml" in
  let fmt_oc = Format.formatter_of_out_channel oc in
  Format.fprintf fmt_oc "%a%!" Pprintast.expression (Conv.copy_expression e) ;
  if Sys.command "ocamlformat raw.ml > formatted.ml" = 0 then
    Format.fprintf fmt "%s" (file_to_string "formatted.ml")
  else
    Format.fprintf fmt "%a%!" Pprintast.expression (Conv.copy_expression e) ;
  close_out oc ;
  Sys.command "rm -f formatted.ml raw.ml" |> ignore

let print_longident fmt l =
  l |> Longident.flatten |> String.concat "." |> Format.pp_print_string fmt

let lid_to_string l = Format.asprintf "%a" print_longident l

let print_pat fmt p = Pprintast.pattern fmt (Conv.copy_pattern p)

let print_coretype fmt t = Pprintast.core_type fmt (Conv.copy_core_type t)

let print_td fmt (recflag, types) =
  let sig_ =
    {psig_desc= Psig_type (recflag, types); psig_loc= Location.none}
  in
  let oc = open_out "raw.ml" in
  let fmt_oc = Format.formatter_of_out_channel oc in
  Format.fprintf fmt_oc "%a%!" Pprintast.signature
    (Conv.copy_signature [sig_]) ;
  if Sys.command "ocamlformat raw.ml > formatted.ml" = 0 then
    Format.fprintf fmt "%s" (file_to_string "formatted.ml")
  else
    Format.fprintf fmt "%a%!" Pprintast.signature
      (Conv.copy_signature [sig_]) ;
  close_out oc ;
  Sys.command "rm -f formatted.ml raw.ml" |> ignore

let print_type_decl fmt t =
  let sig_ =
    {psig_desc= Psig_type (Recursive, [t]); psig_loc= Location.none}
  in
  Pprintast.signature fmt (Conv.copy_signature [sig_])

let print_payload fmt = function
  | PStr str -> Pprintast.structure fmt (Conv.copy_structure str)
  | PSig sig_ -> Pprintast.signature fmt (Conv.copy_signature sig_)
  | PTyp ct -> print_coretype fmt ct
  | PPat (pattern, Some expr) ->
      Format.fprintf fmt "%a %a" print_pat pattern print_expression expr
  | PPat (pattern, None) -> Format.fprintf fmt "%a" print_pat pattern

(* keeps the attributes with name 'n'*)
let check_attributes n attrs =
  List.filter (fun a -> a.attr_name.txt = n) attrs

(* gets the only attribute with name 'n', raises an error if more than one,
   None if 0 *)
let get_attribute_payload n attrs =
  match check_attributes n attrs with
  | [] -> None
  | [{attr_payload; _}] -> Some attr_payload
  | _ -> Format.asprintf "only one %s attribute accepted" n |> failwith

(* gets the single pstr payload attached to an attribute *)
let get_attribute_pstr n attrs =
  match get_attribute_payload n attrs with
  | Some (PStr [{pstr_desc= Pstr_eval (e, _); _}]) -> Some e
  | _ -> None

let has_attribute n attrs = get_attribute_payload n attrs |> Option.is_some

(* markdown escaping *)
let md str = String.split_on_char '*' str |> String.concat "\\*"

(* pretty printing of large numbers: if cardinality is big, we print it as a
   power of 2 for readability *)
let print_bigint =
  let z15 = Z.of_int 32768 in
  let close_log z =
    let down = Z.log2 z in
    let up = succ down in
    let z2 = Z.of_int 2 in
    if Z.sub z (Z.shift_left z2 down) < Z.sub (Z.shift_left z2 up) z then
      down
    else up
  in
  fun fmt z ->
    if Z.gt z z15 then Format.fprintf fmt "~2<sup>%i</sup>" (close_log z)
    else Z.pp_print fmt z

(* ast simplification *)
(**********************)

(* compatible if :
   - fun x -> body x <=> body
   - fun (x1,x2) -> body (x1,x2) <=> body *)
let rec compatible pat exp =
  match (pat.ppat_desc, exp.pexp_desc) with
  | Ppat_var s, Pexp_ident l ->
      Format.asprintf "%a" print_longident l.txt = s.txt
  | Ppat_tuple s, Pexp_tuple l -> List.for_all2 compatible s l
  | _ -> false

(* elementary simplification of some ast patterns *)
let rec trim exp =
  match exp.pexp_desc with
  | Pexp_apply
      ( {pexp_desc= Pexp_fun (Nolabel, None, pat, body); pexp_loc; _}
      , [(Nolabel, arg)] ) ->
      if compatible pat arg then {body with pexp_loc} else exp
  | Pexp_apply ({pexp_desc= Pexp_fun (Nolabel, None, pat, body); _}, args)
    -> (
    match List.rev args with
    | (Nolabel, h) :: tl ->
        if compatible pat h then
          trim {exp with pexp_desc= Pexp_apply (body, List.rev tl)}
        else exp
    | _ -> exp )
  | _ -> exp

(* we overload applies function to simplify them by default *)
let apply_nolbl_s name args = apply_nolbl_s name args |> trim

let apply_nolbl func args = apply_nolbl func args |> trim

(* recursive type detection *)
(****************************)

module SSet = Set.Make (String)
module SMap = Map.Make (String)

(* list of type decl in l that are recursive *)
let has_cycle (l : (string * SSet.t) list) =
  let recursive = Hashtbl.create 1 in
  List.iter
    (fun (t, _) ->
      let reachable = Hashtbl.create 1 in
      let todo = Stack.create () in
      Stack.push t todo ;
      let rec loop () =
        if not (Stack.is_empty todo) then (
          let cur = Stack.pop todo in
          if not (Hashtbl.mem reachable cur) then (
            Hashtbl.add reachable cur () ;
            let nexts =
              List.assoc_opt cur l
              |> Option.fold ~some:Fun.id ~none:SSet.empty
            in
            try
              SSet.iter
                (fun next ->
                  if t = next then (
                    Hashtbl.add recursive t () ;
                    raise Exit ) ;
                  Stack.push next todo )
                nexts
            with Exit -> () ) ;
          loop () )
      in
      loop () )
    l ;
  Hashtbl.to_seq_keys recursive |> List.of_seq

(* collect all the type identifiers that appear in a given type
   declaration *)
let collect t td =
  let rec aux_ct acc ct =
    match ct.ptyp_desc with
    | Ptyp_var _var -> acc
    | Ptyp_constr ({txt; _}, _) ->
        SSet.add (Format.asprintf "%a" print_longident txt) acc
    | Ptyp_tuple tup -> List.fold_left aux_ct acc tup
    | Ptyp_arrow (Nolabel, input, output) -> aux_ct (aux_ct acc input) output
    | _ -> acc
  in
  let aux_record = List.fold_left (fun acc l -> aux_ct acc l.pld_type) in
  let aux acc {ptype_kind; ptype_manifest; _} =
    match ptype_kind with
    | Ptype_abstract ->
        Option.fold ~none:acc ~some:(aux_ct acc) ptype_manifest
    | Ptype_variant constructors ->
        let constr_f acc c =
          match c.pcd_args with
          | Pcstr_tuple tup -> List.fold_left aux_ct acc tup
          | Pcstr_record labs -> aux_record acc labs
        in
        List.fold_left constr_f acc constructors
    | Ptype_record labs -> aux_record acc labs
    | Ptype_open -> acc
  in
  aux t td

(* given a list of type declaratation, returns the sublist of recursive
   types *)
let recursive recflag (typs : type_declaration list) =
  let typ_neighbours =
    List.map (fun t -> (t.ptype_name.txt, collect SSet.empty t)) typs
  in
  match recflag with
  | Nonrecursive -> []
  | Recursive ->
      let names = has_cycle typ_neighbours in
      List.filter (fun td -> List.mem td.ptype_name.txt names) typs

let rec_nonrec recflag typs =
  let rec_ = recursive recflag typs in
  let nonrec_ = List.filter (fun t -> not (List.mem t rec_)) typs in
  (rec_, nonrec_)

(** {2 Monadic operators for the Result type} *)

let ( <$> ) = Result.map

let ( let* ) = Result.bind

let ( let+ ) r f = f <$> r

(** {2 Add some functions to the stdlib} *)

module List = struct
  include List

  (** Yeah I know... *)
  let rec map6 f l1 l2 l3 l4 l5 l6 =
    match (l1, l2, l3, l4, l5, l6) with
    | [], [], [], [], [], [] -> []
    | x1 :: l1, x2 :: l2, x3 :: l3, x4 :: l4, x5 :: l5, x6 :: l6 ->
        let y = f x1 x2 x3 x4 x5 x6 in
        y :: map6 f l1 l2 l3 l4 l5 l6
    | _ -> invalid_arg "List.map6"

  let rec map_result f = function
    | [] -> Ok []
    | x :: xs ->
        let* y = f x in
        let* ys = map_result f xs in
        Ok (y :: ys)
end

module Typ = struct
  let var = Typ.var ~loc:!current_loc

  let poly args = Typ.poly ~loc:!current_loc (List.map def_loc args)

  let constr = Typ.constr ~loc:!current_loc

  let constr_s id = Typ.constr ~loc:!current_loc (lid_loc id)
end

module Type = struct
  let constructor = Type.constructor

  let constructor_s ?attrs ?info ?res ?args str =
    Type.constructor ~loc:!current_loc ?attrs ?info ?res ?args (def_loc str)

  let field ?attrs ?info ?mut =
    Type.field ?attrs ?info ?mut ~loc:!current_loc

  let field_s ?attrs ?info ?mut str = field ?attrs ?info ?mut (def_loc str)
end

(** Left-to-right function composition *)
let ( >>> ) f g x = x |> f |> g
