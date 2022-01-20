(* This module provides helpers for ast building *)

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

(* same as mkloc but with optional argument; default is Location.none*)
let none_loc ?(loc = Location.none) s = Location.mkloc s loc

(* builds a Longident.t Location.t from a string *)
let lid_loc ?(loc = Location.none) id = none_loc ~loc (lparse id)

(* pattern of string *)
let pat_s = function
  | "_" -> Pat.any ()
  | "()" -> Pat.construct (lid_loc "()") None
  | s -> Pat.var (none_loc s)

(* given a string [name], builds the identifier [name] *)
let exp_id ?loc name = lid_loc ?loc name |> Exp.ident

(* same as apply but argument are not labelled *)
let apply_nolbl f args = Exp.apply f (List.map (fun a -> (Nolabel, a)) args)

(* same as apply_nolbl but function name is a string *)
let apply_nolbl_s s = apply_nolbl (exp_id s)

let capitalize_first_char str =
  let b = Bytes.of_string str in
  Bytes.set b 0 (Char.uppercase_ascii str.[0]) ;
  Bytes.to_string b

(* opens locally the module "Name" and builds the expression *)
let let_open mod_ exp =
  let mod_ = capitalize_first_char mod_ in
  Exp.open_ (Opn.mk (Mod.ident (lid_loc mod_))) exp

(* opens the runtime and then build exp *)
let open_runtime = let_open "Testify_runtime"

(* calls a function defined in the runtime *)
let apply_runtime s = apply_nolbl_s ("Testify_runtime." ^ s)

(* Same as Exp.fun_ *)
let lambda = Exp.fun_ Nolabel None

(* Same as lambda with string instead of pattern *)
let lambda_s s = lambda (pat_s s)

(* function composition at ast level *)
let ( |><| ) f g = lambda_s "x" (apply_nolbl f [apply_nolbl g [exp_id "x"]])

(* double application *)
let ( @@@ ) f g e = apply_nolbl f [apply_nolbl g e]

(* boolean expressions *)
let true_ = Exp.construct (lid_loc "true") None

let false_ = Exp.construct (lid_loc "false") None

(* && over ast *)
let ( &&@ ) a b = apply_nolbl_s " (&&) " [a; b]

(* useful constructors *)
let int_ x =
  if x = min_int then exp_id "min_int"
  else if x = max_int then exp_id "max_int"
  else if x < -4096 || x > 4096 then
    let x = Format.asprintf "0x%x" x in
    Exp.constant (Pconst_integer (x, None))
  else Exp.constant (Const.int x)

let one = int_ 1

let float_ x =
  if x < -4096. || x > 4096. then
    Exp.constant (Const.float (Format.asprintf "%h" x))
  else Exp.constant (Const.float (Format.asprintf "%f" x))

let string_ x = Exp.constant (Const.string x)

let unit = Exp.construct (lid_loc "()") None

let pair a b = Exp.tuple [a; b]

(* value binding with string *)
let vb_s id exp = Vb.mk (pat_s id) exp

let letunit exp = Str.value Nonrecursive [vb_s "()" exp]

let let_ id exp in_ = Exp.let_ Nonrecursive [vb_s id exp] in_

let letrec id exp in_ = Exp.let_ Recursive [vb_s id exp] in_

(* ast for lists *)
let empty_list_exp = Exp.construct (lid_loc "[]") None

let cons_exp h t = Exp.construct (lid_loc "( :: )") (Some (Exp.tuple [h; t]))

let list_of_list l = List.fold_right cons_exp l empty_list_exp

(* fresh identifier generator generator *)
let id_gen_gen () =
  let cpt = ref 0 in
  fun () ->
    incr cpt ;
    let s = "x" ^ string_of_int !cpt in
    (s, exp_id s)

(* string concat with separator over ast expressions *)
let string_concat ?(sep = "") l =
  apply_nolbl_s "String.concat" [string_ sep; list_of_list l]

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

(* gets the pstr payload attached to an attribute *)
let get_attribute_pstr n attrs =
  match get_attribute_payload n attrs with
  | Some (PStr [{pstr_desc= Pstr_eval (e, _); _}]) -> Some e
  | Some _ -> Format.kasprintf failwith "bad %s attribute" n
  | None -> None

(* printing *)

(* same as [pp], but in bold blue] *)
let bold_blue x = Format.asprintf "\x1b[34;1m%s\x1b[0m" x

(* same as [pp], but in blue *)
let blue x = Format.asprintf "\x1b[36m%s\x1b[0m" x

(* same as [pp], but in gray *)
let gray x = Format.asprintf "\x1b[37m%s\x1b[0m" x

module Conv = Convert (OCaml_410) (OCaml_current)

let print_expression fmt e =
  Pprintast.expression fmt (Conv.copy_expression e)

let print_longident fmt l =
  l |> Longident.flatten |> String.concat "." |> Format.pp_print_string fmt

let print_pat fmt p = Pprintast.pattern fmt (Conv.copy_pattern p)

let print_coretype fmt t = Pprintast.core_type fmt (Conv.copy_core_type t)

let print_td fmt (recflag, types) =
  let sig_ =
    {psig_desc= Psig_type (recflag, types); psig_loc= Location.none}
  in
  Pprintast.signature fmt (Conv.copy_signature [sig_])

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

(* recursive type detection *)
(****************************)

module SSet = Set.Make (String)
module SMap = Map.Make (String)

(* list of type decl in l that are recursive *)
let has_cycle (l : (type_declaration * SSet.t) list) =
  let recursive = Hashtbl.create 1 in
  List.iter
    (fun (t, _) ->
      let reachable = Hashtbl.create 1 in
      let todo = Stack.create () in
      Stack.push t todo ;
      let rec loop () =
        if not (Stack.is_empty todo) then (
          let cur = Stack.pop todo in
          ( match Hashtbl.find_opt reachable cur with
          | Some _ -> ()
          | None ->
              Hashtbl.add reachable cur () ;
              let nexts = List.assoc cur l in
              SSet.iter
                (fun next ->
                  if t.ptype_name.txt = next then Hashtbl.add recursive t () ;
                  Stack.push t todo )
                nexts ) ;
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
let recursive (recflag, typs) =
  let typ_neighbours = List.map (fun t -> (t, collect SSet.empty t)) typs in
  match recflag with
  | Nonrecursive -> []
  | Recursive -> has_cycle typ_neighbours

let rec_nonrec ((_, typs) as td) =
  let rec_ = recursive td in
  let nonrec_ = List.filter (fun t -> not (List.mem t rec_)) typs in
  (rec_, nonrec_)

let rec compatible pat exp =
  match (pat.ppat_desc, exp.pexp_desc) with
  | Ppat_var s, Pexp_ident l ->
      Format.asprintf "%a" print_longident l.txt = s.txt
  | Ppat_tuple s, Pexp_tuple l -> List.for_all2 compatible s l
  | _ -> false

(* elementary simplification of some ast patterns *)
let trim exp =
  match exp.pexp_desc with
  | Pexp_apply
      ({pexp_desc= Pexp_fun (Nolabel, None, pat, body); _}, [(Nolabel, arg)])
    ->
      if compatible pat arg then body else exp
  | _ -> exp
