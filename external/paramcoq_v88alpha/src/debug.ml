(**************************************************************************)
(*                                                                        *)
(*     CoqParam                                                           *)
(*     Copyright (C) 2012                                                 *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*     Marc Lasson                                                        *)
(*                                                                        *)
(*     INRIA - École Polytechnique - ÉNS de Lyon                          *)
(*                                                                        *)
(*   This file is distributed under the terms of the GNU Lesser General   *)
(*   Public License                                                       *)
(*                                                                        *)
(**************************************************************************)

open Ltac_plugin
open Names
open Vars
open Environ
open Context
open EConstr
open Pp

let toCDecl (old: Names.name * ((Constr.constr) option) * Constr.constr) : Context.Rel.Declaration.t =
  let (name,value,typ) = old in
  match value with
  | Some value -> Context.Rel.Declaration.LocalDef (name,value,typ)
  | None -> Context.Rel.Declaration.LocalAssum (name,typ)

let toDecl (old: Names.name * ((constr) option) * constr) : rel_declaration =
  let (name,value,typ) = old in
  match value with
  | Some value -> Context.Rel.Declaration.LocalDef (name,value,typ)
  | None -> Context.Rel.Declaration.LocalAssum (name,typ)

let fromDecl (n: rel_declaration) :  Names.name * ('a option) * 'a =
  match n with
  | Context.Rel.Declaration.LocalDef (name,value,typ) -> (name,Some value,typ)
  | Context.Rel.Declaration.LocalAssum (name,typ) -> (name,None,typ)

(*
let fromFromLocalEntry (l: Entries.local_entry): Constr.constr =
  match l with
  | Entries.LocalDefEntry c -> c
  | Entries.LocalAssumEntry c -> c
*)

let all = [`ProofIrrelevance;
           `Abstraction;
           `Relation;
           `Translate;
           `Fix;
           `Case;
           `GenericUnfolding;
           `Unfolding;
           `Inductive;
           `Module;
           `Realizer; `Opacity]

(* let debug_flag = [`Time; `Module; `Realizer; `Translate; `Cast; `Inductive; `Module] *)
let debug_flag = [`Fix; `Abstraction; `Time; `Module; `Realizer; `Translate; `Inductive; `Module]

let debug_mode = ref false
let set_debug_mode =
   Goptions.declare_bool_option
    { Goptions.optdepr  = false;
      Goptions.optname  = "Parametricity Debug";
      Goptions.optkey   = ["Parametricity"; "Debug"];
      Goptions.optread  = (fun () -> !debug_mode);
      Goptions.optwrite = (:=) debug_mode }

let debug_rename_env env evd =
  let rc = EConstr.rel_context env in
  let env = Environ.reset_context env in
  let rc = Namegen.name_context env evd rc in
  let env = push_rel_context rc env in
  Namegen.make_all_name_different env evd

let debug_message flags s e =
  if !debug_mode && List.exists (fun x -> List.mem x flags) debug_flag then
    Feedback.msg_notice Pp.(str s ++ e)

let debug_env flags (s : string) env evd =
  if !debug_mode && List.exists (fun x -> List.mem x flags) debug_flag then
    let env = debug_rename_env env evd in
    Feedback.(msg_notice (Pp.str s ++ Printer.pr_context_of env evd))



let debug_undefined_evars evd c =
  let ev = Evarutil.undefined_evars_of_term evd c in
  Feedback.(msg_notice (Pp.int (Evar.Set.cardinal ev) ++ Pp.str " undefined evars:"));
  Evar.Set.iter
    (fun e ->
      Feedback.(msg_notice (Pp.str "evar: "
                            ++ Evar.print e)))
    ev

let debug flags (s : string) env evd c =
  if !debug_mode && List.exists (fun x -> List.mem x flags) debug_flag then
    try
      let env = debug_rename_env env evd in
      Feedback.(msg_notice (Pp.str s
       ++ Printer.pr_context_of env evd));
      Feedback.(msg_notice (Pp.str ""
         ++ Pp.str "\n |-"
         ++ Printer.pr_econstr_env env evd c))
    with e -> Feedback.(msg_notice (str (Printf.sprintf "Caught exception while debugging '%s'" (Printexc.to_string e)))); raise e

let debug_evar_map flags s evd =
  if !debug_mode && List.exists (fun x -> List.mem x flags) debug_flag then (
    Feedback.msg_info Pp.(str s ++ Termops.pr_evar_universe_context (Evd.evar_universe_context evd)))

let debug_string flags s =
  if !debug_mode && List.exists (fun x -> List.mem x flags) debug_flag then
    Feedback.msg_notice (Pp.str ("--->\t"^s))

let debug_case_info flags ci =
  let open Constr in
  if !debug_mode && List.exists (fun x -> List.mem x flags) debug_flag then
    let (ind, k) = ci.ci_ind in
    let ind_string = Printf.sprintf "%s[%d]" (MutInd.to_string ind) k in
    let param = ci.ci_npar in
    let ndecls = String.concat ";" (List.map string_of_int (Array.to_list ci.ci_cstr_ndecls)) in
    let nargs = String.concat ";" (List.map string_of_int (Array.to_list ci.ci_cstr_nargs)) in
    let pp_info x =
      let ind_tags = String.concat ";" (List.map string_of_bool x.ind_tags) in
      let cstr_tags =
        String.concat "," (List.map (fun tags -> String.concat ";" (List.map string_of_bool tags))
        (Array.to_list x.cstr_tags))
      in
      let string_of_style = match x.style with
        LetStyle -> "LetStyle" | IfStyle -> "IfStyle" | LetPatternStyle -> "LetPatternStyle" | MatchStyle -> "MatchStyle" | RegularStyle -> "RegularStyle"
      in
      Printf.sprintf "ind_tags = %s, cstr_tags = %s, style = %s" ind_tags cstr_tags string_of_style
    in
    debug_string flags
  (Printf.sprintf "CASEINFO:inductive = %s.\nparam = %d.\nndecls = %s.\nnargs = %s.\npp_info = %s\n.EOFCASEINFO"
      ind_string
      param
      ndecls
      nargs
      (pp_info ci.ci_pp_info))

let debug_rel_context flags s env l =
  if !debug_mode && List.exists (fun x -> List.mem x flags) debug_flag then
    Feedback.msg_notice Pp.(str s ++ (Termops.print_rel_context (push_rel_context l env)))

let not_implemented ?(reason = "no reason") env evd t =
  debug [`Not_implemented] (Printf.sprintf "not implemented (%s):" reason) env evd t;
  failwith "not_implemented"

module SortSet = Set.Make(Sorts)
let rec sorts accu t = match Constr.kind t with
 | Sort t -> SortSet.add t accu
 | _ -> Constr.fold sorts accu t

let debug_mutual_inductive_entry =
  let open Entries in
  let open Pp in
  let field name value cont = (align ()) ++ (str name) ++ (str " : ") ++ value ++ fnl () ++ cont in
  let rec debug_mutual_inductive_entry evd entry =
    let mind_entry_record_pp = str
      (match entry.mind_entry_record with
        | Some (Some id) ->
           Printf.sprintf "Some (Some %s)" (Id.to_string id)
        | Some None -> "Some None"
        | None -> "None")
    in
    let mind_entry_finite_pp =
      let open Decl_kinds in str
      (match entry.mind_entry_finite with
       Finite -> "Finite" | CoFinite -> "CoFinite" | BiFinite -> "BiFinite")
    in
    debug_string all "env_params:"
    ;
    let env_params =
      List.fold_left (fun acc ->
          function
          | (id, Entries.LocalAssumEntry typ) ->
             debug_env all "acc = " acc evd;
             debug all "typ = " acc evd (of_constr typ);
             Environ.push_rel (toCDecl (Name id, None, typ)) acc
          | (id, Entries.LocalDefEntry def) ->
             debug_env all "acc = " acc evd;
             debug all "def = " acc evd (of_constr def);
             let edef = EConstr.of_constr def in
             Environ.push_rel (toCDecl (Name id, Some def,
                                        EConstr.Unsafe.to_constr (Typing.unsafe_type_of acc evd edef))) acc)
       (Global.env ()) (List.rev entry.mind_entry_params)
    in
    debug_string all "arities:";
    let mind_entry_params_pp = Printer.pr_context_of env_params Evd.empty in
    let arities = List.map
      (fun entry -> entry.mind_entry_typename, entry.mind_entry_arity)
      entry.mind_entry_inds
    in
    let mind_entry_inds_pp =
      List.fold_left app (str "")
       (List.map (pp_one_inductive_entry arities env_params) entry.mind_entry_inds)
    in
    let mind_entry_polymorphic_pp =
      str (match entry.mind_entry_universes with
           | Monomorphic_ind_entry _ -> "false"
           | Polymorphic_ind_entry _ -> "true"
           | Cumulative_ind_entry _ -> "cumulative"
          )
    in
    let mind_entry_universes_pp =
      match entry.mind_entry_universes with
      | Monomorphic_ind_entry ux ->
         Univ.pr_universe_context_set Universes.pr_with_global_universes ux
      | Polymorphic_ind_entry ux ->
         Univ.pr_universe_context Universes.pr_with_global_universes ux
      | Cumulative_ind_entry ci -> Univ.pr_cumulativity_info Universes.pr_with_global_universes ci
    in
    let mind_entry_private_pp =
      match entry.mind_entry_private with
       None -> str "None" | Some true -> str "Some true" | Some false -> str "Some false"
    in
    let fields = List.rev
       [ "mind_entry_record", mind_entry_record_pp;
         "mind_entry_finite", mind_entry_finite_pp;
         "mind_entry_params", mind_entry_params_pp;
         "mind_entry_inds", mind_entry_inds_pp;
         "mind_entry_polymorphic", mind_entry_polymorphic_pp;
         "mind_entry_universes", mind_entry_universes_pp;
         "mind_entry_private", mind_entry_private_pp]
    in
    let res = (str "{") ++ h 140 (
    List.fold_left (fun acc (name, pp) ->
        field name pp acc) (mt ()) fields) ++ str "}" in
    Feedback.msg_notice res;
    let sorts = List.fold_left (fun accu ind ->
      sorts accu ind.mind_entry_arity) SortSet.empty entry.mind_entry_inds
    in
    let sorts_pp =
      SortSet.fold (fun sort accu ->
       accu ++ (Printer.pr_sort evd sort) ++ fnl ()) sorts (mt ())
    in
    Feedback.msg_notice (h 100 sorts_pp)
  and pp_one_inductive_entry arities env_params entry =
    let params = Environ.rel_context env_params in
    let arities = List.map (fun (x, y) -> (x, Term.it_mkProd_or_LetIn y params)) arities in

    let arities_params_env =
      let env_arities =
        List.fold_left (fun acc (id, arity) -> Environ.push_rel (toCDecl (Name id, None, arity)) acc)
                       Environ.empty_env (List.rev arities)
      in
      Environ.push_rel_context params env_arities
    in
    let mind_entry_typename_pp =
      str (Id.to_string entry.mind_entry_typename)
    in
    let mind_entry_arity_pp =
      Printer.safe_pr_constr_env env_params Evd.empty entry.mind_entry_arity
    in
    let mind_entry_template_pp = str (if entry.mind_entry_template then "true" else "false") in
    let mind_entry_consnames_pp =
      str (String.concat ";" (List.map Id.to_string entry.mind_entry_consnames))
    in
    let mind_entry_lc_pp =
      List.fold_left app (str "")
      (List.map (Printer.safe_pr_constr_env arities_params_env Evd.empty) entry.mind_entry_lc)
    in
    let fields =
       [ "mind_entry_typename", mind_entry_typename_pp;
         "mind_entry_arity", mind_entry_arity_pp;
         "mind_entry_template", mind_entry_template_pp;
         "mind_entry_consnames", mind_entry_consnames_pp;
         "mind_entry_lc", mind_entry_lc_pp ]
    in
    str "{" ++ h 100 (
    List.fold_left (fun acc (name, pp) ->
        field name pp acc) (mt ()) fields) ++ str "}"
  in
  fun evd entry -> if !debug_mode then
    debug_mutual_inductive_entry evd entry
