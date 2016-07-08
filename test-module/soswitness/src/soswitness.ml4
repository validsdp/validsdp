(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

DECLARE PLUGIN "soswitness"

open Term
open Names
open Coqlib
open Universes 
open Globnames
open Vars
open Errors

let find_constant contrib dir s =
  constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "soswitness"
let init_constant dir s = find_constant contrib_name dir s

let datatypes_path = ["Coq";"Init";"Datatypes"]

let coq_nat_ind = lazy (init_constant datatypes_path "nat")
let coq_nat_O = lazy (init_constant datatypes_path "O")
let coq_nat_S = lazy (init_constant datatypes_path "S")

let rec mkNat n =
  if n <= 0 then Lazy.force coq_nat_O
  else mkApp (Lazy.force coq_nat_S, [| mkNat (n - 1) |])

let rec ofNat c = match snd (decompose_app c) with
  | [] -> 0
  | c :: _ -> ofNat c + 1

let soswitness env c =
  mkNat (ofNat c / 2), Lazy.force coq_nat_ind

open Tacmach
open Tacticals
open Tacexpr
open Tacinterp

let soswitness gl c id = 
  let open Proofview in
  let open Notations in
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let v, t = soswitness env c in
  let tac = V82.tactic (Refiner.tclEVARS (fst (Typing.type_of env sigma v))) in
  let nowhere = Locus.({ onhyps = Some []; concl_occs = NoOccurrences }) in
  tac <*> Tactics.letin_tac None (Name id) v (Some t) nowhere

TACTIC EXTEND soswitness_of_in
| ["soswitness" "of" constr(c) "in" ident(id) ] -> 
  [ Proofview.Goal.enter 
      (fun gl ->
       let gl = Proofview.Goal.assume gl in
       soswitness gl c id) ]
END
