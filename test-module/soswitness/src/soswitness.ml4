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

let eq_cstr c constant = Constr.equal c (Lazy.force constant)

let datatypes_path = ["Coq"; "Init"; "Datatypes"]
let coq_nat_ind = lazy (init_constant datatypes_path "nat")
let coq_nat_O = lazy (init_constant datatypes_path "O")
let coq_nat_S = lazy (init_constant datatypes_path "S")

let rec mkNat n =
  if n <= 0 then Lazy.force coq_nat_O
  else mkApp (Lazy.force coq_nat_S, [| mkNat (n - 1) |])

let rec ofNat c = match snd (decompose_app c) with
  | [] -> 0
  | c :: _ -> ofNat c + 1

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

let ppconstr c = Format.printf "%a@." pp_constr c

let int31_path = ["Coq"; "Numbers"; "Cyclic"; "Int31"; "Int31"]
let coq_int31_0 = lazy (init_constant int31_path "D0")
let coq_int31_1 = lazy (init_constant int31_path "D1")

let ofint31 c =
  let rec aux args cur = match args with
    | [] -> assert false
    | [d] when eq_cstr d coq_int31_0 -> Z.(shift_left (of_int cur) 1)
    | [d] (*when eq_cstr d coq_int31_1*) -> Z.(succ (shift_left (of_int cur) 1))
    | d :: t when eq_cstr d coq_int31_0 -> aux t (2 * cur)
    | d :: t (*when eq_cstr d coq_int31_1*) -> aux t (2 * cur + 1) in
  aux (snd (decompose_app c)) 0

let ofzn2z hght c =
  let rec pow n = if n <= 0 then 1 else 2 * pow (n - 1) in
  let rec aux hght c =
    if hght <= 0 then ofint31 c else
      match snd (decompose_app c) with
      | [_] (* DoubleType.W0 *) -> Z.zero
      | [_; h; l] (* DoubleType.WW *) ->
         let hght' = hght - 1 in
         let h, l = aux hght' h, aux hght' l in
         Z.add (Z.shift_left h (31 * pow hght')) l
      | _ -> assert false in
  aux hght c

let bigN_path = ["Coq"; "Numbers"; "Natural"; "BigN"; "BigN"; "BigN"]
let coq_bigN_N0 = lazy (init_constant bigN_path "N0")
let coq_bigN_N1 = lazy (init_constant bigN_path "N1")
let coq_bigN_N2 = lazy (init_constant bigN_path "N2")
let coq_bigN_N3 = lazy (init_constant bigN_path "N3")
let coq_bigN_N4 = lazy (init_constant bigN_path "N4")
let coq_bigN_N5 = lazy (init_constant bigN_path "N5")
let coq_bigN_N6 = lazy (init_constant bigN_path "N6")
let coq_bigN_Nn = lazy (init_constant bigN_path "Nn")

let ofBigN c = match decompose_app c with
  | c, [i] when eq_cstr c coq_bigN_N0 ->
     let i = ofint31 i in
     let _ = Pp.(msg_info (str "i: " ++ int (Z.to_int i))) in
     Pp.(msg_info (str "ofBigN, N0: " ++ Printer.pr_constr c))
  | c, [d] when eq_cstr c coq_bigN_N1 ->
     let i = ofzn2z 1 d in
     let _ = Pp.(msg_info (str "i: " ++ str (Z.to_string i))) in
     Pp.(msg_info (str "ofBigN, N1: " ++ Printer.pr_constr c))
  | c, [d] when eq_cstr c coq_bigN_N2 ->
     let i = ofzn2z 2 d in
     let _ = Pp.(msg_info (str "i: " ++ str (Z.to_string i))) in
     Pp.(msg_info (str "ofBigN, N2: " ++ Printer.pr_constr c))
  | c, [d] when eq_cstr c coq_bigN_N3 ->
     let i = ofzn2z 3 d in
     let _ = Pp.(msg_info (str "i: " ++ str (Z.to_string i))) in
     Pp.(msg_info (str "ofBigN, N3: " ++ Printer.pr_constr c))
  | c, [d] when eq_cstr c coq_bigN_N4 ->
     let i = ofzn2z 4 d in
     let _ = Pp.(msg_info (str "i: " ++ str (Z.to_string i))) in
     Pp.(msg_info (str "ofBigN, N4: " ++ Printer.pr_constr c))
  | c, [d] when eq_cstr c coq_bigN_N5 ->
     let i = ofzn2z 5 d in
     let _ = Pp.(msg_info (str "i: " ++ str (Z.to_string i))) in
     Pp.(msg_info (str "ofBigN, N5: " ++ Printer.pr_constr c))
  | c, [d] when eq_cstr c coq_bigN_N6 ->
     let i = ofzn2z 6 d in
     let _ = Pp.(msg_info (str "i: " ++ str (Z.to_string i))) in
     Pp.(msg_info (str "ofBigN, N6: " ++ Printer.pr_constr c))
  | c, args when eq_cstr c coq_bigN_Nn ->
     (* TODO *)
     Pp.(msg_info (str "ofBigN, Nn: " ++ Printer.pr_constr c))
  | _ -> assert false

let soswitness env c =
  let _ = ofBigN c in
  mkNat 0, Lazy.force coq_nat_ind
(*  mkNat (ofNat c / 2), Lazy.force coq_nat_ind*)

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
