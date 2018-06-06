(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "soswitness"

exception Parse_error

(* Various constructors and destructors needed. *)

let find_constant contrib dir s =
  Universes.constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "soswitness"
let init_constant dir s = find_constant contrib_name dir s


let eq_cst c constant = Constr.equal c (Lazy.force constant)

let datatypes_path = ["Coq"; "Init"; "Datatypes"]
let coq_nat_ind = lazy (init_constant datatypes_path "nat")
let coq_nat_O = lazy (init_constant datatypes_path "O")
let coq_nat_S = lazy (init_constant datatypes_path "S")

let rec mkNat n =
  if n <= 0 then Lazy.force coq_nat_O
  else Term.mkApp (Lazy.force coq_nat_S, [|mkNat (n - 1)|])

let rec ofNat c = match snd (Term.decompose_app c) with
  | [] -> 0
  | c :: _ -> ofNat c + 1

let coq_list_ind = lazy (init_constant datatypes_path "list")
let coq_list_nil = lazy (init_constant datatypes_path "nil")
let coq_list_cons = lazy (init_constant datatypes_path "cons")

let tyList tye = Term.mkApp (Lazy.force coq_list_ind, [|tye|])
                         
let mkList tye mke l =
  let nil = Lazy.force coq_list_nil in
  let cons = Lazy.force coq_list_cons in
  let rec aux l = match l with
    | [] -> Term.mkApp (nil, [|tye|])
    | h :: t -> Term.mkApp (cons, [|tye; mke h; aux t|]) in
  aux l
                
let rec ofList ofe c = match snd (Term.decompose_app c) with
  | [] | [_] (*nil*) -> []
  | [_; h; t] (*cons*) -> ofe h :: ofList ofe t
  | _ -> raise Parse_error

let coq_prod = lazy (init_constant datatypes_path "prod")
let coq_pair = lazy (init_constant datatypes_path "pair")

let tyPair tya tyb = Term.mkApp (Lazy.force coq_prod, [|tya; tyb|])
                        
let mkPair tya tyb mka mkb (a, b) =
  Term.mkApp (Lazy.force coq_pair, [|tya; tyb; mka a; mkb b|])
                
let ofPair ofa ofb c = match snd (Term.decompose_app c) with
  | [_; _; a; b] -> ofa a, ofb b
  | _ -> raise Parse_error

let positive_path = ["Coq"; "Numbers"; "BinNums"]
let coq_positive_ind = lazy (init_constant positive_path "positive")
let coq_positive_I = lazy (init_constant positive_path "xI")
let coq_positive_O = lazy (init_constant positive_path "xO")
let coq_positive_H = lazy (init_constant positive_path "xH")

let rec mkPositive n =
  if n <= 1 then Lazy.force coq_positive_H
  else if n mod 2 = 0 then
    Term.mkApp (Lazy.force coq_positive_O, [|mkPositive (n / 2)|])
  else
    Term.mkApp (Lazy.force coq_positive_I, [|mkPositive (n / 2)|])

let rec ofPositive c = match Term.decompose_app c with
  | c, [] -> 1
  | c, [n] when eq_cst c coq_positive_O -> 2 * ofPositive n
  | c, [n] (*when eq_cst c coq_positive_I*) -> 2 * ofPositive n + 1
  | _ -> raise Parse_error

let nat_path = ["Coq"; "Numbers"; "BinNums"]
let coq_N_ind = lazy (init_constant nat_path "N")
let coq_N_0 = lazy (init_constant nat_path "N0")
let coq_N_pos = lazy (init_constant nat_path "Npos")

let mkN n =
  if n <= 0 then Lazy.force coq_N_0
  else Term.mkApp (Lazy.force coq_N_pos, [|mkPositive n|])

let ofN c = match snd (Term.decompose_app c) with
  | [] -> 0
  | p :: _ -> ofPositive p

let int31_path = ["Coq"; "Numbers"; "Cyclic"; "Int31"; "Int31"]
let coq_int31_ind = lazy (init_constant int31_path "int31")
let coq_int31_I31 = lazy (init_constant int31_path "I31")
let coq_int31_0 = lazy (init_constant int31_path "D0")
let coq_int31_1 = lazy (init_constant int31_path "D1")

let mkInt31 n =
  let i31 = Lazy.force coq_int31_I31 in
  let d0 = Lazy.force coq_int31_0 in
  let d1 = Lazy.force coq_int31_1 in
  let rec aux d n acc =
    if d <= 0 then acc else
      let q, r = Z.div_rem n (Z.of_int 2) in
      aux (d - 1) q ((if Z.(r = zero) then d0 else d1) :: acc) in
  Term.mkApp (i31, Array.of_list (aux 31 n []))
  
let ofInt31 c =
  let rec aux args acc = match args with
    | [] -> raise Parse_error
    | [d] when eq_cst d coq_int31_0 -> Z.(shift_left (of_int acc) 1)
    | [d] (*when eq_cst d coq_int31_1*) -> Z.(succ (shift_left (of_int acc) 1))
    | d :: t when eq_cst d coq_int31_0 -> aux t (2 * acc)
    | d :: t (*when eq_cst d coq_int31_1*) -> aux t (2 * acc + 1) in
  aux (snd (Term.decompose_app c)) 0

let zn2z_path = ["Coq"; "Numbers"; "Cyclic"; "DoubleCyclic"; "DoubleType"]
let coq_zn2z_ind = lazy (init_constant zn2z_path "zn2z")
let coq_zn2z_W0 = lazy (init_constant zn2z_path "W0")
let coq_zn2z_WW = lazy (init_constant zn2z_path "WW")

let rec tyZn2z hght =
  if hght <= 0 then Lazy.force coq_int31_ind
  else Term.mkApp (Lazy.force coq_zn2z_ind, [|tyZn2z (hght - 1)|])
                       
let mkZn2z hght n =
  let w0 = Lazy.force coq_zn2z_W0 in
  let wW = Lazy.force coq_zn2z_WW in
  let rec aux hght n =
    if hght <= 0 then mkInt31 n else if Z.(n = zero) then w0 else
      let hght' = hght - 1 in
      let h, l = Z.div_rem n (Z.shift_left Z.one (31 * (1 lsl hght'))) in
      Term.mkApp (wW, [|tyZn2z hght'; aux hght' h; aux hght' l|]) in
  aux hght n
  
let ofZn2z hght c =
  let rec aux hght c =
    if hght <= 0 then ofInt31 c else
      match snd (Term.decompose_app c) with
      | [_] (* DoubleType.W0 *) -> Z.zero
      | [_; h; l] (* DoubleType.WW *) ->
         let hght' = hght - 1 in
         let h, l = aux hght' h, aux hght' l in
         Z.add (Z.shift_left h (31 * (1 lsl hght'))) l
      | _ -> raise Parse_error in
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

let mkBigN n =
  let rec height pow2 acc =
    if Z.lt n pow2 then acc else height Z.(pow2 * pow2) (acc + 1) in
  let hght = height Z.(shift_left one 31) 0 in
  let word = mkZn2z hght n in
  match hght with
  | 0 -> Term.mkApp (Lazy.force coq_bigN_N0, [|word|])
  | 1 -> Term.mkApp (Lazy.force coq_bigN_N1, [|word|])
  | 2 -> Term.mkApp (Lazy.force coq_bigN_N2, [|word|])
  | 3 -> Term.mkApp (Lazy.force coq_bigN_N3, [|word|])
  | 4 -> Term.mkApp (Lazy.force coq_bigN_N4, [|word|])
  | 5 -> Term.mkApp (Lazy.force coq_bigN_N5, [|word|])
  | 6 -> Term.mkApp (Lazy.force coq_bigN_N6, [|word|])
  | _ -> Term.mkApp (Lazy.force coq_bigN_Nn, [|mkNat (hght - 7); word|])
  
let ofBigN c = match Term.decompose_app c with
  | c, [i] when eq_cst c coq_bigN_N0 -> ofInt31 i
  | c, [d] when eq_cst c coq_bigN_N1 -> ofZn2z 1 d
  | c, [d] when eq_cst c coq_bigN_N2 -> ofZn2z 2 d
  | c, [d] when eq_cst c coq_bigN_N3 -> ofZn2z 3 d
  | c, [d] when eq_cst c coq_bigN_N4 -> ofZn2z 4 d
  | c, [d] when eq_cst c coq_bigN_N5 -> ofZn2z 5 d
  | c, [d] when eq_cst c coq_bigN_N6 -> ofZn2z 6 d
  | c, [n; d] when eq_cst c coq_bigN_Nn -> ofZn2z (ofNat n + 7) d
  | _ -> raise Parse_error

let bigZ_path = ["Coq"; "Numbers"; "Integer"; "BigZ"; "BigZ"; "BigZ"]
let coq_bigZ_ind = lazy (init_constant bigZ_path "t")
let coq_bigZ_Pos = lazy (init_constant bigZ_path "Pos")
let coq_bigZ_Neg = lazy (init_constant bigZ_path "Neg")

let mkBigZ n =
  if Z.sign n >= 0 then Term.mkApp (Lazy.force coq_bigZ_Pos, [|mkBigN n|])
  else Term.mkApp (Lazy.force coq_bigZ_Neg, [|mkBigN (Z.neg n)|])

let ofBigZ c = match Term.decompose_app c with
  | c, [n] when eq_cst c coq_bigZ_Pos -> ofBigN n
  | c, [n] (*when eq_cst c coq_bigZ_Neg*) -> Z.neg (ofBigN n)
  | _ -> raise Parse_error

let bigQ_path = ["Coq"; "Numbers"; "Rational"; "BigQ"; "BigQ"; "BigQ"]
let coq_bigQ_ind = lazy (init_constant bigQ_path "t_")
let coq_bigQ_Qz = lazy (init_constant bigQ_path "Qz")
let coq_bigQ_Qq = lazy (init_constant bigQ_path "Qq")

let mkBigQ q =
  if Z.(Q.den q = one) then
    Term.mkApp (Lazy.force coq_bigQ_Qz, [|mkBigZ (Q.num q)|])
  else
    Term.mkApp (Lazy.force coq_bigQ_Qq, [|mkBigZ (Q.num q); mkBigN (Q.den q)|])
                
let ofBigQ c = match snd (Term.decompose_app c) with
  | [n] (*Qz*) -> Q.of_bigint (ofBigZ n)
  | [n; d] (*Qq*) -> Q.make (ofBigZ n) (ofBigN d)
  | _ -> raise Parse_error

let float_path = ["Interval"; "Interval_specific_ops"]
let coq_float_ind = lazy (init_constant float_path "s_float")
let coq_float_nan = lazy (init_constant float_path "Fnan")
let coq_float_float = lazy (init_constant float_path "Float")

let mkFloat f =
  let bigZ = Lazy.force coq_bigZ_ind in
  let nan = Term.mkApp (Lazy.force coq_float_nan, [|bigZ; bigZ|]) in
  let float = Term.mkApp (Lazy.force coq_float_float, [|bigZ; bigZ|]) in
  let fl m e = Term.mkApp (float, [|mkBigZ m; mkBigZ e|]) in
  match classify_float f with
  | FP_normal ->
     let m, e = frexp f in
     fl (Z.of_float (m *. 2. ** 52.)) (Z.of_int (e - 52))
  | FP_subnormal ->
     let m = f *. 2. ** 1022. *. 2. ** 52. in  (* 2**1074 would overflow *)
     fl (Z.of_float m) (Z.of_int (-1074))
  | FP_zero -> fl Z.zero Z.zero
  | FP_infinite | FP_nan -> nan

let parameters_path = ["ValidSDP"; "soswitness"]
let coq_parameters_ind = lazy (init_constant parameters_path "validsdp_tac_parameters")
let coq_parameters_s_sdpa = lazy (init_constant parameters_path "s_sdpa")
let coq_parameters_s_csdp = lazy (init_constant parameters_path "s_csdp")
let coq_parameters_s_mosek = lazy (init_constant parameters_path "s_mosek")
let coq_parameters_s_verbose = lazy (init_constant parameters_path "s_verbose")

type validsdp_tac_parameters = S_sdpa | S_csdp | S_mosek | S_verbose of int

let ofParameters p = match Term.decompose_app p with
  | c, [] when eq_cst c coq_parameters_s_sdpa -> S_sdpa
  | c, [] when eq_cst c coq_parameters_s_csdp -> S_csdp
  | c, [] when eq_cst c coq_parameters_s_mosek -> S_mosek
  | c, [n] when eq_cst c coq_parameters_s_verbose -> S_verbose (ofNat n)
  | _ -> raise Parse_error

(*
let error msg = CErrors.errorlabstrm "" msg
let errorpp msg = CErrors.error msg
 *)
exception SosFail of int * Pp.std_ppcmds
let fail level msg = raise (SosFail(level, msg))
let failpp level msg = raise (SosFail(level, Pp.str msg))
let maxlevel = 999
let error msg = fail maxlevel msg (* could be set a smaller level *)
let errorpp msg = failpp maxlevel msg
let failtac level msg = Tacticals.New.tclFAIL level msg

(* The actual tactic. *)
       
module Sos = Osdp.Sos.Q
module SosP = Sos.Poly

(* [psatz q] calls OSDP to retrieve witnesses for q >= lb. Returns
   [nb_vars, lb, (z, Q), []] where [nb_vars] is the number of
   variables appearing in [q], [lb] is maximized if [intro = true] and
   [0] otherwise, [z, Q] (z : vector of monomials, Q : float matrix)
   is a witness for q >= 0. *)
let psatz intro options q =
  let nb_vars = SosP.nb_vars q in
  let lb = Sos.make "lb" in
  let ret, _, vals, wl =
    if intro then Sos.solve ~options (Sos.Maximize lb) [Sos.(!!q - lb)]
    else Sos.solve ~options Sos.Purefeas [Sos.(!!q)] in
  match (ret = Osdp.SdpRet.Success), wl with
  | (false, _ | _, []) ->
     Format.printf "l27@."; errorpp "soswitness: OSDP found no witnesses"
  | _, (zQ :: _) ->
     let array_to_list (z, q) =
       Array.(to_list (map Osdp.Monomial.to_list z), to_list (map to_list q)) in
     let lb = if intro then Sos.value lb vals else Q.zero in
     nb_vars, lb, array_to_list zQ, []

(* [psatz_hyps q [p1;...; pn]] calls OSDP to retrieve witnesses for
   p1 >= 0 -> ... -> pn >= 0 -> q >= lb. Returns [nb_vars, lb, (z, Q),
   [(s1, (z1, Q1));...; (sn, (zn, Qn))]] where [nb_vars] is the number
   of variables appearing in [p1,..., pn, q], [lb] is maximized when
   [intro = true] and [0] otherwise, [z, Q] (z : vector of monomials,
   Q : float matrix) is a witness for q - \sum_i si pi >= 0 and each
   (zi, Qi) is a witness for si >= 0. *)
let psatz_hyps intro options q pl =
  let get_wits keep =
    let nb_vars = List.map SosP.nb_vars (q :: pl) |> List.fold_left max 0 in
    let coeff = Sos.make "c" in
    let lb = Sos.make "lb" in
    let sum, sigmas =
      let degs = List.map SosP.degree (q :: pl) in
      let max_deg = List.fold_left max 0 degs in
      let max_deg_list =
        (q :: pl) |> List.map SosP.degree_list
        |> List.map Osdp.Monomial.of_list
        |> List.fold_left Osdp.Monomial.lcm Osdp.Monomial.one in
      let rup n = (n + 1) / 2 * 2 in
      let rup_monomial m =
        Osdp.Monomial.of_list (List.map rup (Osdp.Monomial.to_list m)) in
      let sum = if intro then Sos.(!!q - lb) else Sos.(coeff * !!q) in
      List.fold_left
        (fun (sum, sigmas) p ->
          let s =
            let l =
              let d = max_deg - SosP.degree p in
              let d = if keep then d else rup d in
              Sos.to_list (Sos.make ~n:nb_vars ~d "s") in
            let l =
              if keep then l else
                let lim =
                  let p_list = Osdp.Monomial.of_list (SosP.degree_list p) in
                  rup_monomial (Osdp.Monomial.div max_deg_list p_list) in
                List.filter (fun (m, _) -> Osdp.Monomial.divide m lim) l in
            Sos.of_list l in
          Sos.(sum - s * !!p), s :: sigmas)
        (sum, []) pl in
    let ret, _, vals, wl =
      if intro then
        Sos.solve ~options (Sos.Maximize lb) (sum :: List.rev sigmas)
      else
        Sos.solve ~options Sos.Purefeas (sum :: coeff :: List.rev sigmas) in
    if ret <> Osdp.SdpRet.Success then None
    else
      match wl with
      | [] | [_] -> assert false
      | h :: t when intro -> Some (nb_vars, lb, coeff, sigmas, vals, h, t)
      | h :: _ :: t -> Some (nb_vars, lb, coeff, sigmas, vals, h, t) in
  let w = match get_wits false with
    | (Some _) as w -> w
    | None -> get_wits true in
  match w with
  | None -> errorpp "soswitness: OSDP found no witnesses"
  | Some (nb_vars, lb, coeff, sigmas, vals, zQ, zQl) ->
     let sigmas = List.rev_map (fun e -> Sos.value_poly e vals) sigmas in
     if intro then
       let array_to_list (z, q) =
         Array.(to_list (map Osdp.Monomial.to_list z), to_list (map to_list q)) in
       let szQl = List.combine sigmas (List.map array_to_list zQl) in
       nb_vars, Sos.value lb vals, array_to_list zQ, szQl
     else
       let coeff = Sos.value coeff vals in
       if SosP.Coeff.equal coeff SosP.Coeff.zero then
         errorpp "soswitness: OSDP found no witnesses";
       let coeff = SosP.Coeff.inv coeff in
       let sigmas = List.map (SosP.mult_scalar coeff) sigmas in
       let coeff = SosP.Coeff.to_float coeff in
       let array_to_list (z, q) =
         let q = Array.map (Array.map (fun c -> coeff *. c)) q in
         Array.(to_list (map Osdp.Monomial.to_list z), to_list (map to_list q)) in
       let szQl = List.combine sigmas (List.map array_to_list zQl) in
       nb_vars, Q.zero, array_to_list zQ, szQl

let soswitness intro options c =
  let ty_N = Lazy.force coq_N_ind in
  let ty_seqmultinom = tyList ty_N in
  let ty_bigQ = Lazy.force coq_bigQ_ind in
  let ty_poly = tyList (tyPair ty_seqmultinom ty_bigQ) in
  (* Deconstruct the input (translate it from Coq to OCaml). *)
  let q, pl =
    let ofSeqmultinom c = Osdp.Monomial.of_list (ofList ofN c) in
    let ofPoly c =
      Osdp.Sos.Q.Poly.of_list (ofList (ofPair ofSeqmultinom ofBigQ) c) in
    try
      ofPair ofPoly (ofList ofPoly) c
    with Parse_error ->
      let ty_input = tyPair ty_poly (tyList ty_poly) in
      fail maxlevel
        Pp.(str "soswitness: wrong input type (expected "
            ++ Printer.pr_constr ty_input ++ str ").") in
  let () =  (* TODO: try to fix that *)
    if Osdp.Sos.Q.Poly.is_const q <> None then
      errorpp "soswitness: expects a closed term representing \
               a non constant polynomial" in
  (* Call OSDP to retrieve witnesses *)
  let nb_vars, lb, zq, szql =
    match pl with
    | [] -> psatz intro options q
    | _ -> psatz_hyps intro options q pl in
  (* Add trailing zeros to multinoms in z so that they all have same length. *)
  let rec add_tr_0 n l = match l with
    | [] -> if n <= 0 then [] else 0 :: add_tr_0 (n - 1) []
    | h :: t -> h :: add_tr_0 (n - 1) t in
  let add_zeros (z, q) = List.map (add_tr_0 nb_vars) z, q in
  let zq, szql = add_zeros zq, List.map (fun (s, zq) -> s, add_zeros zq) szql in
  (* Reconstruct the output (translate it from OCaml to Coq). *)
  let ty_seqmultinom_list = tyList ty_seqmultinom in
  let ty_bigZ = Lazy.force coq_bigZ_ind in
  let ty_float = Term.mkApp (Lazy.force coq_float_ind, [|ty_bigZ; ty_bigZ|]) in
  let ty_float_list = tyList ty_float in
  let ty_float_matrix = tyList ty_float_list in
  let ty_witness = tyPair ty_seqmultinom_list ty_float_matrix in
  let mk_witness (zQ : int list list * float list list) : Term.constr =
    mkPair
      ty_seqmultinom_list ty_float_matrix
      (mkList ty_seqmultinom (mkList ty_N mkN))
      (mkList ty_float_list (mkList ty_float mkFloat))
      zQ in
  let mk_s_witness =
    let mkSeqmultinom m =
      mkList ty_N mkN (add_tr_0 nb_vars (Osdp.Monomial.to_list m)) in
    let mkPoly p =
      mkList
        (tyPair ty_seqmultinom ty_bigQ)
        (mkPair ty_seqmultinom ty_bigQ mkSeqmultinom mkBigQ)
        (Osdp.Sos.Q.Poly.to_list p) in
    mkPair ty_poly ty_witness mkPoly mk_witness in
  let t = tyPair ty_witness (tyList (tyPair ty_poly ty_witness)) in
  let wits =
    mkPair
      ty_witness (tyList (tyPair ty_poly ty_witness))
      mk_witness
      (mkList (tyPair ty_poly ty_witness) mk_s_witness)
      (zq, szql) in
  if not intro then (wits, t)
  else (mkPair ty_bigQ t mkBigQ (fun t -> t) (lb, wits), tyPair ty_bigQ t)

let soswitness intro options gl c id =
  let (v, t), ti = Osdp.Utils.profile (fun () -> soswitness intro options c) in
  if options.Sos.verbose > 0 then
    Format.printf "soswitness took: %.2fs@." ti;
  Tactics.letin_tac None (Names.Name id) v (Some t) Locusops.nowhere

let soswitness_opts ?(intro=false) gl c id opts =
  let opts = ofList ofParameters opts in
  let options =
    List.fold_left
      (fun options opt -> match opt with
         | S_sdpa ->
           { options with
             Sos.sdp =
               { options.Sos.sdp with Osdp.Sdp.solver = Osdp.Sdp.Sdpa } }
         | S_csdp ->
           { options with
             Sos.sdp =
               { options.Sos.sdp with Osdp.Sdp.solver = Osdp.Sdp.Csdp } }
         | S_mosek ->
           { options with
             Sos.sdp =
               { options.Sos.sdp with Osdp.Sdp.solver = Osdp.Sdp.Mosek } }
         | S_verbose n ->
           { options with
             Sos.verbose = n;
             Sos.sdp =
               { options.Sos.sdp with Osdp.Sdp.verbose = n } } )
      Sos.default opts in
  try soswitness intro options gl c id
  with SosFail (level, msg) -> failtac level msg
     | Failure msg -> failtac maxlevel (Pp.str msg)
     | e -> let msg = "Anomaly: " ^ (Printexc.to_string e) in
            failtac maxlevel Pp.(str msg)

open Constrarg

TACTIC EXTEND soswitness_of_as
["soswitness" "of" constr(c) "as" ident(id) ] ->
[ Proofview.Goal.enter { Proofview.Goal.enter = fun gl ->
    let gl = Proofview.Goal.assume gl in
    let opts =
      mkList (Lazy.force coq_parameters_ind) (fun () -> assert false) [] in
    soswitness_opts gl c id opts } ]
|
["soswitness" "of" constr(c) "as" ident(id) "with" constr(opts) ] ->
[ Proofview.Goal.enter { Proofview.Goal.enter = fun gl ->
    let gl = Proofview.Goal.assume gl in
    soswitness_opts gl c id opts } ]
|
["soswitness_intro" "of" constr(c) "as" ident(id) ] ->
[ Proofview.Goal.enter { Proofview.Goal.enter = fun gl ->
    let gl = Proofview.Goal.assume gl in
    let opts =
      mkList (Lazy.force coq_parameters_ind) (fun () -> assert false) [] in
    soswitness_opts ~intro:true gl c id opts } ]
|
["soswitness_intro" "of" constr(c) "as" ident(id) "with" constr(opts) ] ->
[ Proofview.Goal.enter { Proofview.Goal.enter = fun gl ->
    let gl = Proofview.Goal.assume gl in
    soswitness_opts ~intro:true gl c id opts } ]
END
