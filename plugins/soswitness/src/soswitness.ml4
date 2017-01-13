(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

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

let rec mkN n =
  if n <= 0 then Lazy.force coq_N_0
  else Term.mkApp (Lazy.force coq_N_pos, [|mkPositive n|])

let rec ofN c = match snd (Term.decompose_app c) with
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
    if Z.(n < pow2) then acc else height Z.(pow2 * pow2) (acc + 1) in
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
  let fl = fun m e -> Term.mkApp (float, [|mkBigZ m; mkBigZ e|]) in
  match classify_float f with
  | FP_normal ->
     let m, e = frexp f in
     fl (Z.of_float (m *. 2. ** 52.)) (Z.of_int (e - 52))
  | FP_subnormal ->
     let m = f *. 2. ** 1022. *. 2. ** 52. in  (* 2**1074 would overflow *)
     fl (Z.of_float m) (Z.of_int (-1074))
  | FP_zero -> fl Z.zero Z.zero
  | FP_infinite | FP_nan -> nan
                           
(* The actual tactic. *)
       
(* [psatz (q, [p1;...; pn])] calls OSDP to retrieve witnesses for
   p1 >= 0 -> ... -> pn >= 0 -> q >= 0. Returns [nb_vars, (z, Q),
   [(s1, (z1, Q1));...; (sn, (zn, Qn))]] where [nb_vars] is the number
   of variables appearing in [p1,..., pn, q], [z, Q] (z : vector of
   monomials, Q : float matrix) is a witness for q - \sum_i si pi >= 0
   and each (zi, Qi) is a witness for si >= 0. *)
let psatz q pl =
  let module Sos = Osdp.Sos.Q in
  let module SosP = Sos.Poly in
  let nb_vars = List.map SosP.nb_vars (q :: pl) |> List.fold_left max 0 in
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
    List.fold_left
      (fun (sum, sigmas) p ->
        let s =
          let _, l =
            Sos.var_poly "s" nb_vars (rup (max_deg - SosP.degree p)) in
          let l =
            let lim =
              let p_list = Osdp.Monomial.of_list (SosP.degree_list p) in
              rup_monomial (Osdp.Monomial.div max_deg_list p_list) in
            List.filter (fun (m, _) -> Osdp.Monomial.divide m lim) l in
          List.fold_left
            (fun p (m, v) -> Sos.(add p (mult (monomial m) v)))
            Sos.(!!Poly.zero) l in
        Sos.(sum - s * !!p), s :: sigmas)
      (Sos.(!!q), []) pl in
  let ret, _, vals, wl =
    let options =
      (* { *) Sos.default (* with *)
        (* Sos.verbose = 3 ; *)
        (* Sos.sdp = { Osdp.Sdp.default with Osdp.Sdp.verbose = 1 } } *) in
    Sos.solve ~options ~solver:Osdp.Sdp.Sdpa Sos.Purefeas
              (sum :: List.rev sigmas) in
  let w =
    if ret <> Osdp.SdpRet.Success then None
    else match wl with [] -> assert false | zQ :: zQl -> Some (zQ, zQl) in
  match w with
  | None -> Errors.error "soswitness: OSDP found no witnesses."
  | Some (zQ, zQl) ->
     let sigmas = List.rev_map (fun e -> Sos.value_poly e vals) sigmas in
     let array_to_list (z, q) =
       Array.(to_list (map Osdp.Monomial.to_list z), to_list (map to_list q)) in
     nb_vars, array_to_list zQ, List.combine sigmas (List.map array_to_list zQl)

let soswitness c =
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
      Errors.errorlabstrm
        ""
        Pp.(str "soswitness: wrong input type (expected "
            ++ Printer.pr_constr ty_input ++ str ").") in
  let () =  (* TODO: try to fix that *)
    if Osdp.Sos.Q.Poly.is_const q <> None then
      Errors.error "soswitness: expects a closed term representing \
                    a non constant polynomial." in
  (* Call OSDP to retrieve witnesses *)
  let nb_vars, zq, szql = psatz q pl in
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
  mkPair
    ty_witness (tyList (tyPair ty_poly ty_witness))
    mk_witness
    (mkList (tyPair ty_poly ty_witness) mk_s_witness)
    (zq, szql),
  tyPair ty_witness (tyList (tyPair ty_poly ty_witness))

let soswitness gl c id = 
  let v, t = soswitness c in
  let nowhere = Locus.({ onhyps = Some []; concl_occs = NoOccurrences }) in
  Tactics.letin_tac None (Names.Name id) v (Some t) nowhere

TACTIC EXTEND soswitness_of_as
| ["soswitness" "of" constr(c) "as" ident(id) ] -> 
  [ Proofview.Goal.enter 
      (fun gl ->
       let gl = Proofview.Goal.assume gl in
       soswitness gl c id) ]
END
