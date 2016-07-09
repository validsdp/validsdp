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

(* debug *)
let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)
let ppconstr c = Format.printf "%a@." pp_constr c

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

let coq_list_ind = lazy (init_constant datatypes_path "list")
let coq_list_nil = lazy (init_constant datatypes_path "nil")
let coq_list_cons = lazy (init_constant datatypes_path "cons")

let tyList tye = mkApp (Lazy.force coq_list_ind, [| tye |])
                         
let mkList tye mke l =
  let nil = Lazy.force coq_list_nil in
  let cons = Lazy.force coq_list_cons in
  let rec aux l = match l with
    | [] -> mkApp (nil, [| tye |])
    | h :: t -> mkApp (cons, [| tye; mke h; aux t |]) in
  aux l
                
let rec ofList ofe c = match snd (decompose_app c) with
  | [] | [_] (*nil*) -> []
  | [_; h; t] (*cons*) -> ofe h :: ofList ofe t
  | _ -> assert false

let coq_prod = lazy (init_constant datatypes_path "prod")
let coq_pair = lazy (init_constant datatypes_path "pair")

let tyPair tya tyb = mkApp (Lazy.force coq_prod, [| tya; tyb |])
                        
let mkPair tya tyb mka mkb (a, b) =
  mkApp (Lazy.force coq_pair, [| tya; tyb; mka a; mkb b |])
                
let ofPair ofa ofb c = match snd (decompose_app c) with
  | [_; _; a; b] -> ofa a, ofb b
  | _ -> assert false

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
  mkApp (i31, Array.of_list (aux 31 n []))
  
let ofInt31 c =
  let rec aux args acc = match args with
    | [] -> assert false
    | [d] when eq_cstr d coq_int31_0 -> Z.(shift_left (of_int acc) 1)
    | [d] (*when eq_cstr d coq_int31_1*) -> Z.(succ (shift_left (of_int acc) 1))
    | d :: t when eq_cstr d coq_int31_0 -> aux t (2 * acc)
    | d :: t (*when eq_cstr d coq_int31_1*) -> aux t (2 * acc + 1) in
  aux (snd (decompose_app c)) 0

let zn2z_path = ["Coq"; "Numbers"; "Cyclic"; "DoubleCyclic"; "DoubleType"]
let coq_zn2z_ind = lazy (init_constant zn2z_path "zn2z")
let coq_zn2z_W0 = lazy (init_constant zn2z_path "W0")
let coq_zn2z_WW = lazy (init_constant zn2z_path "WW")

let rec tyZn2z hght =
  if hght <= 0 then Lazy.force coq_int31_ind
  else mkApp (Lazy.force coq_zn2z_ind, [| tyZn2z (hght - 1) |])
                       
let mkZn2z hght n =
  let w0 = Lazy.force coq_zn2z_W0 in
  let wW = Lazy.force coq_zn2z_WW in
  let rec aux hght n =
    if hght <= 0 then mkInt31 n else if Z.(n = zero) then w0 else
      let hght' = hght - 1 in
      let h, l = Z.div_rem n (Z.shift_left Z.one (31 * (1 lsl hght'))) in
      mkApp (wW, [| tyZn2z hght'; aux hght' h; aux hght' l |]) in
  aux hght n
  
let ofZn2z hght c =
  let rec aux hght c =
    if hght <= 0 then ofInt31 c else
      match snd (decompose_app c) with
      | [_] (* DoubleType.W0 *) -> Z.zero
      | [_; h; l] (* DoubleType.WW *) ->
         let hght' = hght - 1 in
         let h, l = aux hght' h, aux hght' l in
         Z.add (Z.shift_left h (31 * (1 lsl hght'))) l
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

let mkBigN n =
  let rec height pow2 acc =
    if Z.(n < pow2) then acc else height Z.(pow2 * pow2) (acc + 1) in
  let hght = height Z.(shift_left one 31) 0 in
  let word = mkZn2z hght n in
  match hght with
  | 0 -> mkApp (Lazy.force coq_bigN_N0, [| word |])
  | 1 -> mkApp (Lazy.force coq_bigN_N1, [| word |])
  | 2 -> mkApp (Lazy.force coq_bigN_N2, [| word |])
  | 3 -> mkApp (Lazy.force coq_bigN_N3, [| word |])
  | 4 -> mkApp (Lazy.force coq_bigN_N4, [| word |])
  | 5 -> mkApp (Lazy.force coq_bigN_N5, [| word |])
  | 6 -> mkApp (Lazy.force coq_bigN_N6, [| word |])
  | _ -> mkApp (Lazy.force coq_bigN_Nn, [| mkNat (hght - 7); word |])
  
let ofBigN c = match decompose_app c with
  | c, [i] when eq_cstr c coq_bigN_N0 -> ofInt31 i
  | c, [d] when eq_cstr c coq_bigN_N1 -> ofZn2z 1 d
  | c, [d] when eq_cstr c coq_bigN_N2 -> ofZn2z 2 d
  | c, [d] when eq_cstr c coq_bigN_N3 -> ofZn2z 3 d
  | c, [d] when eq_cstr c coq_bigN_N4 -> ofZn2z 4 d
  | c, [d] when eq_cstr c coq_bigN_N5 -> ofZn2z 5 d
  | c, [d] when eq_cstr c coq_bigN_N6 -> ofZn2z 6 d
  | c, [n; d] when eq_cstr c coq_bigN_Nn -> ofZn2z (ofNat n + 7) d
  | _ -> assert false

let bigZ_path = ["Coq"; "Numbers"; "Integer"; "BigZ"; "BigZ"; "BigZ"]
let coq_bigZ_ind = lazy (init_constant bigZ_path "t")
let coq_bigZ_Pos = lazy (init_constant bigZ_path "Pos")
let coq_bigZ_Neg = lazy (init_constant bigZ_path "Neg")

let mkBigZ n =
  if Z.sign n >= 0 then mkApp (Lazy.force coq_bigZ_Pos, [| mkBigN n |])
  else mkApp (Lazy.force coq_bigZ_Neg, [| mkBigN (Z.neg n) |])
                        
let ofBigZ c = match decompose_app c with
  | c, [n] when eq_cstr c coq_bigZ_Pos -> ofBigN n
  | c, [n] (*when eq_cstr c coq_bigZ_Neg*) -> Z.neg (ofBigN n)
  | _ -> assert false

let bigQ_path = ["Coq"; "Numbers"; "Rationals"; "BigQ"; "BigQ"; "BigQ"]
let coq_bigQ_Qz = lazy (init_constant bigZ_path "Qz")
let coq_bigQ_Qq = lazy (init_constant bigZ_path "Qq")

let mkBigQ q =
  if Z.(Q.den q = one) then
    mkApp (Lazy.force coq_bigQ_Qz, [| mkBigZ (Q.num q) |])
  else
    mkApp (Lazy.force coq_bigQ_Qq, [| mkBigZ (Q.num q); mkBigN (Q.den q) |])
                
let ofBigQ c = match snd (decompose_app c) with
  | [n] (*Qz*) -> Q.of_bigint (ofBigZ n)
  | [n; d] (*Qq*) -> Q.make (ofBigZ n) (ofBigN d)
  | _ -> assert false

let float_path = ["Interval"; "Interval_specific_ops"]
let coq_float_ind = lazy (init_constant float_path "s_float")
let coq_float_nan = lazy (init_constant float_path "Fnan")
let coq_float_float = lazy (init_constant float_path "Float")

let mkFloat f =
  let bigZ = Lazy.force coq_bigZ_ind in
  let nan = mkApp (Lazy.force coq_float_nan, [| bigZ; bigZ |]) in
  let float = mkApp (Lazy.force coq_float_float, [| bigZ; bigZ |]) in
  let fl = fun m e -> mkApp (float, [| mkBigZ m; mkBigZ e |]) in
  match classify_float f with
  | FP_normal ->
     let m, e = frexp f in
     fl (Z.of_float (m *. 2. ** 52.)) (Z.of_int (e - 52))
  | FP_subnormal ->
     let m = f *. 2. ** 1022. *. 2. ** 52. in  (* 2**1074 would overflow *)
     fl (Z.of_float m) (Z.of_int (-1074))
  | FP_zero -> fl Z.zero Z.zero
  | FP_infinite | FP_nan -> nan
                           
let ofSeqmultinom c = Osdp.Monomial.of_list (ofList ofNat c)

let ofSeqMultinomCoeff c =
  Osdp.Sos.Q.Poly.of_list (ofList (ofPair ofSeqmultinom ofBigQ) c)

let soswitness env c =
  let p = ofSeqMultinomCoeff c in
  let _ =
    Pp.(msg_info (str (Format.asprintf "p = %a@." Osdp.Sos.Q.Poly.pp p))) in
  let _, _, _, wl =
    Osdp.Sos.Q.solve Osdp.Sos.Q.Purefeas [Osdp.Sos.Q.Const p] in
  let z, q =
    match wl with
    | [] -> (*fail*)
       Format.printf "no witness@.";
       [], []
    | [z, q] ->
       Format.printf
         "z, q = @[(@[%a@]),@ [@[%a@]]@]@."
         (Osdp.Utils.pp_array ~sep:",@ " Osdp.Monomial.pp)
         z
         (Osdp.Utils.pp_matrix
            ~begl:"@[" ~endl:"@]" ~sepl:";@ " ~sepc:",@ " Format.pp_print_float)
         q;
       let tr_monom =
         let rec add_tr_0 n l =
           if n <= 0 then l else
             match l with
             | [] -> 0 :: add_tr_0 (n - 1) []
             | h :: t -> h :: add_tr_0 (n - 1) t in
         let nb_vars =
           Array.fold_left (fun n m -> max n (Osdp.Monomial.nb_vars m)) 0 z in
         fun m -> add_tr_0 nb_vars (Osdp.Monomial.to_list m) in
       Array.(to_list (map tr_monom z), to_list (map to_list q))
    | _ -> assert false in
  let ty_nat = Lazy.force coq_nat_ind in
  let ty_seqmultinom = tyList ty_nat in
  let ty_seqmultinom_list = tyList ty_seqmultinom in
  let ty_bigZ = Lazy.force coq_bigZ_ind in
  let ty_float = mkApp (Lazy.force coq_float_ind, [| ty_bigZ; ty_bigZ |]) in
  let ty_float_list = tyList ty_float in
  let ty_float_matrix = tyList ty_float_list in
  mkPair
    ty_seqmultinom_list ty_float_matrix
    (mkList ty_seqmultinom (mkList ty_nat mkNat))
    (mkList ty_float_list (mkList ty_float mkFloat))
    (z, q),
  tyPair ty_seqmultinom_list ty_float_matrix

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
