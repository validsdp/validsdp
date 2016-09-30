(* Attempt to prove that p >= 0 with p at the end of this file is an
 * inductive invariant, for the program
 *
x1 = rand(0.9, 1.1);
x2 = rand(0, 0.2);
x3 = rand(0, 0.2);
x4 = rand(0, 0.2);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2; pre_x3 = x3; pre_x4 = x4;
  if (x1^2 + x2^2 + x3^2 + x4^2 <= 1) {
    x1 = 0.25 * (0.8 * pre_x1^2 + 1.4 * pre_x2 - 0.5 * pre_x3^2);
    x2 = 0.25 * (1.3 * pre_x1 + 0.5 * pre_x2^2 - 0.8 * pre_x4^2);
    x3 = 0.25 * (0.8 * pre_x3^2 + 1.4 * pre_x4);
    x4 = 0.25 * (1.3 * pre_x3 + 0.5 * pre_x4^2);
  } else {
    x1 = 0.25 * (0.5 * pre_x1 + 0.4 * pre_x2^2);
    x2 = 0.25 * (-0.6 * pre_x1^2 + 0.3 * pre_x2^2);
    x3 = 0.25 * (0.5 * pre_x3 + 0.4 * pre_x4^2);
    x4 = 0.25 * (-0.6 * pre_x3 + 0.3 * pre_x4^2);
  }
}
 *)

(* This requires OSDP (>= 0.4.4, available from
 * https://cavale.enseeiht.fr/osdp/, must be compiled with MOSEK but
 * CSDP, SDPA, GLPK and Camlp4 are not required). To compile:
 *
 * % make
 *
 * and to run:
 *
 * % ./ex6_d4 *)

let solver_synth = Osdp.Sdp.Mosek
let solver_recheck = Osdp.Sdp.Mosek

module Sos = struct
  include Osdp.Sos.Q
  let ( / ) n m = Q.of_int n /. Q.of_int m
end

let options = { Sos.default with
                Sos.verbose = 0(*3*);
                Sos.sdp =
                  { Osdp.Sdp.default with
                    Osdp.Sdp.solver = solver_synth } }

let options_recheck = { Sos.default with
                        Sos.verbose = 0(*3*);
                        Sos.sdp =
                          { Osdp.Sdp.default with
                            Osdp.Sdp.solver = solver_recheck } }

let print_poly = false

let x1, x2, x3, x4 = Sos.(??0, ??1, ??2, ??3)

(* initial condition 0.9 <= x1 <= 1.1 encoded as (x1 - 0.9)*(1.1 - x1) (>= 0) *)
let pI1 = Sos.((x1 - 9 / 10) * (11 / 10 - x1))
(* initial condition 0 <= x2 <= 0.2 *)
let pI2 = Sos.(x2 * (2 / 10 - x2))
(* initial condition 0 <= x3 <= 0.2 *)
let pI3 = Sos.(x3 * (2 / 10 - x3))
(* initial condition 0 <= x4 <= 0.2 *)
let pI4 = Sos.(x4 * (2 / 10 - x4))
(* guard x1^2 + x2^2 + x3^2 + x4^2 <= 1 (then branch) *)
let g0 = Sos.(1 / 1 - (x1**2 + x2**2 + x3**2 + x4**2))
(* assignment in then branch *)
let t0 = Sos.([1 / 4 * (8 / 10 * x1**2 + 14 / 10 * x2 - 5 / 10 * x3**2);
               1 / 4 * (13 / 10 * x1 + 5 / 10 * x2**2 - 8 / 10 * x4**2);
               1 / 4 * (8 / 10 * x3**2 + 14 / 10 * x4);
               1 / 4 * (13 / 10 * x3 + 5 / 10 * x4**2)])

(* guard x1^2 + x2^2 + x3^2 + x4^2 >= 1 (else branch) *)
let g1 = Sos.((x1**2 + x2**2 + x3**2 + x4**2) - 1 / 1)
(* assignment in else branch *)
let t1 = Sos.([1 / 4 * (5 / 10 * x1 + 4 / 10 * x2**2);
               1 / 4 * ((-6) / 10 * x1**2 + 3 / 10 * x2**2);
               1 / 4 * (5 / 10 * x3 + 4 / 10 * x4**2);
               1 / 4 * ((-6) / 10 * x3 + 3 / 10 * x4**2)])

(* chack that invariant p >= 0 satisfy initial conditions and is inductive *)
let check_inv p =
  let deg = Sos.Poly.degree p in
  let rnd n = n / 2 * 2 in
  let check_init, sigma1, sigma2, sigma3, sigma4 =
    (* p - \sigma1 pI1 - \sigma2 pI2 >= 0, \sigma{1,2} >= 0 *)
    let init, sigma1, sigma2, sigma3, sigma4 =
      let sigma1, _ = Sos.var_poly "s1" 4 (rnd (deg - Sos.degree pI1)) in
      let sigma2, _ = Sos.var_poly "s2" 4 (rnd (deg - Sos.degree pI2)) in
      let sigma3, _ = Sos.var_poly "s3" 4 (rnd (deg - Sos.degree pI3)) in
      let sigma4, _ = Sos.var_poly "s4" 4 (rnd (deg - Sos.degree pI4)) in
      Sos.(!!p - sigma1 * pI1 - sigma2 * pI2 - sigma3 * pI3 - sigma4 * pI4), sigma1, sigma2, sigma3, sigma4 in
    let ret, _, vals, _ = Sos.solve ~options Sos.Purefeas [init; sigma1; sigma2; sigma3; sigma4] in
    let sigma1 = Sos.value_poly sigma1 vals in
    let sigma2 = Sos.value_poly sigma2 vals in
    let sigma3 = Sos.value_poly sigma3 vals in
    let sigma4 = Sos.value_poly sigma4 vals in
    ret = Osdp.SdpRet.Success, sigma1, sigma2, sigma3, sigma4 in
  if not print_poly then Format.printf "check_init: %B@." check_init;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma1 x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp sigma1;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma2 x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp sigma2;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma3 x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp sigma3;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma4 x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp sigma4;
  let recheck_init, t_recheck_init =
    Osdp.Utils.profile
      (fun () ->
       let init = Sos.(!!p - !!sigma1 * pI1 - !!sigma2 * pI2 - !!sigma3 * pI3 - !!sigma4 * pI4) in
       let options = options_recheck in
       let ret, _, _, _ =
         Sos.(solve ~options Purefeas [init; !!sigma1; !!sigma2; !!sigma3; !!sigma4]) in
       ret = Osdp.SdpRet.Success) in
  if not print_poly then Format.printf "recheck_init: %B@." recheck_init;
  if not print_poly then Format.printf "time recheck_init: %.2fs@." t_recheck_init;
  let check_t0, sigma, sigma0 =
    (* p \circ t0 - \sigma p - \sigma_0 g0 >= 0, \sigma >= 0, \sigma_0 >=0 *)
    let ind0, sigma, sigma0 =
      let deg0 = List.fold_left max 0 (List.map Sos.degree t0) in
      let sigma, _ = Sos.var_poly "s" 4 (rnd ((deg0 - 1) * deg)) in
      let sigma0, _ = Sos.var_poly "s0" 4 (rnd (deg * deg0 - Sos.degree g0)) in
      Sos.(compose !!p t0 - sigma * !!p - sigma0 * g0), sigma, sigma0 in
    let ret, _, vals, _ =
      Sos.solve ~options Sos.Purefeas [ind0; sigma; sigma0] in
    let sigma = Sos.value_poly sigma vals in
    let sigma0 = Sos.value_poly sigma0 vals in
    ret = Osdp.SdpRet.Success, sigma, sigma0 in
  if not print_poly then Format.printf "check_ind0: %B@." check_t0;
  if print_poly then
    Format.printf "@[<v 2>Let ind0_sigma x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp sigma;
  if print_poly then
    Format.printf "@[<v 2>Let ind0_sigma0 x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp sigma0;
  let recheck_ind0, t_recheck_ind0 =
    Osdp.Utils.profile
      (fun () ->
       let ind0 = Sos.(compose !!p t0 - !!sigma * !!p - !!sigma0 * g0) in
       let options = options_recheck in
       let ret, _, _, _ =
         Sos.(solve ~options Purefeas [ind0; !!sigma; !!sigma0]) in
       ret = Osdp.SdpRet.Success) in
  if not print_poly then Format.printf "recheck_ind0: %B@." recheck_ind0;
  if not print_poly then Format.printf "time recheck_ind0: %.2fs@." t_recheck_ind0;
  let check_t1, sigma, sigma1 =
    (* p \circ t1 - \sigma p - \sigma_1 g1 >= 0, \sigma >= 0, \sigma_1 >=0 *)
    let ind1, sigma, sigma1 =
      let deg1 = List.fold_left max 0 (List.map Sos.degree t1) in
      let sigma, _ = Sos.var_poly "s" 4 (rnd ((deg1 - 1) * deg)) in
      let sigma1, _ = Sos.var_poly "s1" 4 (rnd (deg * deg1 - Sos.degree g1)) in
      Sos.(compose !!p t1 - sigma * !!p - sigma1 * g1), sigma, sigma1 in
    (* Format.printf "ind1 : %a@." Sos.pp ind1; *)
    let ret, _, vals, _ =
      Sos.solve ~options Sos.Purefeas [ind1; sigma; sigma1] in
    let sigma = Sos.value_poly sigma vals in
    let sigma1 = Sos.value_poly sigma1 vals in
    ret = Osdp.SdpRet.Success, sigma, sigma1 in
  if not print_poly then Format.printf "check_ind1: %B@." check_t1;
  if print_poly then
    Format.printf "@[<v 2>Let ind1_sigma x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp sigma;
  if print_poly then
    Format.printf "@[<v 2>Let ind1_sigma1 x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp sigma1;
  let recheck_ind1, t_recheck_ind1 =
    Osdp.Utils.profile
      (fun () ->
       let ind1 = Sos.(compose !!p t1 - !!sigma * !!p - !!sigma1 * g1) in
       let options = options_recheck in
       let ret, _, _, _ =
         Sos.(solve ~options Purefeas [ind1; !!sigma; !!sigma1]) in
       ret = Osdp.SdpRet.Success) in
  if not print_poly then Format.printf "recheck_ind1: %B@." recheck_ind1;
  if not print_poly then Format.printf "time recheck_ind1: %.2fs@." t_recheck_ind1;
  if not print_poly then Format.printf "recheck: %B@." (recheck_init && recheck_ind0 && recheck_ind1);
  if not print_poly then Format.printf "time recheck: %.2fs@."
                                       (t_recheck_init +. t_recheck_ind0 +. t_recheck_ind1);
  check_init && check_t0 && check_t1

module P = struct
  include Sos.Poly
  let ( / ) n m = Q.of_string n /. Q.of_string m
end

let _ =
  let p =
    let x0, x1, x2, x3 = P.(??0, ??1, ??2, ??3) in
    P.("48940054069273278153"/"36893488147419103232" + "5694253208528417"/"36893488147419103232" * 
        x0 + "8102901656505047"/"73786976294838206464" * x1 + "6269474379387387"/"147573952589676412928" * 
        x2 + "3441584900231701"/"73786976294838206464" * x3 + "-4669554109426427"/"4503599627370496" * 
        x0**2 + "92085480506231"/"288230376151711744" * x0 * x1 + "-5598335104289841"/"4503599627370496" * 
        x1**2 + "1843119203387555"/"9007199254740992" * x0 * x2 + "1461108288648583"/"9007199254740992" * 
        x1 * x2 + "-8892369674005945"/"4503599627370496" * x2**2 + "3683663009832627"/"18014398509481984" * 
        x0 * x3 + "4279969919285975"/"144115188075855872" * x1 * x3 + "4599270683968915"/"4503599627370496" * 
        x2 * x3 + "-2426931813006713"/"1125899906842624" * x3**2 + "5679646795147455"/"288230376151711744" * 
        x0**3 + "6898152399613459"/"288230376151711744" * x0**2 * x1 + "7964854552138401"/"288230376151711744" * 
        x0 * x1**2 + "-7996748256319621"/"288230376151711744" * x1**3 + "-3558136104620279"/"72057594037927936" * 
        x0**2 * x2 + "-8703141464088499"/"288230376151711744" * x0 * x1 * x2 + "-6898701029652147"/"144115188075855872" * 
        x1**2 * x2 + "1876121044027675"/"2251799813685248" * x0 * x2**2 + "-4463283652912723"/"18014398509481984" * 
        x1 * x2**2 + "-2162885693276891"/"72057594037927936" * x2**3 + "-5398056230914363"/"72057594037927936" * 
        x0**2 * x3 + "5474141078075247"/"72057594037927936" * x0 * x1 * x3 + "5834256714415749"/"288230376151711744" * 
        x1**2 * x3 + "-8201190208057061"/"4503599627370496" * x0 * x2 * x3 + "5783137378410261"/"9007199254740992" * 
        x1 * x2 * x3 + "4519517124910863"/"72057594037927936" * x2**2 * x3 + "5564976919447915"/"4503599627370496" * 
        x0 * x3**2 + "-4032767964075663"/"9007199254740992" * x1 * x3**2 + "-5705740165923223"/"36028797018963968" * 
        x2 * x3**2 + "5632093774890191"/"36028797018963968" * x3**3 + "-5678805155964555"/"576460752303423488" * 
        x0**4 + "7449854677957833"/"576460752303423488" * x0**3 * x1 + "-2627994069062625"/"576460752303423488" * 
        x0**2 * x1**2 + "8725945813410821"/"18446744073709551616" * x0 * x1**3 + "-8911675626378479"/"9223372036854775808" * 
        x1**4 + "5585412167840481"/"1152921504606846976" * x0**3 * x2 + "-4131646996160293"/"576460752303423488" * 
        x0**2 * x1 * x2 + "7067301336180357"/"576460752303423488" * x0 * x1**2 * x2 + "-444139637288545"/"144115188075855872" * 
        x1**3 * x2 + "-549762786449193"/"2251799813685248" * x0**2 * x2**2 + "239478656343597"/"2251799813685248" * 
        x0 * x1 * x2**2 + "-1878441530106213"/"18014398509481984" * x1**2 * x2**2 + "4223954103278339"/"72057594037927936" * 
        x0 * x2**3 + "-3983274901088115"/"72057594037927936" * x1 * x2**3 + "-2592136743387799"/"4503599627370496" * 
        x2**4 + "1611594838859253"/"288230376151711744" * x0**3 * x3 + "7250209135848541"/"4611686018427387904" * 
        x0**2 * x1 * x3 + "-1227179578630901"/"144115188075855872" * x0 * x1**2 * x3 + "-2073325184724095"/"9223372036854775808" * 
        x1**3 * x3 + "5365581902893101"/"9007199254740992" * x0**2 * x2 * x3 + "-8972440832492619"/"36028797018963968" * 
        x0 * x1 * x2 * x3 + "4571320738466443"/"18014398509481984" * 
        x1**2 * x2 * x3 + "-5260570922044893"/"288230376151711744" * x0 * x2**2 * x3 + "5786032707896575"/"72057594037927936" * 
        x1 * x2**2 * x3 + "5865540286708361"/"2251799813685248" * x2**3 * x3 + "-465574218383891"/"1125899906842624" * 
        x0**2 * x3**2 + "3181253618894765"/"18014398509481984" * x0 * x1 * x3**2 + "-6165504408072355"/"36028797018963968" * 
        x1**2 * x3**2 + "-8236815771369237"/"36028797018963968" * x0 * x2 * x3**2 + "1131632067628285"/"18014398509481984" * 
        x1 * x2 * x3**2 + "-5528298683556665"/"1125899906842624" * x2**2 * x3**2 + "8301825989304093"/"36028797018963968" * 
        x0 * x3**3 + "-4013672348018387"/"36028797018963968" * x1 * x3**3 + "2626355412004073"/"562949953421312" * 
        x2 * x3**3 + "-4180528354014335"/"2251799813685248" * x3**4) in
  if print_poly then
    Format.printf "@[<v 2>Let p x0 x1 x2 x3 :=@ %a.@ @]@." Sos.Poly.pp p;
  let res = check_inv p in
  if not print_poly then Format.printf "Invariant p >= 0 proved: %B@." res
