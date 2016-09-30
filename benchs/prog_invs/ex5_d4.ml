(* Attempt to prove that p >= 0 with p at the end of this file is an
 * inductive invariant, for the program
 *
x1 = rand(0.9, 1.1);
x2 = rand(0, 0.2);
x3 = rand(0, 0.2);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2; pre_x3 = x3;
  if (x1^2 + x2^2 + x3^2 <= 1) {
    x1 = 0.25 * (0.8 * pre_x1^2 + 1.4 * pre_x2 - 0.5 * pre_x3^2);
    x2 = 0.25 * (1.3 * pre_x1 + 0.5 * pre_x3^2);
    x3 = 0.25 * (1.4 * pre_x2 + 0.8 * pre_x3^2);
  } else {
    x1 = 0.25 * (0.8 * pre_x1 + 0.4 * pre_x2^2);
    x2 = 0.25 * (-0.6 * pre_x2^2 + 0.3 * pre_x3^2);
    x3 = 0.25 * (0.5 * pre_x3 + 0.4 * pre_x1^2);
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
 * % ./ex5_d4 *)

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

let x1, x2, x3 = Sos.(??0, ??1, ??2)

(* initial condition 0.9 <= x1 <= 1.1 encoded as (x1 - 0.9)*(1.1 - x1) (>= 0) *)
let pI1 = Sos.((x1 - 9 / 10) * (11 / 10 - x1))
(* initial condition 0 <= x2 <= 0.2 *)
let pI2 = Sos.(x2 * (2 / 10 - x2))
(* initial condition 0 <= x3 <= 0.2 *)
let pI3 = Sos.(x3 * (2 / 10 - x3))
(* guard x1^2 + x2^2 + x3^2 <= 1 (then branch) *)
let g0 = Sos.(1 / 1 - (x1**2 + x2**2 + x3**2))
(* assignment in then branch *)
let t0 = Sos.([1 / 4 * (8 / 10 * x1**2 + 14 / 10 * x2 - 5 / 10 * x3**2);
               1 / 4 * (13 / 10 * x1**2 + 5 / 10 * x3**2);
               1 / 4 * (14 / 10 * x2 + 8 / 10 * x3**2)])
(* guard x1^2 + x2^2 + x3^2 >= 1 (else branch) *)
let g1 = Sos.((x1**2 + x2**2 + x3**2) - 1 / 1)
(* assignment in else branch *)
let t1 = Sos.([1 / 4 * (8 / 10 * x1 + 4 / 10 * x2**2);
               1 / 4 * ((-6) / 10 * x2**2 + 3 / 10 * x3**2);
               1 / 4 * (5 / 10 * x3 + 4 / 10 * x1**2)])

(* chack that invariant p >= 0 satisfy initial conditions and is inductive *)
let check_inv p =
  let deg = Sos.Poly.degree p in
  let rnd n = n / 2 * 2 in
  let check_init, sigma1, sigma2, sigma3 =
    (* p - \sigma1 pI1 - \sigma2 pI2 >= 0, \sigma{1,2} >= 0 *)
    let init, sigma1, sigma2, sigma3 =
      let sigma1, _ = Sos.var_poly "s1" 3 (rnd (deg - Sos.degree pI1)) in
      let sigma2, _ = Sos.var_poly "s2" 3 (rnd (deg - Sos.degree pI2)) in
      let sigma3, _ = Sos.var_poly "s3" 3 (rnd (deg - Sos.degree pI3)) in
      Sos.(!!p - sigma1 * pI1 - sigma2 * pI2 - sigma3 * pI3), sigma1, sigma2, sigma3 in
    let ret, _, vals, _ = Sos.solve ~options Sos.Purefeas [init; sigma1; sigma2; sigma3] in
    let sigma1 = Sos.value_poly sigma1 vals in
    let sigma2 = Sos.value_poly sigma2 vals in
    let sigma3 = Sos.value_poly sigma3 vals in
    ret = Osdp.SdpRet.Success, sigma1, sigma2, sigma3 in
  if not print_poly then Format.printf "check_init: %B@." check_init;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma1 x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp sigma1;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma2 x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp sigma2;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma3 x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp sigma3;
  let recheck_init, t_recheck_init =
    Osdp.Utils.profile
      (fun () ->
       let init = Sos.(!!p - !!sigma1 * pI1 - !!sigma2 * pI2 - !!sigma3 * pI3) in
       let options = options_recheck in
       let ret, _, _, _ =
         Sos.(solve ~options Purefeas [init; !!sigma1; !!sigma2; !!sigma3]) in
       ret = Osdp.SdpRet.Success) in
  if not print_poly then Format.printf "recheck_init: %B@." recheck_init;
  if not print_poly then Format.printf "time recheck_init: %.2fs@." t_recheck_init;
  let check_t0, sigma, sigma0 =
    (* p \circ t0 - \sigma p - \sigma_0 g0 >= 0, \sigma >= 0, \sigma_0 >=0 *)
    let ind0, sigma, sigma0 =
      let deg0 = List.fold_left max 0 (List.map Sos.degree t0) in
      let sigma, _ = Sos.var_poly "s" 3 (rnd ((deg0 - 1) * deg)) in
      let sigma0, _ = Sos.var_poly "s0" 3 (rnd (deg * deg0 - Sos.degree g0)) in
      Sos.(compose !!p t0 - sigma * !!p - sigma0 * g0), sigma, sigma0 in
    let ret, _, vals, _ =
      Sos.solve ~options Sos.Purefeas [ind0; sigma; sigma0] in
    let sigma = Sos.value_poly sigma vals in
    let sigma0 = Sos.value_poly sigma0 vals in
    ret = Osdp.SdpRet.Success, sigma, sigma0 in
  if not print_poly then Format.printf "check_ind0: %B@." check_t0;
  if print_poly then
    Format.printf "@[<v 2>Let ind0_sigma x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp sigma;
  if print_poly then
    Format.printf "@[<v 2>Let ind0_sigma0 x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp sigma0;
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
      let sigma, _ = Sos.var_poly "s" 3 (rnd ((deg1 - 1) * deg)) in
      let sigma1, _ = Sos.var_poly "s1" 3 (rnd (deg * deg1 - Sos.degree g1)) in
      Sos.(compose !!p t1 - sigma * !!p - sigma1 * g1), sigma, sigma1 in
    (* Format.printf "ind1 : %a@." Sos.pp ind1; *)
    let ret, _, vals, _ =
      Sos.solve ~options Sos.Purefeas [ind1; sigma; sigma1] in
    let sigma = Sos.value_poly sigma vals in
    let sigma1 = Sos.value_poly sigma1 vals in
    ret = Osdp.SdpRet.Success, sigma, sigma1 in
  if not print_poly then Format.printf "check_ind1: %B@." check_t1;
  if print_poly then
    Format.printf "@[<v 2>Let ind1_sigma x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp sigma;
  if print_poly then
    Format.printf "@[<v 2>Let ind1_sigma1 x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp sigma1;
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
    let x0, x1, x2 = P.(??0, ??1, ??2) in
    P.("376932522065681012931"/"295147905179352825856" + "8509962722502765"/"295147905179352825856" * 
        x0 + "4810786678983139"/"147573952589676412928" * x1 + "8195275705635465"/"1180591620717411303424" * 
        x2 + "-5286590888873701"/"4503599627370496" * x0**2 + "3142771579399875"/"36028797018963968" * 
        x0 * x1 + "-591108560874675"/"281474976710656" * x1**2 + "1261458973270647"/"2251799813685248" * 
        x0 * x2 + "5929053759940775"/"72057594037927936" * x1 * x2 + "-1259727915632095"/"562949953421312" * 
        x2**2 + "1149275400895391"/"4503599627370496" * x0**3 + "7285847311712275"/"18014398509481984" * 
        x0**2 * x1 + "8440266932050133"/"18014398509481984" * x0 * x1**2 + "4371217067606495"/"36028797018963968" * 
        x1**3 + "-458360830646393"/"1125899906842624" * x0**2 * x2 + "-2813070140505775"/"4503599627370496" * 
        x0 * x1 * x2 + "-8737122075031031"/"72057594037927936" * x1**2 * x2 + "3341105181056463"/"4503599627370496" * 
        x0 * x2**2 + "7431847970290251"/"18014398509481984" * x1 * x2**2 + "-7134326653543871"/"288230376151711744" * 
        x2**3 + "-4419035466710003"/"36028797018963968" * x0**4 + "-3191026702181451"/"18014398509481984" * 
        x0**3 * x1 + "-8852489850214139"/"72057594037927936" * x0**2 * x1**2 + "-2762344079633701"/"36028797018963968" * 
        x0 * x1**3 + "-974190988861453"/"36028797018963968" * x1**4 + "4592531851313069"/"36028797018963968" * 
        x0**3 * x2 + "1897745899402969"/"9007199254740992" * x0**2 * x1 * x2 + "3929173054132589"/"36028797018963968" * 
        x0 * x1**2 * x2 + "5952875244748005"/"288230376151711744" * x1**3 * x2 + "-5462054773810051"/"36028797018963968" * 
        x0**2 * x2**2 + "-5346287477580991"/"36028797018963968" * x0 * x1 * x2**2 + "-92562462037723"/"2251799813685248" * 
        x1**2 * x2**2 + "8810307269401287"/"576460752303423488" * x0 * x2**3 + "3135835432654057"/"576460752303423488" * 
        x1 * x2**3 + "-569947876840979"/"288230376151711744" * x2**4) in
  if print_poly then
    Format.printf "@[<v 2>Let p x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp p;
  let res = check_inv p in
  if not print_poly then Format.printf "Invariant p >= 0 proved: %B@." res
