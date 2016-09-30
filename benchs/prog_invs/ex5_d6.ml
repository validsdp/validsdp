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
 * % ./ex5_d6 *)

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
    P.("11148842843060291029"/"9223372036854775808" + "-3038523017709797"/"147573952589676412928" * 
        x0 + "-2040062184279335"/"73786976294838206464" * x1 + "-1744819625419305"/"147573952589676412928" * 
        x2 + "-7534424154515997"/"2251799813685248" * x0**2 + "7605455650326721"/"9007199254740992" * 
        x0 * x1 + "-1120587160130789"/"281474976710656" * x1**2 + "6115525038782477"/"4503599627370496" * 
        x0 * x2 + "2717536855551575"/"36028797018963968" * x1 * x2 + "-2695358078587379"/"562949953421312" * 
        x2**2 + "4082885647166711"/"1125899906842624" * x0**3 + "-7965558105277639"/"2251799813685248" * 
        x0**2 * x1 + "3566715215490303"/"1125899906842624" * x0 * x1**2 + "3774531100246339"/"2251799813685248" * 
        x1**3 + "-3368934380388715"/"36028797018963968" * x0**2 * x2 + "-6691387167040511"/"18014398509481984" * 
        x0 * x1 * x2 + "4287840329747981"/"72057594037927936" * x1**2 * x2 + "546125018984877"/"140737488355328" * 
        x0 * x2**2 + "6634425606322615"/"18014398509481984" * x1 * x2**2 + "4203154570586865"/"4503599627370496" * 
        x2**3 + "-4789853005973365"/"1125899906842624" * x0**4 + "6424822321346237"/"18014398509481984" * 
        x0**3 * x1 + "-2847109437409909"/"1125899906842624" * x0**2 * x1**2 + "8456325543324165"/"2251799813685248" * 
        x0 * x1**3 + "-8444132257622035"/"1125899906842624" * x1**4 + "-8779841912227093"/"4503599627370496" * 
        x0**3 * x2 + "-1176333443526759"/"2251799813685248" * x0**2 * x1 * x2 + "6449215168082861"/"9007199254740992" * 
        x0 * x1**2 * x2 + "-2387325232629625"/"2251799813685248" * x1**3 * x2 + "8018184649424921"/"36028797018963968" * 
        x0**2 * x2**2 + "7836248156453079"/"2251799813685248" * x0 * x1 * x2**2 + "-3696166239069993"/"562949953421312" * 
        x1**2 * x2**2 + "-5071208151834403"/"9007199254740992" * x0 * x2**3 + "2014340130717431"/"2251799813685248" * 
        x1 * x2**3 + "-5209799962832495"/"562949953421312" * x2**4 + "3403967096450647"/"562949953421312" * 
        x0**5 + "6805483601088709"/"1125899906842624" * x0**4 * x1 + "1646638296351309"/"562949953421312" * 
        x0**3 * x1**2 + "6559690859833595"/"2251799813685248" * x0**2 * x1**3 + "6159356350314271"/"2251799813685248" * 
        x0 * x1**4 + "3857266078087503"/"9007199254740992" * x1**5 + "-1402278648672577"/"1125899906842624" * 
        x0**4 * x2 + "4974683696209663"/"9007199254740992" * x0**3 * x1 * x2 + "3404677542973091"/"2251799813685248" * 
        x0**2 * x1**2 * x2 + "-3089199761170993"/"9007199254740992" * x0 * x1**3 * x2 + "8835937231770709"/"9007199254740992" * 
        x1**4 * x2 + "1504963654096473"/"281474976710656" * x0**3 * x2**2 + "6179719295709989"/"2251799813685248" * 
        x0**2 * x1 * x2**2 + "8321934588509757"/"36028797018963968" * x0 * x1**2 * x2**2 + "5325346037387883"/"9007199254740992" * 
        x1**3 * x2**2 + "1303895724798923"/"1125899906842624" * x0**2 * x2**3 + "4962289518502755"/"4503599627370496" * 
        x0 * x1 * x2**3 + "8051311313548445"/"144115188075855872" * x1**2 * x2**3 + "5629229922149095"/"9007199254740992" * 
        x0 * x2**4 + "1078190555692545"/"2251799813685248" * x1 * x2**4 + "4029472700879393"/"9007199254740992" * 
        x2**5 + "-6905484624451749"/"2251799813685248" * x0**6 + "-4094470219898305"/"1125899906842624" * 
        x0**5 * x1 + "-6835974550320589"/"4503599627370496" * x0**4 * x1**2 + "-3653983831399287"/"1125899906842624" * 
        x0**3 * x1**3 + "-1657584500407475"/"281474976710656" * x0**2 * x1**4 + "-4713140631330757"/"1125899906842624" * 
        x0 * x1**5 + "-149724226870219"/"140737488355328" * x1**6 + "4416029031095903"/"2251799813685248" * 
        x0**5 * x2 + "-5922106847679043"/"18014398509481984" * x0**4 * x1 * x2 + "168628785911401"/"1125899906842624" * 
        x0**3 * x1**2 * x2 + "2447772727689043"/"1125899906842624" * x0**2 * x1**3 * x2 + "4854035513871189"/"4503599627370496" * 
        x0 * x1**4 * x2 + "5157671898941375"/"144115188075855872" * x1**5 * x2 + "-6849355709857453"/"1125899906842624" * 
        x0**4 * x2**2 + "-8112071915959789"/"2251799813685248" * x0**3 * x1 * x2**2 + "-5029666524966815"/"1125899906842624" * 
        x0**2 * x1**2 * x2**2 + "-1256205025462677"/"281474976710656" * 
        x0 * x1**3 * x2**2 + "-8176532954114109"/"4503599627370496" * x1**4 * x2**2 + "7362746665414197"/"2251799813685248" * 
        x0**3 * x2**3 + "-2367424950900109"/"4503599627370496" * x0**2 * x1 * x2**3 + "1271777838816935"/"562949953421312" * 
        x0 * x1**2 * x2**3 + "8492898259532065"/"18014398509481984" * x1**3 * x2**3 + "-2915592515101857"/"562949953421312" * 
        x0**2 * x2**4 + "-6533437770308491"/"2251799813685248" * x0 * x1 * x2**4 + "-7358023390478105"/"4503599627370496" * 
        x1**2 * x2**4 + "2273479135712835"/"2251799813685248" * x0 * x2**5 + "8000120946974601"/"36028797018963968" * 
        x1 * x2**5 + "-8872336316523177"/"72057594037927936" * x2**6) in
  if print_poly then
    Format.printf "@[<v 2>Let p x0 x1 x2 :=@ %a.@ @]@." Sos.Poly.pp p;
  let res = check_inv p in
  if not print_poly then Format.printf "Invariant p >= 0 proved: %B@." res
