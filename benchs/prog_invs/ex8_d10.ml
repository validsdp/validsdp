(* Attempt to prove that p >= 0 with p at the end of this file is an
 * inductive invariant, for the program
 *
x1 = rand(-1.0, 1.0);
x2 = rand(-1.0, 1.0);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2;
  if (x2 <= x1) {
    x1 = 0.687 * pre_x1 + 0.558 * pre_x2 - 0.0001 * pre_x1 * pre_x2;
    x2 = -0.292 * pre_x1 + 0.773 * pre_x2;
  } else {
    x1 = 0.369 * pre_x1 + 0.532 * pre_x2 - 0.0001 * pre_x1^2;
    x2 = -1.27 * pre_x1 + 0.12 * pre_x2 - 0.0001 * pre_x1 * pre_x2;
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
 * % ./ex8_d10 *)

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

let x1, x2 = Sos.(??0, ??1)

(* initial condition -1 <= x1 <= 1 encoded as (x1 - 1)*(1 - x1) (>= 0) *)
let pI1 = Sos.((x1 - 1 / 1) * (1 / 1 - x1))
(* initial condition -1 <= x2 <= 1 *)
let pI2 = Sos.((x2 - 1 / 1) * (1 / 1 - x2))
(* guard x2 <= x1 (then branch) *)
let g0 = Sos.(x1 - x2)
(* assignment in then branch *)
let t0 = Sos.([687 / 1000 * x1 + 558 / 1000 * x2 - 1 / 10000 * x1 * x2;
               (-292) / 1000 * x1 + 773 / 1000 * x2])
(* guard x2 >= x1 (else branch) *)
let g1 = Sos.(x2 - x1)
(* assignment in else branch *)
let t1 = Sos.([369 / 1000 * x1 + 532 / 1000 * x2 - 1 / 10000 * x1**2;
               (-127) / 100 * x1 + 12 / 100 * x2 - 1 / 10000 * x1 * x2])

(* chack that invariant p >= 0 satisfy initial conditions and is inductive *)
let check_inv p =
  let deg = Sos.Poly.degree p in
  let rnd n = n / 2 * 2 in
  let check_init, sigma1, sigma2 =
    (* p - \sigma1 pI1 - \sigma2 pI2 >= 0, \sigma{1,2} >= 0 *)
    let init, sigma1, sigma2 =
      let sigma1, _ = Sos.var_poly "s1" 2 (rnd (deg - Sos.degree pI1)) in
      let sigma2, _ = Sos.var_poly "s2" 2 (rnd (deg - Sos.degree pI2)) in
      Sos.(!!p - sigma1 * pI1 - sigma2 * pI2), sigma1, sigma2 in
    let ret, _, vals, _ = Sos.solve ~options Sos.Purefeas [init; sigma1; sigma2] in
    let sigma1 = Sos.value_poly sigma1 vals in
    let sigma2 = Sos.value_poly sigma2 vals in
    ret = Osdp.SdpRet.Success, sigma1, sigma2 in
  if not print_poly then Format.printf "check_init: %B@." check_init;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma1 x0 x1 :=@ %a.@ @]@." Sos.Poly.pp sigma1;
  if print_poly then
    Format.printf "@[<v 2>Let init_sigma2 x0 x1 :=@ %a.@ @]@." Sos.Poly.pp sigma2;
  let recheck_init, t_recheck_init =
    Osdp.Utils.profile
      (fun () ->
       let init = Sos.(!!p - !!sigma1 * pI1 - !!sigma2 * pI2) in
       let options = options_recheck in
       let ret, _, _, _ =
         Sos.(solve ~options Purefeas [init; !!sigma1; !!sigma2]) in
       ret = Osdp.SdpRet.Success) in
  if not print_poly then Format.printf "recheck_init: %B@." recheck_init;
  if not print_poly then Format.printf "time recheck_init: %.2fs@." t_recheck_init;
  let check_t0, sigma, sigma0 =
    (* p \circ t0 - \sigma p - \sigma_0 g0 >= 0, \sigma >= 0, \sigma_0 >=0 *)
    let ind0, sigma, sigma0 =
      let deg0 = List.fold_left max 0 (List.map Sos.degree t0) in
      let sigma, _ = Sos.var_poly "s" 2 (rnd ((deg0 - 1) * deg)) in
      let sigma0, _ = Sos.var_poly "s0" 2 (rnd (deg * deg0 - Sos.degree g0)) in
      Sos.(compose !!p t0 - sigma * !!p - sigma0 * g0), sigma, sigma0 in
    let ret, _, vals, _ =
      Sos.solve ~options Sos.Purefeas [ind0; sigma; sigma0] in
    let sigma = Sos.value_poly sigma vals in
    let sigma0 = Sos.value_poly sigma0 vals in
    ret = Osdp.SdpRet.Success, sigma, sigma0 in
  if not print_poly then Format.printf "check_ind0: %B@." check_t0;
  if print_poly then
    Format.printf "@[<v 2>Let ind0_sigma x0 x1 :=@ %a.@ @]@." Sos.Poly.pp sigma;
  if print_poly then
    Format.printf "@[<v 2>Let ind0_sigma0 x0 x1 :=@ %a.@ @]@." Sos.Poly.pp sigma0;
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
      let sigma, _ = Sos.var_poly "s" 2 (rnd ((deg1 - 1) * deg)) in
      let sigma1, _ = Sos.var_poly "s1" 2 (rnd (deg * deg1 - Sos.degree g1)) in
      Sos.(compose !!p t1 - sigma * !!p - sigma1 * g1), sigma, sigma1 in
    (* Format.printf "ind1 : %a@." Sos.pp ind1; *)
    let ret, _, vals, _ =
      Sos.solve ~options Sos.Purefeas [ind1; sigma; sigma1] in
    let sigma = Sos.value_poly sigma vals in
    let sigma1 = Sos.value_poly sigma1 vals in
    ret = Osdp.SdpRet.Success, sigma, sigma1 in
  if not print_poly then Format.printf "check_ind1: %B@." check_t1;
  if print_poly then
    Format.printf "@[<v 2>Let ind1_sigma x0 x1 :=@ %a.@ @]@." Sos.Poly.pp sigma;
  if print_poly then
    Format.printf "@[<v 2>Let ind1_sigma1 x0 x1 :=@ %a.@ @]@." Sos.Poly.pp sigma1;
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
    let x0, x1 = P.(??0, ??1) in
    P.("2751369891250564829"/"1152921504606846976" + "-3097717965715433"/"4611686018427387904" * 
        x0**2 + "-1669577382630305"/"9223372036854775808" * x0 * x1 + "-5087457629923805"/"9223372036854775808" * 
        x1**2 + "6178333010432029"/"288230376151711744" * x0**3 + "-3733807525210169"/"144115188075855872" * 
        x0**2 * x1 + "-447350411140235"/"288230376151711744" * x0 * x1**2 + "5058697133185035"/"144115188075855872" * 
        x1**3 + "-5935474593424963"/"2251799813685248" * x0**4 + "-1443237039368917"/"18014398509481984" * 
        x0**3 * x1 + "-6165992812696583"/"2251799813685248" * x0**2 * x1**2 + "-5507320924791329"/"4503599627370496" * 
        x0 * x1**3 + "-3338002160059011"/"2251799813685248" * x1**4 + "6088129726249333"/"9007199254740992" * 
        x0**5 + "-2289635847447407"/"562949953421312" * x0**4 * x1 + "-6419735255785315"/"1125899906842624" * 
        x0**3 * x1**2 + "-6929173244553837"/"9007199254740992" * x0**2 * x1**3 + "5067333275040391"/"9007199254740992" * 
        x0 * x1**4 + "635849871328907"/"562949953421312" * x1**5 + "-6250058693782407"/"4503599627370496" * 
        x0**6 + "5204505599971377"/"1125899906842624" * x0**5 * x1 + "-1859305396320963"/"281474976710656" * 
        x0**4 * x1**2 + "-1499262564252091"/"281474976710656" * x0**3 * x1**3 + "2565118736069077"/"4503599627370496" * 
        x0**2 * x1**4 + "7265881697497037"/"144115188075855872" * x0 * x1**5 + "5157199432811747"/"36028797018963968" * 
        x1**6 + "-4541437987623649"/"36028797018963968" * x0**7 + "5452079272378425"/"1125899906842624" * 
        x0**6 * x1 + "7274817664941309"/"1125899906842624" * x0**5 * x1**2 + "1356130390825973"/"281474976710656" * 
        x0**4 * x1**3 + "6507847885036715"/"1125899906842624" * x0**3 * x1**4 + "357150797539963"/"1125899906842624" * 
        x0**2 * x1**5 + "-8252781156878691"/"9007199254740992" * x0 * x1**6 + "-1616838843261621"/"1125899906842624" * 
        x1**7 + "2927675830487615"/"562949953421312" * x0**8 + "-2995864767016941"/"281474976710656" * 
        x0**7 * x1 + "4647104799839235"/"281474976710656" * x0**6 * x1**2 + "4979819182879587"/"562949953421312" * 
        x0**5 * x1**3 + "399859618481861"/"70368744177664" * x0**4 * x1**4 + "4424465019862403"/"1125899906842624" * 
        x0**3 * x1**5 + "3262997926439249"/"1125899906842624" * x0**2 * x1**6 + "1856928467829909"/"1125899906842624" * 
        x0 * x1**7 + "1598341012866239"/"2251799813685248" * x1**8 + "-7942014041546771"/"72057594037927936" * 
        x0**9 + "-3333308530813159"/"2251799813685248" * x0**8 * x1 + "-5124471921815915"/"2251799813685248" * 
        x0**7 * x1**2 + "-4825820819707963"/"2251799813685248" * x0**6 * x1**3 + "-1904091811909683"/"562949953421312" * 
        x0**5 * x1**4 + "-2380173841684083"/"1125899906842624" * x0**4 * x1**5 + "-390726982423727"/"281474976710656" * 
        x0**3 * x1**6 + "6893291745192459"/"18014398509481984" * x0**2 * x1**7 + "1901642351442651"/"4503599627370496" * 
        x0 * x1**8 + "2462301735840719"/"4503599627370496" * x1**9 + "-5659452882657849"/"2251799813685248" * 
        x0**10 + "6939325838569607"/"1125899906842624" * x0**9 * x1 + "-4805160669944875"/"562949953421312" * 
        x0**8 * x1**2 + "-2333274266582637"/"562949953421312" * x0**7 * x1**3 + "-8599682961494615"/"2251799813685248" * 
        x0**6 * x1**4 + "-1314413742743423"/"1125899906842624" * x0**5 * x1**5 + "-4961001981841713"/"2251799813685248" * 
        x0**4 * x1**6 + "-4784778027034377"/"2251799813685248" * x0**3 * x1**7 + "-1809084932745541"/"1125899906842624" * 
        x0**2 * x1**8 + "-6471928452385259"/"9007199254740992" * x0 * x1**9 + "-3092960601051931"/"9007199254740992" * 
        x1**10) in
  if print_poly then
    Format.printf "@[<v 2>Let p x0 x1 :=@ %a.@ @]@." Sos.Poly.pp p;
  let res = check_inv p in
  if not print_poly then Format.printf "Invariant p >= 0 proved: %B@." res
