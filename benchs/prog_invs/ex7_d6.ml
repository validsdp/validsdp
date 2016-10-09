(* Attempt to prove that p >= 0 with p at the end of this file is an
 * inductive invariant, for the program
 *
x1 = rand(0.5, 0.7);
x2 = rand(0.5, 0.7);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2;
  if (x1^2 + x2^2 <= 1) {
    x1 = pre_x1^2 + pre_x2^3;
    x2 = pre_x1^3 + pre_x2^2;
  } else {
    x1 = 0.5 * pre_x1^3 + 0.4 * pre_x2^2;
    x2 = -0.6 * pre_x1^2 + 0.3 * pre_x2^2;
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
 * % ./ex7_d6 *)

module Sos = struct
  include Osdp.Sos.Q
  let ( / ) n m = Q.of_int n /. Q.of_int m
end

let options = { Sos.default with
                Sos.verbose = 0(*3*);
                Sos.sdp =
                  { Osdp.Sdp.default with
                    Osdp.Sdp.solver = Osdp.Sdp.Mosek } }

let x1, x2 = Sos.(??0, ??1)

(* initial condition 0.5 <= x1 <= 0.7 encoded as (x1 - 0.5)*(0.7 - x1) (>= 0) *)
let pI1 = Sos.((x1 - 5 / 10) * (7 / 10 - x1))
(* initial condition 0.5 <= x2 <= 0.7 *)
let pI2 = Sos.((x2 - 5 / 10) * (7 / 10 - x2))
(* guard x1^2 + x2^2 <= 1 (then branch) *)
let g0 = Sos.(1 / 1 - (x1**2 + x2**2))
(* assignment in then branch *)
let t0 = Sos.([x1**2 + x2**3;
               x1**3 + x2**2])
(* guard x1^2 + x2^2 >= 1 (else branch) *)
let g1 = Sos.((x1**2 + x2**2) - 1 / 1)
(* assignment in else branch *)
let t1 = Sos.([5 / 10 * x1**3 + 4 / 10 * x2**2;
               (-6) / 10 * x1**2 + 3 / 10 * x2**2])

(* chack that invariant p >= 0 satisfy initial conditions and is inductive *)
let check_inv p polys =
  let sigma1 = List.assoc "init_sigma1" polys in
  let sigma2 = List.assoc "init_sigma2" polys in
  let check_init, t_check_init =
    Osdp.Utils.profile
      (fun () ->
       let init = Sos.(!!p - !!sigma1 * pI1 - !!sigma2 * pI2) in
       let ret, _, _, _ =
         Sos.(solve ~options Purefeas [init; !!sigma1; !!sigma2]) in
       ret = Osdp.SdpRet.Success) in
  Format.printf "check_init: %B@." check_init;
  Format.printf "time check_init: %.2fs@." t_check_init;
  let sigma = List.assoc "ind0_sigma" polys in
  let sigma0 = List.assoc "ind0_sigma0" polys in
  let check_ind0, t_check_ind0 =
    Osdp.Utils.profile
      (fun () ->
       let ind0 = Sos.(compose !!p t0 - !!sigma * !!p - !!sigma0 * g0) in
       let ret, _, _, _ =
         Sos.(solve ~options Purefeas [ind0; !!sigma; !!sigma0]) in
       ret = Osdp.SdpRet.Success) in
  Format.printf "check_ind0: %B@." check_ind0;
  Format.printf "time check_ind0: %.2fs@." t_check_ind0;
  let sigma = List.assoc "ind1_sigma" polys in
  let sigma1 = List.assoc "ind1_sigma1" polys in
  let check_ind1, t_check_ind1 =
    Osdp.Utils.profile
      (fun () ->
       let ind1 = Sos.(compose !!p t1 - !!sigma * !!p - !!sigma1 * g1) in
       let ret, _, _, _ =
         Sos.(solve ~options Purefeas [ind1; !!sigma; !!sigma1]) in
       ret = Osdp.SdpRet.Success) in
  Format.printf "check_ind1: %B@." check_ind1;
  Format.printf "time check_ind1: %.2fs@." t_check_ind1;
  Format.printf "time check: %.2fs@."
                (t_check_init +. t_check_ind0 +. t_check_ind1);
  check_init && check_ind0 && check_ind1

module P = struct
  include Sos.Poly
  let ( / ) n m = Q.of_string n /. Q.of_string m
end

let _ =
  let p =
    let x0, x1 = P.(??0, ??1) in
    P.("4738216471197271"/"4503599627370496" + "461486665561107"/"36028797018963968" * 
        x0 + "2148860567220837"/"72057594037927936" * x1 + "-8202775146209813"/"2251799813685248" * 
        x0**2 + "-8626419234253377"/"4503599627370496" * x0 * x1 + "-7868078000648565"/"2251799813685248" * 
        x1**2 + "3921066891027203"/"1125899906842624" * x0**3 + "2767544406545225"/"1125899906842624" * 
        x0**2 * x1 + "5506010582442379"/"2251799813685248" * x0 * x1**2 + "3617072631418827"/"4503599627370496" * 
        x1**3 + "-138133466777373"/"70368744177664" * x0**4 + "-8073725813518985"/"18014398509481984" * 
        x0**3 * x1 + "5942106187826601"/"1125899906842624" * x0**2 * x1**2 + "6784102076241101"/"2251799813685248" * 
        x0 * x1**3 + "-5823498136032391"/"36028797018963968" * x1**4 + "1027144908312917"/"4503599627370496" * 
        x0**5 + "-4727205476840271"/"9007199254740992" * x0**4 * x1 + "-5407525212435085"/"2251799813685248" * 
        x0**3 * x1**2 + "-5224058528371821"/"2251799813685248" * x0**2 * x1**3 + "-7991748307902929"/"18014398509481984" * 
        x0 * x1**4 + "1505099781016865"/"1125899906842624" * x1**5 + "-4903820959533185"/"576460752303423488" * 
        x0**6 + "8376633397351463"/"288230376151711744" * x0**5 * x1 + "7978081282562245"/"144115188075855872" * 
        x0**4 * x1**2 + "-6712614333940499"/"36028797018963968" * x0**3 * x1**3 + "-3803524531712927"/"4503599627370496" * 
        x0**2 * x1**4 + "-2951633102464389"/"2251799813685248" * x0 * x1**5 + "-4574065549448907"/"4503599627370496" * 
        x1**6) in
  let polys = Parse.file "ex7_d6.v" in
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p polys)
