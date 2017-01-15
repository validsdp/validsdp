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

module Sos = struct
  include Osdp.Sos.Q
  let ( / ) n m = Q.of_int n /. Q.of_int m
end

let options = { Sos.default with
                Sos.verbose = 0(*3*);
                Sos.sdp =
                  { Osdp.Sdp.default with
                    Osdp.Sdp.solver = Osdp.Sdp.Sdpa } }

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
  let coeff = Sos.make "c" in
  let sigma1 = Sos.make ~n:3 ~d:2 "s1" in
  let sigma2 = Sos.make ~n:3 ~d:2 "s2" in
  let sigma3 = Sos.make ~n:3 ~d:2 "s3" in
  let check_init, t_check_init =
    Osdp.Utils.profile
      (fun () ->
       let init = Sos.(coeff * !!p - sigma1 * pI1 - sigma2 * pI2 - sigma3 * pI3) in
       let ret, _, vals, _ =
         Sos.(solve ~options Purefeas [init; coeff; sigma1; sigma2; sigma3]) in
       ret = Osdp.SdpRet.Success
       && (let coeff = Sos.value coeff vals in
           Sos.Poly.Coeff.(compare coeff zero) > 0)) in
  Format.printf "check_init: %B@." check_init;
  Format.printf "time check_init: %.2fs@." t_check_init;
  let coeff = Sos.make "c" in
  let sigma = Sos.make ~n:3 ~d:4 "s" in
  let sigma0 = Sos.make ~n:3 ~d:6 "s0" in
  let check_ind0, t_check_ind0 =
    Osdp.Utils.profile
      (fun () ->
       let ind0 = Sos.(coeff * compose !!p t0 - sigma * !!p - sigma0 * g0) in
       let ret, _, vals, _ =
         Sos.(solve ~options Purefeas [ind0; coeff; sigma; sigma0]) in
       ret = Osdp.SdpRet.Success
       && (let coeff = Sos.value coeff vals in
           Sos.Poly.Coeff.(compare coeff zero) > 0)) in
  Format.printf "check_ind0: %B@." check_ind0;
  Format.printf "time check_ind0: %.2fs@." t_check_ind0;
  let coeff = Sos.make "c" in
  let sigma = Sos.make ~n:3 ~d:4 "s" in
  let sigma1 = Sos.make ~n:3 ~d:6 "s1" in
  let check_ind1, t_check_ind1 =
    Osdp.Utils.profile
      (fun () ->
       let ind1 = Sos.(coeff * compose !!p t1 - sigma * !!p - sigma1 * g1) in
       let ret, _, vals, _ =
         Sos.(solve ~options Purefeas [ind1; coeff; sigma; sigma1]) in
       ret = Osdp.SdpRet.Success
       && (let coeff = Sos.value coeff vals in
           Sos.Poly.Coeff.(compare coeff zero) > 0)) in
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
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p)
