(* Attempt to prove that p >= 0 with p at the end of this file is an
 * inductive invariant, for the program
 *
x1 = rand(0.9, 1.1);
x2 = rand(0, 0.2);
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
 * % ./ex4_d4 *)

module Sos = struct
  include Osdp.Sos.Q
  let ( / ) n m = Q.of_int n /. Q.of_int m
end

let options = { Sos.default with
                Sos.verbose = 0(*3*);
                Sos.sdp =
                  { Osdp.Sdp.default with
                    Osdp.Sdp.solver = Osdp.Sdp.Sdpa } }

let x1, x2 = Sos.(??0, ??1)

(* initial condition 0.9 <= x1 <= 1.1 encoded as (x1 - 0.9)*(1.1 - x1) (>= 0) *)
let pI1 = Sos.((x1 - 9 / 10) * (11 / 10 - x1))
(* initial condition 0 <= x2 <= 0.2 *)
let pI2 = Sos.(x2 * (2 / 10 - x2))
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
let check_inv p =
  let coeff = Sos.make "c" in
  let sigma1 = Sos.make ~n:2 ~d:2 "s1" in
  let sigma2 = Sos.make ~n:2 ~d:2 "s2" in
  let check_init, t_check_init =
    Osdp.Utils.profile
      (fun () ->
       let init = Sos.(coeff * !!p - sigma1 * pI1 - sigma2 * pI2) in
       let ret, _, vals, _ =
         Sos.(solve ~options Purefeas [init; coeff; sigma1; sigma2]) in
       ret = Osdp.SdpRet.Success
       && (let coeff = Sos.value coeff vals in
           Sos.Poly.Coeff.(compare coeff zero) > 0)) in
  Format.printf "check_init: %B@." check_init;
  Format.printf "time check_init: %.2fs@." t_check_init;
  let coeff = Sos.make "c" in
  let sigma = Sos.make ~n:2 ~d:8 "s" in
  let sigma0 = Sos.make ~n:2 ~d:10 "s0" in
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
  let sigma = Sos.make ~n:2 ~d:8 "s" in
  let sigma1 = Sos.make ~n:2 ~d:10 "s1" in
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
    let x0, x1 = P.(??0, ??1) in
    P.("45341764775"/"2199023255552" + "2543726999988995"/"576460752303423488" * 
        x0 + "-1432997702740123"/"4611686018427387904" * x1 + "-6302578343467645"/"288230376151711744" * 
        x0**2 + "6245114857897609"/"1152921504606846976" * x0 * x1 + "-5391003868387453"/"576460752303423488" * 
        x1**2 + "6367724791712061"/"576460752303423488" * x0**3 + "-3595005646773247"/"288230376151711744" * 
        x0**2 * x1 + "3726914850232837"/"288230376151711744" * x0 * x1**2 + "7525758218067537"/"288230376151711744" * 
        x1**3 + "-5053053318909601"/"576460752303423488" * x0**4 + "-8679218943287311"/"9223372036854775808" * 
        x0**3 * x1 + "979459393320495"/"36028797018963968" * x0**2 * x1**2 + "2667063388576173"/"1152921504606846976" * 
        x0 * x1**3 + "-1416111155701539"/"36028797018963968" * x1**4) in
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p)
