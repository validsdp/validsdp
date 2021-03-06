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
 * % ./ex4_d8 *)

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
  let sigma1 = Sos.make ~n:2 ~d:6 "s1" in
  let sigma2 = Sos.make ~n:2 ~d:6 "s2" in
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
  let sigma = Sos.make ~n:2 ~d:16 "s" in
  let sigma0 = Sos.make ~n:2 ~d:22 "s0" in
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
  let sigma = Sos.make ~n:2 ~d:16 "s" in
  let sigma1 = Sos.make ~n:2 ~d:22 "s1" in
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
    let x1, x2 = P.(??0, ??1) in
    P.("161665552462085691"/"72057594037927936" + "5894209604283881"/"576460752303423488" * 
        x1 + "4026839744894797"/"1152921504606846976" * x2 + "-570763263822683"/"70368744177664" * 
        x1**2 + "-3276759790410289"/"562949953421312" * x1 * x2 + "-8583394086252111"/"1125899906842624" * 
        x2**2 + "6371928205597611"/"562949953421312" * x1**3 + "2990885910233667"/"281474976710656" * 
        x1**2 * x2 + "1643973001149963"/"140737488355328" * x1 * x2**2 + "1542089506080425"/"281474976710656" * 
        x2**3 + "-4799251149104555"/"562949953421312" * x1**4 + "-5658382378280923"/"1125899906842624" * 
        x1**3 * x2 + "7749818766026805"/"2251799813685248" * x1**2 * x2**2 + "1281182822772917"/"2251799813685248" * 
        x1 * x2**3 + "96115315873591"/"17592186044416" * x2**4 + "6194375225294295"/"1125899906842624" * 
        x1**5 + "216753755181017"/"70368744177664" * x1**4 * x2 + "-420813637474157"/"35184372088832" * 
        x1**3 * x2**2 + "-7884809520285811"/"562949953421312" * x1**2 * x2**3 + "-3590702668670401"/"281474976710656" * 
        x1 * x2**4 + "-2607751962589009"/"562949953421312" * x2**5 + "-1386973484500641"/"562949953421312" * 
        x1**6 + "-4760860470479713"/"2251799813685248" * x1**5 * x2 + "7441625272809979"/"1125899906842624" * 
        x1**4 * x2**2 + "1414455816956327"/"140737488355328" * x1**3 * x2**3 + "6326806100507715"/"1125899906842624" * 
        x1**2 * x2**4 + "5242312748125127"/"4503599627370496" * x1 * x2**5 + "-6753693085396311"/"2251799813685248" * 
        x2**6 + "2310408309450379"/"9007199254740992" * x1**7 + "-1282633630135753"/"4503599627370496" * 
        x1**6 * x2 + "-3873229099985911"/"2251799813685248" * x1**5 * x2**2 + "-5645906880002219"/"2251799813685248" * 
        x1**4 * x2**3 + "-6242468220524711"/"2251799813685248" * x1**3 * x2**4 + "5687521358113993"/"2251799813685248" * 
        x1**2 * x2**5 + "1674758640227347"/"140737488355328" * x1 * x2**6 + "6291148553230949"/"1125899906842624" * 
        x2**7 + "-5252213773793345"/"576460752303423488" * x1**8 + "7348633685485539"/"288230376151711744" * 
        x1**7 * x2 + "-2047870194208245"/"144115188075855872" * x1**6 * x2**2 + "-2879854488063785"/"9007199254740992" * 
        x1**5 * x2**3 + "-5649078646047861"/"36028797018963968" * x1**4 * x2**4 + "1694311663061067"/"1125899906842624" * 
        x1**3 * x2**5 + "-6411409407138369"/"72057594037927936" * x1**2 * x2**6 + "-1516261991165219"/"281474976710656" * 
        x1 * x2**7 + "-2878544359045033"/"562949953421312" * x2**8) in
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p)
