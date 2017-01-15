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
 * % ./ex7_d8 *)

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
    let x0, x1 = P.(??0, ??1) in
    P.("422466560484490895"/"288230376151711744" + "6926984831030345"/"2305843009213693952" * 
        x0 + "-8529584755092047"/"2305843009213693952" * x1 + "-2012343878195585"/"1125899906842624" * 
        x0**2 + "-3521458502666927"/"2251799813685248" * x0 * x1 + "-1570337351860585"/"140737488355328" * 
        x1**2 + "8511192731411189"/"4503599627370496" * x0**3 + "5113816193877479"/"4503599627370496" * 
        x0**2 * x1 + "650185879370577"/"70368744177664" * x0 * x1**2 + "3900427119031809"/"281474976710656" * 
        x1**3 + "-705642803542583"/"70368744177664" * x0**4 + "-358711900726861"/"140737488355328" * 
        x0**3 * x1 + "2673246439652531"/"281474976710656" * x0**2 * x1**2 + "-3532692190729867"/"281474976710656" * 
        x0 * x1**3 + "3392990004312683"/"2251799813685248" * x1**4 + "603298355885275"/"70368744177664" * 
        x0**5 + "7730999829343969"/"562949953421312" * x0**4 * x1 + "1490692954153793"/"281474976710656" * 
        x0**3 * x1**2 + "-2266979092525585"/"70368744177664" * x0**2 * x1**3 + "-6432817666875783"/"281474976710656" * 
        x0 * x1**4 + "757769917618545"/"70368744177664" * x1**5 + "-4842264840851431"/"1125899906842624" * 
        x0**6 + "-5602482603323659"/"562949953421312" * x0**5 * x1 + "2476014632279723"/"562949953421312" * 
        x0**4 * x1**2 + "2353074899048683"/"70368744177664" * x0**3 * x1**3 + "8191939289327783"/"562949953421312" * 
        x0**2 * x1**4 + "5594424204735809"/"562949953421312" * x0 * x1**5 + "-78983991683129"/"4398046511104" * 
        x1**6 + "4853899563812589"/"18014398509481984" * x0**7 + "-2015104324474291"/"9007199254740992" * 
        x0**6 * x1 + "-5718486054540663"/"4503599627370496" * x0**5 * x1**2 + "-6770688066175901"/"1125899906842624" * 
        x0**4 * x1**3 + "-7089322066933189"/"281474976710656" * x0**3 * x1**4 + "-6171643405031141"/"562949953421312" * 
        x0**2 * x1**5 + "6831720514398641"/"140737488355328" * x0 * x1**6 + "1486449442317321"/"281474976710656" * 
        x1**7 + "-3952833233238511"/"576460752303423488" * x0**8 + "5506656746008749"/"576460752303423488" * 
        x0**7 * x1 + "882267975180367"/"18014398509481984" * x0**6 * x1**2 + "7786242759023605"/"18014398509481984" * 
        x0**5 * x1**3 + "-7766321859279597"/"9007199254740992" * x0**4 * x1**4 + "-4787378206140887"/"1125899906842624" * 
        x0**3 * x1**5 + "1255574223617737"/"1125899906842624" * x0**2 * x1**6 + "-4719857941408859"/"2251799813685248" * 
        x0 * x1**7 + "-686650668144077"/"35184372088832" * x1**8) in
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p)
