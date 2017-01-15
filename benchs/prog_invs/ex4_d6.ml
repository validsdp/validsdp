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
 * % ./ex4_d6 *)

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
  let sigma1 = Sos.make ~n:2 ~d:4 "s1" in
  let sigma2 = Sos.make ~n:2 ~d:4 "s2" in
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
  let sigma = Sos.make ~n:2 ~d:12 "s" in
  let sigma0 = Sos.make ~n:2 ~d:16 "s0" in
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
  let sigma = Sos.make ~n:2 ~d:12 "s" in
  let sigma1 = Sos.make ~n:2 ~d:16 "s1" in
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
    P.("11724193731320667"/"9007199254740992" + "5363509247042945"/"1152921504606846976" * 
        x0 + "6697439732049177"/"576460752303423488" * x1 + "-2538921022898767"/"1125899906842624" * 
        x0**2 + "-158622508368809"/"140737488355328" * x0 * x1 + "-2153763193131945"/"1125899906842624" * 
        x1**2 + "1261645552858613"/"562949953421312" * x0**3 + "6720054296628647"/"4503599627370496" * 
        x0**2 * x1 + "2787072307930385"/"2251799813685248" * x0 * x1**2 + "8841768526834515"/"18014398509481984" * 
        x1**3 + "-5548502078413043"/"4503599627370496" * x0**4 + "-6352973998063161"/"36028797018963968" * 
        x0**3 * x1 + "7355223013039007"/"2251799813685248" * x0**2 * x1**2 + "7116910381908169"/"4503599627370496" * 
        x0 * x1**3 + "-575281306133581"/"2251799813685248" * x1**4 + "368553632223861"/"2251799813685248" * 
        x0**5 + "-3554591502428539"/"9007199254740992" * x0**4 * x1 + "-1808382380122255"/"1125899906842624" * 
        x0**3 * x1**2 + "-2806808898838291"/"2251799813685248" * x0**2 * x1**3 + "-36108254505365"/"9007199254740992" * 
        x0 * x1**4 + "843150192031495"/"1125899906842624" * x1**5 + "-8782095016692183"/"1152921504606846976" * 
        x0**6 + "6544640190593663"/"288230376151711744" * x0**5 * x1 + "3334276451595169"/"144115188075855872" * 
        x0**4 * x1**2 + "-4918224622344679"/"36028797018963968" * x0**3 * x1**3 + "-4677603389160537"/"9007199254740992" * 
        x0**2 * x1**4 + "-1667155699402415"/"2251799813685248" * x0 * x1**5 + "-4984497334918313"/"9007199254740992" * 
        x1**6) in
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p)
