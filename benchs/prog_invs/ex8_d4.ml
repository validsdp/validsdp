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
 * % ./ex8_d4 *)

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
    P.("360137561854871"/"1125899906842624" + "-4648532753362095"/"1152921504606846976" * 
        x0**2 + "-522343598561959"/"576460752303423488" * x0 * x1 + "-7354102629772791"/"2305843009213693952" * 
        x1**2 + "5916113786527169"/"576460752303423488" * x0**3 + "-574397345683745"/"36028797018963968" * 
        x0**2 * x1 + "-1432498279428087"/"576460752303423488" * x0 * x1**2 + "4968500152983215"/"288230376151711744" * 
        x1**3 + "-8454232510940359"/"72057594037927936" * x0**4 + "8778941830946171"/"288230376151711744" * 
        x0**3 * x1 + "-3420954828653527"/"36028797018963968" * x0**2 * x1**2 + "-8812954633677685"/"144115188075855872" * 
        x0 * x1**3 + "-4295668762430125"/"72057594037927936" * x1**4) in
  let polys = Parse.file "ex8_d4.v" in
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p polys)
