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
 * % ./ex7_d10 *)

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
  let sigma1 = Sos.make ~n:2 ~d:8 "s1" in
  let sigma2 = Sos.make ~n:2 ~d:8 "s2" in
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
  let sigma = Sos.make ~n:2 ~d:20 "s" in
  let sigma0 = Sos.make ~n:2 ~d:28 "s0" in
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
  let sigma = Sos.make ~n:2 ~d:20 "s" in
  let sigma1 = Sos.make ~n:2 ~d:28 "s1" in
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
    P.("6663396779481634255"/"4611686018427387904" + "958453180783139"/"144115188075855872" * 
        x0 + "5002734848710397"/"2305843009213693952" * x1 + "-3714704700823963"/"140737488355328" * 
        x0**2 + "2760004052733555"/"281474976710656" * x0 * x1 + "-6219994100723803"/"562949953421312" * 
        x1**2 + "1569339114838169"/"17592186044416" * x0**3 + "-4269534020587661"/"70368744177664" * 
        x0**2 * x1 + "6829824526785077"/"281474976710656" * x0 * x1**2 + "-2090572470872219"/"562949953421312" * 
        x1**3 + "-5240849430967025"/"35184372088832" * x0**4 + "4153632242573579"/"35184372088832" * 
        x0**3 * x1 + "2757276872629607"/"35184372088832" * x0**2 * x1**2 + "-7828849473439869"/"2251799813685248" * 
        x0 * x1**3 + "-5440502054742119"/"281474976710656" * x1**4 + "2825111038977275"/"17592186044416" * 
        x0**5 + "-7077061622146121"/"70368744177664" * x0**4 * x1 + "-320871210247287"/"1099511627776" * 
        x0**3 * x1**2 + "2505211680271333"/"70368744177664" * x0**2 * x1**3 + "7644698780461217"/"140737488355328" * 
        x0 * x1**4 + "3961973284694491"/"35184372088832" * x1**5 + "-7743524602047787"/"70368744177664" * 
        x0**6 + "2789815021291623"/"70368744177664" * x0**5 * x1 + "8231631222642615"/"35184372088832" * 
        x0**4 * x1**2 + "1283729025119609"/"70368744177664" * x0**3 * x1**3 + "1716838090644893"/"17592186044416" * 
        x0**2 * x1**4 + "-1404098008692995"/"4398046511104" * x0 * x1**5 + "-2515301591750811"/"17592186044416" * 
        x1**6 + "74292292859905"/"2199023255552" * x0**7 + "5104157155729075"/"2251799813685248" * 
        x0**6 * x1 + "5278666810801977"/"562949953421312" * x0**5 * x1**2 + "-5563947438451113"/"140737488355328" * 
        x0**4 * x1**3 + "-7782190535127559"/"35184372088832" * x0**3 * x1**4 + "2893207448482549"/"70368744177664" * 
        x0**2 * x1**5 + "8579641566377057"/"35184372088832" * x0 * x1**6 + "4825334523795795"/"35184372088832" * 
        x1**7 + "-688495911927937"/"140737488355328" * x0**8 + "-724795967809523"/"281474976710656" * 
        x0**7 * x1 + "-4953342636224053"/"281474976710656" * x0**6 * x1**2 + "-687875586301207"/"35184372088832" * 
        x0**5 * x1**3 + "198788696088903"/"4398046511104" * x0**4 * x1**4 + "8328856451085225"/"35184372088832" * 
        x0**3 * x1**5 + "-309591290713297"/"4398046511104" * x0**2 * x1**6 + "-5297638694235333"/"70368744177664" * 
        x0 * x1**7 + "-7345016667310557"/"70368744177664" * x1**8 + "4013336032663289"/"36028797018963968" * 
        x0**9 + "-5666891151461549"/"4503599627370496" * x0**8 * x1 + "-2816757793065755"/"1125899906842624" * 
        x0**7 * x1**2 + "-4788422774740657"/"562949953421312" * x0**6 * x1**3 + "-7812951548799969"/"281474976710656" * 
        x0**5 * x1**4 + "-8499368439981473"/"562949953421312" * x0**4 * x1**5 + "2247638969137519"/"35184372088832" * 
        x0**3 * x1**6 + "-2396914650796327"/"17592186044416" * x0**2 * x1**7 + "517007713739487"/"4398046511104" * 
        x0 * x1**8 + "3167988434663279"/"70368744177664" * x1**9 + "-371582216163627"/"144115188075855872" * 
        x0**10 + "8671781478507543"/"1152921504606846976" * x0**9 * x1 + "-7238028155121355"/"72057594037927936" * 
        x0**8 * x1**2 + "-7384186774266561"/"144115188075855872" * x0**7 * x1**3 + "-3039147230713629"/"4503599627370496" * 
        x0**6 * x1**4 + "-1243882748396279"/"281474976710656" * x0**5 * x1**5 + "-7897799494157741"/"18014398509481984" * 
        x0**4 * x1**6 + "7921901963465403"/"2251799813685248" * x0**3 * x1**7 + "-1600656723919683"/"35184372088832" * 
        x0**2 * x1**8 + "5034259702369825"/"562949953421312" * x0 * x1**9 + "-131392341649221"/"4398046511104" * 
        x1**10) in
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p)
