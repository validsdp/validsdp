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
 * % ./ex4_d10 *)

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
    P.("8987395123151517477"/"4611686018427387904" + "8893261590519765"/"9223372036854775808" * 
        x0 + "2764620085281493"/"4611686018427387904" * x1 + "-762995180902649"/"70368744177664" * 
        x0**2 + "1872606290655735"/"281474976710656" * x0 * x1 + "-2624126371847389"/"281474976710656" * 
        x1**2 + "7265916113715343"/"281474976710656" * x0**3 + "-7391592181846879"/"281474976710656" * 
        x0**2 * x1 + "2208568708068981"/"140737488355328" * x0 * x1**2 + "23762819918821"/"8796093022208" * 
        x1**3 + "-6511460237411829"/"140737488355328" * x0**4 + "8722260536783613"/"281474976710656" * 
        x0**3 * x1 + "4804234895405367"/"281474976710656" * x0**2 * x1**2 + "-8577714942801095"/"281474976710656" * 
        x0 * x1**3 + "-5265023639870085"/"2251799813685248" * x1**4 + "8102840114726881"/"140737488355328" * 
        x0**5 + "-7403973278063863"/"562949953421312" * x0**4 * x1 + "-1234703206305595"/"17592186044416" * 
        x0**3 * x1**2 + "5320134228727747"/"70368744177664" * x0**2 * x1**3 + "2251144234924427"/"281474976710656" * 
        x0 * x1**4 + "5813201814936653"/"281474976710656" * x1**5 + "-3044489657079467"/"70368744177664" * 
        x0**6 + "-8317783909311011"/"1125899906842624" * x0**5 * x1 + "5751906116772821"/"70368744177664" * 
        x0**4 * x1**2 + "-3290472152757389"/"281474976710656" * x0**3 * x1**3 + "5668210288991619"/"281474976710656" * 
        x0**2 * x1**4 + "-4571093218279997"/"70368744177664" * x0 * x1**5 + "-2939560969780967"/"281474976710656" * 
        x1**6 + "683162528700147"/"35184372088832" * x0**7 + "1150448355036541"/"70368744177664" * 
        x0**6 * x1 + "-5072842624796853"/"140737488355328" * x0**5 * x1**2 + "-5994272696098785"/"140737488355328" * 
        x0**4 * x1**3 + "-5325320329714693"/"70368744177664" * x0**3 * x1**4 + "-5553916110642339"/"281474976710656" * 
        x0**2 * x1**5 + "4140701801908681"/"70368744177664" * x0 * x1**6 + "6220373918645045"/"281474976710656" * 
        x1**7 + "-2536972496138239"/"562949953421312" * x0**8 + "-413085040399817"/"70368744177664" * 
        x0**7 * x1 + "2711130044901239"/"562949953421312" * x0**6 * x1**2 + "1115216018322205"/"140737488355328" * 
        x0**5 * x1**3 + "1812191784642595"/"35184372088832" * x0**4 * x1**4 + "4863196379112075"/"70368744177664" * 
        x0**3 * x1**5 + "-4729070977106959"/"70368744177664" * x0**2 * x1**6 + "-4675542648877751"/"281474976710656" * 
        x0 * x1**7 + "-4451655391374831"/"140737488355328" * x1**8 + "2349038140855955"/"18014398509481984" * 
        x0**9 + "-5930234904541751"/"4503599627370496" * x0**8 * x1 + "-2729425669879505"/"1125899906842624" * 
        x0**7 * x1**2 + "1978892581265703"/"1125899906842624" * x0**6 * x1**3 + "-106656830813879"/"8796093022208" * 
        x0**5 * x1**4 + "-7964610133829439"/"562949953421312" * x0**4 * x1**5 + "8873781327449163"/"281474976710656" * 
        x0**3 * x1**6 + "-6346235944656559"/"18014398509481984" * x0**2 * x1**7 + "7159618615161045"/"140737488355328" * 
        x0 * x1**8 + "8067193080892351"/"1125899906842624" * x1**9 + "-699221736208067"/"288230376151711744" * 
        x0**10 + "2596308005981341"/"144115188075855872" * x0**9 * x1 + "-7086473226607205"/"72057594037927936" * 
        x0**8 * x1**2 + "-2532779168514511"/"36028797018963968" * x0**7 * x1**3 + "-499753870842093"/"4503599627370496" * 
        x0**6 * x1**4 + "-1829119921384613"/"562949953421312" * x0**5 * x1**5 + "8272286571466563"/"4503599627370496" * 
        x0**4 * x1**6 + "5116331882171435"/"562949953421312" * x0**3 * x1**7 + "-2780756571012153"/"140737488355328" * 
        x0**2 * x1**8 + "-6752570325684547"/"562949953421312" * x0 * x1**9 + "-5542696380597103"/"1125899906842624" * 
        x1**10) in
  Format.printf "Invariant p >= 0 proved: %B@." (check_inv p)
