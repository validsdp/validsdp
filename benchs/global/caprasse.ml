module Sos = struct
  include Osdp.Sos.Q
  let ( / ) n m = Q.of_int n /. Q.of_int m
end

let options = { Sos.default with
                Sos.verbose = 0(*3*);
                Sos.sdp =
                  { Osdp.Sdp.default with
                    Osdp.Sdp.solver = Osdp.Sdp.Sdpa } }

let x1, x2, x3, x4 = Sos.(??0, ??1, ??2, ??3)

let p = Sos.(-x1*x3**3+4/1*x2*x3**2*x4+4/1*x1*x3*x4**2+2/1*x2*x4**3+4/1*x1*x3+4/1*x3**2-10/1*x2*x4-10/1*x4**2+2/1)
                    
(* bound on x1 : x1 \in [-0.5, 0.5] *)
let b1 = Sos.((x1 + 1 / 2) * (1 / 2 - x1))
(* bound on x2 : x2 \in [-0.5, 0.5] *)
let b2 = Sos.((x2 + 1 / 2) * (1 / 2 - x2))
(* bound on x3 : x3 \in [-0.5, 0.5] *)
let b3 = Sos.((x3 + 1 / 2) * (1 / 2 - x3))
(* bound on x4 : x4 \in [-0.5, 0.5] *)
let b4 = Sos.((x4 + 1 / 2) * (1 / 2 - x4))

let lb = Sos.(-3181 / 1000)
            
let ub = Sos.(4486 / 1000)
            
(* chack that invariant lb <= p(x) <= ub when x satisfies bounds *)
let check_bounds =
  let check_lb =
    let sigma = Sos.make "s" in
    let sigma1 = Sos.make ~n:4 ~d:2 "s1" in
    let sigma2 = Sos.make ~n:4 ~d:2 "s2" in
    let sigma3 = Sos.make ~n:4 ~d:2 "s3" in
    let sigma4 = Sos.make ~n:4 ~d:2 "s4" in
    let e = Sos.(sigma * (p - lb) - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4) in
    let ret, _, vals, _ =
      Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3; sigma4]) in
    ret = Osdp.SdpRet.Success &&
      (let sigma = Sos.value sigma vals in
       Sos.Poly.Coeff.(compare sigma zero) > 0) in
  let check_ub =
    let sigma = Sos.make "s" in
    let sigma1 = Sos.make ~n:4 ~d:2 "s1" in
    let sigma2 = Sos.make ~n:4 ~d:2 "s2" in
    let sigma3 = Sos.make ~n:4 ~d:2 "s3" in
    let sigma4 = Sos.make ~n:4 ~d:2 "s4" in
    let e = Sos.(sigma * (ub - p) - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4) in
    let ret, _, vals, _ =
      Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3; sigma4]) in
    ret = Osdp.SdpRet.Success &&
      (let sigma = Sos.value sigma vals in
       Sos.Poly.Coeff.(compare sigma zero) > 0) in
  check_lb && check_ub
  
let _ =
  Format.printf "Bounds proved: %B@." check_bounds
