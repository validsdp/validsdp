module Sos = struct
  include Osdp.Sos.Q
  let ( / ) n m = Q.of_int n /. Q.of_int m
end

let options = { Sos.default with
                Sos.verbose = 0(*3*);
                Sos.sdp =
                  { Osdp.Sdp.default with
                    Osdp.Sdp.solver = Osdp.Sdp.Sdpa } }

let x1, x2, x3, x4, x5, x6, x7 = Sos.(??0, ??1, ??2, ??3, ??4, ??5, ??6)

let p = Sos.(x1**2+2/1*x2**2+2/1*x3**2+2/1*x4**2+2/1*x5**2+2/1*x6**2+2/1*x7**2-x1)
                    
(* bound on x1 : x1 \in [-1, 1] *)
let b1 = Sos.((x1 + 1 / 1) * (1 / 1 - x1))
(* bound on x2 : x2 \in [-1, 1] *)
let b2 = Sos.((x2 + 1 / 1) * (1 / 1 - x2))
(* bound on x3 : x3 \in [-1, 1] *)
let b3 = Sos.((x3 + 1 / 1) * (1 / 1 - x3))
(* bound on x4 : x4 \in [-1, 1] *)
let b4 = Sos.((x4 + 1 / 1) * (1 / 1 - x4))
(* bound on x5 : x5 \in [-1, 1] *)
let b5 = Sos.((x5 + 1 / 1) * (1 / 1 - x5))
(* bound on x6 : x6 \in [-1, 1] *)
let b6 = Sos.((x6 + 1 / 1) * (1 / 1 - x6))
(* bound on x7 : x7 \in [-1, 1] *)
let b7 = Sos.((x7 + 1 / 1) * (1 / 1 - x7))

let lb = Sos.(-2501 / 10000)
            
let ub = Sos.(140001 / 10000)
            
(* chack that invariant lb <= p(x) <= ub when x satisfies bounds *)
let check_bounds =
  let check_lb =
    let sigma = Sos.make "s" in
    let sigma1 = Sos.make "s1" in
    let sigma2 = Sos.make "s2" in
    let sigma3 = Sos.make "s3" in
    let sigma4 = Sos.make "s4" in
    let sigma5 = Sos.make "s5" in
    let sigma6 = Sos.make "s6" in
    let sigma7 = Sos.make "s7" in
    let e = Sos.(sigma * (p - lb) - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4 - sigma5 * b5 - sigma6 * b6 - sigma7 * b7) in
    let ret, _, vals, _ =
      Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3; sigma4; sigma5; sigma6; sigma7]) in
    ret = Osdp.SdpRet.Success &&
      (let sigma = Sos.value sigma vals in
       Sos.Poly.Coeff.(compare sigma zero) > 0) in
  let check_ub =
    let sigma = Sos.make "s" in
    let sigma1 = Sos.make "s1" in
    let sigma2 = Sos.make "s2" in
    let sigma3 = Sos.make "s3" in
    let sigma4 = Sos.make "s4" in
    let sigma5 = Sos.make "s5" in
    let sigma6 = Sos.make "s6" in
    let sigma7 = Sos.make "s7" in
    let e = Sos.(sigma * (ub - p) - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4 - sigma5 * b5 - sigma6 * b6 - sigma7 * b7) in
    let ret, _, vals, _ =
      Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3; sigma4; sigma5; sigma6; sigma7]) in
    ret = Osdp.SdpRet.Success &&
      (let sigma = Sos.value sigma vals in
       Sos.Poly.Coeff.(compare sigma zero) > 0) in
  check_lb && check_ub
  
let _ =
  Format.printf "Bounds proved: %B@." check_bounds
