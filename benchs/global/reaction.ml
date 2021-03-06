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

let p = Sos.(-x1 + 2 / 1 * x2 - x3 - 835634534 / 1000000000 * x2 * (1 / 1 + x2))
                    
(* bound on x1 : x1 \in [-5, 5] *)
let b1 = Sos.((x1 + 5 / 1) * (5 / 1 - x1))
(* bound on x2 : x2 \in [-5, 5] *)
let b2 = Sos.((x2 + 5 / 1) * (5 / 1 - x2))
(* bound on x3 : x3 \in [-5, 5] *)
let b3 = Sos.((x3 + 5 / 1) * (5 / 1 - x3))

let lb = Sos.(-36713 / 1000)
            
let ub = Sos.(10439 / 1000)
            
(* chack that invariant lb <= p(x) <= ub when x satisfies bounds *)
let check_bounds =
  let check_lb =
    let sigma = Sos.make "s" in
    let sigma1 = Sos.make "s1" in
    let sigma2 = Sos.make "s2" in
    let sigma3 = Sos.make "s3" in
    let e = Sos.(sigma * (p - lb) - sigma1 * b1 - sigma2 * b2 - sigma3 * b3) in
    let ret, _, vals, _ =
      Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3]) in
    ret = Osdp.SdpRet.Success &&
      (let sigma = Sos.value sigma vals in
       Sos.Poly.Coeff.(compare sigma zero) > 0) in
  let check_ub =
    let sigma = Sos.make "s" in
    let sigma1 = Sos.make "s1" in
    let sigma2 = Sos.make "s2" in
    let sigma3 = Sos.make "s3" in
    let e = Sos.(sigma * (p - lb) - sigma1 * b1 - sigma2 * b2 - sigma3 * b3) in
    let ret, _, vals, _ =
      Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3]) in
    ret = Osdp.SdpRet.Success &&
      (let sigma = Sos.value sigma vals in
       Sos.Poly.Coeff.(compare sigma zero) > 0) in
  check_lb && check_ub
  
let _ =
  Format.printf "Bounds proved: %B@." check_bounds
