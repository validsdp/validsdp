module Sos = struct
  include Osdp.Sos.Q
  let ( / ) n m = Q.of_int n /. Q.of_int m
end

let options = { Sos.default with
                Sos.verbose = 0(*3*);
                Sos.sdp =
                  { Osdp.Sdp.default with
                    Osdp.Sdp.solver = Osdp.Sdp.Sdpa } }

let x1, x2, x3, x4, x5, x6, x7, x8 = Sos.(??0, ??1, ??2, ??3, ??4, ??5, ??6, ??7)

let p = Sos.(-x1*x6**3+3/1*x1*x6*x7**2-x3*x7**3+3/1*x3*x7*x6**2-x2*x5**3+3/1*x2*x5*x8**2-x4*x8**3+3/1*x4*x8*x5**2-9563453/10000000)
                    
(* bound on x1 : x1 \in [-0.1, 0.4] *)
let b1 = Sos.((x1 + 1 / 10) * (4 / 10 - x1))
(* bound on x2 : x2 \in [0.4, 1] *)
let b2 = Sos.((x2 - 4 / 10) * (1 / 1 - x2))
(* bound on x3 : x3 \in [-0.7, -0.4] *)
let b3 = Sos.((x3 + 7 / 10) * (-4 / 10 - x3))
(* bound on x4 : x4 \in [-0.7, 0.4] *)
let b4 = Sos.((x4 + 7 / 10) * (4 / 10 - x4))
(* bound on x5 : x5 \in [0.1, 0.2] *)
let b5 = Sos.((x5 - 1 / 10) * (2 / 10 - x5))
(* bound on x6 : x6 \in [-0.1, 0.2] *)
let b6 = Sos.((x6 + 1 / 10) * (2 / 10 - x6))
(* bound on x7 : x7 \in [-0.3, 1.1] *)
let b7 = Sos.((x7 + 3 / 10) * (11 / 10 - x7))
(* bound on x8 : x8 \in [-1.1, -0.3] *)
let b8 = Sos.((x8 + 11 / 10) * (-3 / 10 - x8))

let lb = Sos.(-1744 / 1000)
            
(* chack that invariant lb <= p(x) <= ub when x satisfies bounds *)
let check_bounds =
  let sigma = Sos.make "s" in
  let sigma1 = Sos.make ~n:8 ~d:2 "s1" in
  let sigma2 = Sos.make ~n:8 ~d:2 "s2" in
  let sigma3 = Sos.make ~n:8 ~d:2 "s3" in
  let sigma4 = Sos.make ~n:8 ~d:2 "s4" in
  let sigma5 = Sos.make ~n:8 ~d:2 "s5" in
  let sigma6 = Sos.make ~n:8 ~d:2 "s6" in
  let sigma7 = Sos.make ~n:8 ~d:2 "s7" in
  let sigma8 = Sos.make ~n:8 ~d:2 "s8" in
  let e = Sos.(sigma * (p - lb) - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4 - sigma5 * b5 - sigma6 * b6 - sigma7 * b7 - sigma8 * b8) in
  let ret, _, vals, _ =
      Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3; sigma4; sigma5; sigma6; sigma7; sigma8]) in
  ret = Osdp.SdpRet.Success &&
    (let sigma = Sos.value sigma vals in
     Sos.Poly.Coeff.(compare sigma zero) > 0)

let _ =
  Format.printf "Bounds proved: %B@." check_bounds
