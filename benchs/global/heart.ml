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
let ub = Sos.(1369 / 1000)
            
(* chack that invariant lb <= p(x) <= ub when x satisfies bounds *)
let check_bounds polys =
  let check_lb =
    let sigma = List.assoc "lb_sigma" polys in
    let sigma1 = List.assoc "lb_sigma1" polys in
    let sigma2 = List.assoc "lb_sigma2" polys in
    let sigma3 = List.assoc "lb_sigma3" polys in
    let sigma4 = List.assoc "lb_sigma4" polys in
    let sigma5 = List.assoc "lb_sigma5" polys in
    let sigma6 = List.assoc "lb_sigma6" polys in
    let sigma7 = List.assoc "lb_sigma7" polys in
    let sigma8 = List.assoc "lb_sigma8" polys in
    let e = Sos.(!!sigma * (p - lb) - !!sigma1 * b1 - !!sigma2 * b2 - !!sigma3 * b3 - !!sigma4 * b4 - !!sigma5 * b5 - !!sigma6 * b6 - !!sigma7 * b7 - !!sigma8 * b8) in
    let ret, _, _, _ =
      Sos.(solve ~options Purefeas [e; !!sigma; !!sigma1; !!sigma2; !!sigma3; !!sigma4; !!sigma5; !!sigma6; !!sigma7; !!sigma8]) in
    ret = Osdp.SdpRet.Success in
  let check_ub =
    let sigma = List.assoc "ub_sigma" polys in
    let sigma1 = List.assoc "ub_sigma1" polys in
    let sigma2 = List.assoc "ub_sigma2" polys in
    let sigma3 = List.assoc "ub_sigma3" polys in
    let sigma4 = List.assoc "ub_sigma4" polys in
    let sigma5 = List.assoc "ub_sigma5" polys in
    let sigma6 = List.assoc "ub_sigma6" polys in
    let sigma7 = List.assoc "ub_sigma7" polys in
    let sigma8 = List.assoc "ub_sigma8" polys in
    let e = Sos.(!!sigma * (ub - p) - !!sigma1 * b1 - !!sigma2 * b2 - !!sigma3 * b3 - !!sigma4 * b4 - !!sigma5 * b5 - !!sigma6 * b6 - !!sigma7 * b7 - !!sigma8 * b8) in
    let ret, _, _, _ =
      Sos.(solve ~options Purefeas [e; !!sigma; !!sigma1; !!sigma2; !!sigma3; !!sigma4; !!sigma5; !!sigma6; !!sigma7; !!sigma8]) in
    ret = Osdp.SdpRet.Success in
  check_lb && check_ub

let _ =
  let polys = Parse.file "heart.v" in
  Format.printf "Bounds proved: %B@." (check_bounds polys)
