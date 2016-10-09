module Sos = struct
  include Osdp.Sos.Q
  let ( / ) n m = Q.of_int n /. Q.of_int m
end

let options = { Sos.default with
                Sos.verbose = 0(*3*);
                Sos.sdp =
                  { Osdp.Sdp.default with
                    Osdp.Sdp.solver = Osdp.Sdp.Sdpa } }

let x1, x2, x3, x4, x5, x6 = Sos.(??0, ??1, ??2, ??3, ??4, ??5)

let p = Sos.(x6*x2**2+x5*x3**2-x1*x4**2+x4**3+x4**2-1/3*x1+4/3*x4)
                    
(* bound on x1 : x1 \in [-1, 0] *)
let b1 = Sos.((x1 + 1 / 1) * (0 / 1 - x1))
(* bound on x2 : x2 \in [-0.1, 0.9] *)
let b2 = Sos.((x2 + 1 / 10) * (9 / 10 - x2))
(* bound on x3 : x3 \in [-0.1, 0.5] *)
let b3 = Sos.((x3 + 1 / 10) * (5 / 10 - x3))
(* bound on x4 : x4 \in [-1, -0.1] *)
let b4 = Sos.((x4 + 1 / 1) * (-1 / 10 - x4))
(* bound on x5 : x5 \in [-0.1, -0.05] *)
let b5 = Sos.((x5 + 1 / 10) * (-5 / 100 - x5))
(* bound on x6 : x6 \in [-0.1, -0.03] *)
let b6 = Sos.((x6 + 1 / 10) * (-3 / 100 - x6))

let lb = Sos.(-14394 / 10000)
let ub = Sos.(2191 / 10000)
            
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
    let e = Sos.(!!sigma * (p - lb) - !!sigma1 * b1 - !!sigma2 * b2 - !!sigma3 * b3 - !!sigma4 * b4 - !!sigma5 * b5 - !!sigma6 * b6) in
    let ret, _, _, _ =
      Sos.(solve ~options Purefeas [e; !!sigma; !!sigma1; !!sigma2; !!sigma3; !!sigma4; !!sigma5; !!sigma6]) in
    ret = Osdp.SdpRet.Success in
  let check_ub =
    let sigma = List.assoc "ub_sigma" polys in
    let sigma1 = List.assoc "ub_sigma1" polys in
    let sigma2 = List.assoc "ub_sigma2" polys in
    let sigma3 = List.assoc "ub_sigma3" polys in
    let sigma4 = List.assoc "ub_sigma4" polys in
    let sigma5 = List.assoc "ub_sigma5" polys in
    let sigma6 = List.assoc "ub_sigma6" polys in
    let e = Sos.(!!sigma * (ub - p) - !!sigma1 * b1 - !!sigma2 * b2 - !!sigma3 * b3 - !!sigma4 * b4 - !!sigma5 * b5 - !!sigma6 * b6) in
    let ret, _, _, _ =
      Sos.(solve ~options Purefeas [e; !!sigma; !!sigma1; !!sigma2; !!sigma3; !!sigma4; !!sigma5; !!sigma6]) in
    ret = Osdp.SdpRet.Success in
  check_lb && check_ub

let _ =
  let polys = Parse.file "butcher.v" in
  Format.printf "Bounds proved: %B@." (check_bounds polys)
