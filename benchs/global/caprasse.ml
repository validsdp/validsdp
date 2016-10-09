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
let check_bounds polys =
  let check_lb =
    let sigma = List.assoc "lb_sigma" polys in
    let sigma1 = List.assoc "lb_sigma1" polys in
    let sigma2 = List.assoc "lb_sigma2" polys in
    let sigma3 = List.assoc "lb_sigma3" polys in
    let sigma4 = List.assoc "lb_sigma4" polys in
    let e = Sos.(!!sigma * (p - lb) - !!sigma1 * b1 - !!sigma2 * b2 - !!sigma3 * b3 - !!sigma4 * b4) in
    let ret, _, _, _ =
      Sos.(solve ~options Purefeas [e; !!sigma; !!sigma1; !!sigma2; !!sigma3; !!sigma4]) in
    ret = Osdp.SdpRet.Success in
  let check_ub =
    let sigma = List.assoc "ub_sigma" polys in
    let sigma1 = List.assoc "ub_sigma1" polys in
    let sigma2 = List.assoc "ub_sigma2" polys in
    let sigma3 = List.assoc "ub_sigma3" polys in
    let sigma4 = List.assoc "ub_sigma4" polys in
    let e = Sos.(!!sigma * (ub - p) - !!sigma1 * b1 - !!sigma2 * b2 - !!sigma3 * b3 - !!sigma4 * b4) in
    let ret, _, _, _ =
      Sos.(solve ~options Purefeas [e; !!sigma; !!sigma1; !!sigma2; !!sigma3; !!sigma4]) in
    ret = Osdp.SdpRet.Success in
  check_lb && check_ub

let _ =
  let polys = Parse.file "caprasse.v" in
  Format.printf "Bounds proved: %B@." (check_bounds polys)
