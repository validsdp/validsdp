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

let p = Sos.((x1-x2)**2+(x2-1/1)**2+(x1-x3**2)**2+(x3-1/1)**2)
                    
(* bound on x1 : x1 \in [-10, 10] *)
let b1 = Sos.((x1 + 10 / 1) * (10 / 1 - x1))
(* bound on x2 : x2 \in [-10, 10] *)
let b2 = Sos.((x2 + 10 / 1) * (10 / 1 - x2))
(* bound on x3 : x3 \in [-10, 10] *)
let b3 = Sos.((x3 + 10 / 1) * (10 / 1 - x3))

let lb = Sos.(-1 / 10000)
            
(* chack that invariant lb <= p(x) <= ub when x satisfies bounds *)
let check_bounds polys =
  let check_lb =
    let sigma = List.assoc "lb_sigma" polys in
    let sigma1 = List.assoc "lb_sigma1" polys in
    let sigma2 = List.assoc "lb_sigma2" polys in
    let sigma3 = List.assoc "lb_sigma3" polys in
    let e = Sos.(!!sigma * (p - lb) - !!sigma1 * b1 - !!sigma2 * b2 - !!sigma3 * b3) in
    let ret, _, _, _ =
      Sos.(solve ~options Purefeas [e; !!sigma; !!sigma1; !!sigma2; !!sigma3]) in
    ret = Osdp.SdpRet.Success in
  check_lb

let _ =
  let polys = Parse.file "schwefel.v" in
  Format.printf "Bounds proved: %B@." (check_bounds polys)
