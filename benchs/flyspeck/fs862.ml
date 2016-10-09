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

let p = Sos.((- 4/1)
  * (x4 * x4 * x1
     + 8/1 * (x5 - x6) * (x2 - x3)
       - x4 * (16/1 * x1 + (x5 - 8/1) * x2 + (x6 - 8/1) * x3)))
                    
(* bound on x1 : x1 \in [1, 1.17547965573] *)
let b1 = Sos.((x1 - 1 / 1) * (117547965573 / 100000000000 - x1))
(* bound on x2 : x2 \in [1, 1.17547965573] *)
let b2 = Sos.((x2 - 1 / 1) * (117547965573 / 100000000000 - x2))
(* bound on x3 : x3 \in [1, 1.17547965573] *)
let b3 = Sos.((x3 - 1 / 1) * (117547965573 / 100000000000 - x3))
(* bound on x4 : x4 \in [2.51952632905, 9.0601] *)
let b4 = Sos.((x4 - 251952632905 / 100000000000) * (90601 / 10000 - x4))
(* bound on x5 : x5 \in [4, 6.3504] *)
let b5 = Sos.((x5 - 4 / 1) * (63504 / 10000 - x5))
(* bound on x6 : x6 \in [6.25, 15.53] *)
let b6 = Sos.((x6 - 625 / 100) * (1553 / 100 - x6))

(* prove that p > 0 on the above defined box *)
let check_p_pos polys =
  let sigma = List.assoc "sigma" polys in
  let sigma1 = List.assoc "sigma1" polys in
  let sigma2 = List.assoc "sigma2" polys in
  let sigma3 = List.assoc "sigma3" polys in
  let sigma4 = List.assoc "sigma4" polys in
  let sigma5 = List.assoc "sigma5" polys in
  let sigma6 = List.assoc "sigma6" polys in
  let e = Sos.(!!sigma * p - !!sigma1 * b1 - !!sigma2 * b2 - !!sigma3 * b3 - !!sigma4 * b4 - !!sigma5 * b5 - !!sigma6 * b6) in
  let ret, _, vals, _ =
    Sos.(solve ~options Purefeas [e; !!sigma; !!sigma1; !!sigma2; !!sigma3; !!sigma4; !!sigma5; !!sigma6]) in
  ret = Osdp.SdpRet.Success

let _ =
  let polys = Parse.file "fs862.v" in
  Format.printf "Bounds proved: %B@." (check_p_pos polys)
