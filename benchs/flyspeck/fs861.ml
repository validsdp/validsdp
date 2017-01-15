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
(* bound on x5 : x5 \in [5.6644, 15.53] *)
let b5 = Sos.((x5 - 56644 / 10000) * (1553 / 100 - x5))
(* bound on x6 : x6 \in [5.6644, 15.53] *)
let b6 = Sos.((x6 - 56644 / 10000) * (1553 / 100 - x6))

(* prove that p > 0 on the above defined box *)
let check_p_pos =
  let sigma = Sos.make "s" in
  let sigma1 = Sos.make ~n:6 ~d:2 "s1" in
  let sigma2 = Sos.make ~n:6 ~d:2 "s2" in
  let sigma3 = Sos.make ~n:6 ~d:2 "s3" in
  let sigma4 = Sos.make ~n:6 ~d:2 "s4" in
  let sigma5 = Sos.make ~n:6 ~d:2 "s5" in
  let sigma6 = Sos.make ~n:6 ~d:2 "s6" in
  let e = Sos.(sigma * p - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4 - sigma5 * b5 - sigma6 * b6) in
  let ret, _, vals, _ =
    Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3; sigma4; sigma5; sigma6]) in
  ret = Osdp.SdpRet.Success &&
    (let sigma = Sos.value sigma vals in
     Sos.Poly.Coeff.(compare sigma zero) > 0)

let _ =
  Format.printf "Bounds proved: %B@." check_p_pos
