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

let p = Sos.(- ((- x2) * x3 - x1 * x4
  + x2 * x5 + x3 * x6 - x5 * x6 + x1 * ((- x1) + x2 + x3 - x4 + x5 + x6)))
                    
(* bound on x1 : x1 \in [4, 6.3504] *)
let b1 = Sos.((x1 - 4 / 1) * (63504 / 10000 - x1))
(* bound on x2 : x2 \in [4, 4] *)
let b2 = Sos.((x2 - 4 / 1) * (4 / 1 - x2))
(* bound on x3 : x3 \in [4, 4] *)
let b3 = Sos.((x3 - 4 / 1) * (4 / 1 - x3))
(* bound on x4 : x4 \in [9.0601, 15.327225] *)
let b4 = Sos.((x4 - 90601 / 10000) * (15327225 / 1000000 - x4))
(* bound on x5 : x5 \in [4, 6.3504] *)
let b5 = Sos.((x5 - 4 / 1) * (63504 / 10000 - x5))
(* bound on x6 : x6 \in [4, 6.3504] *)
let b6 = Sos.((x6 - 4 / 1) * (63504 / 10000 - x6))

(* prove that p > 0 on the above defined box *)
let check_p_pos =
  let sigma = Sos.make "s" in
  let sigma1 = Sos.make "s1" in
  let sigma2 = Sos.make "s2" in
  let sigma3 = Sos.make "s3" in
  let sigma4 = Sos.make "s4" in
  let sigma5 = Sos.make "s5" in
  let sigma6 = Sos.make "s6" in
  let e = Sos.(sigma * p - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4 - sigma5 * b5 - sigma6 * b6) in
  let ret, _, vals, _ =
    Sos.(solve ~options Purefeas [e; sigma; sigma1; sigma2; sigma3; sigma4; sigma5; sigma6]) in
  ret = Osdp.SdpRet.Success &&
    (let sigma = Sos.value sigma vals in
     Sos.Poly.Coeff.(compare sigma zero) > 0)

let _ =
  Format.printf "Bounds proved: %B@." check_p_pos
