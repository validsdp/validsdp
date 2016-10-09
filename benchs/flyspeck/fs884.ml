(* This one fails *)

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

let p = Sos.(-(  x1
  * (x1 * x4 * ((- x1) + x2 + x3 - x4 + x5 + x6)
     + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)
       + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) - x2 * x3 * x4
         - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6)
  * (4/1)
  + ((- x2) * x3 - x1 * x4
     + x2 * x5 + x3 * x6 - x5 * x6 + x1 * ((- x1) + x2 + x3 - x4 + x5 + x6))
    * ((- x2) * x3 - x1 * x4
       + x2 * x5 + x3 * x6 - x5 * x6 + x1 * ((- x1) + x2 + x3 - x4 + x5 + x6))
    * (- 245468/1000000)))
                    
let p' = Sos.(-302/10
     + (x1 * x4 * ((- x1) + x2 + x3 - x4 + x5 + x6)
        + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)
          + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) - x2 * x3 * x4
            - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6))
                    
(* bound on x1 : x1 \in [4, 6.3504] *)
let b1 = Sos.((x1 - 4 / 1) * (63504 / 10000 - x1))
(* bound on x2 : x2 \in [6.3504, 6.3504] *)
let b2 = Sos.((x2 - 63504 / 10000) * (63504 / 10000 - x2))
(* bound on x3 : x3 \in [4, 6.3504] *)
let b3 = Sos.((x3 - 4 / 1) * (63504 / 10000 - x3))
(* bound on x4 : x4 \in [4, 4] *)
let b4 = Sos.((x4 - 4 / 1) * (4 / 1 - x4))
(* bound on x5 : x5 \in [9.0601, 10.4976] *)
let b5 = Sos.((x5 - 90601 / 10000) * (104976 / 10000 - x5))
(* bound on x6 : x6 \in [4, 6.3504] *)
let b6 = Sos.((x6 - 4 / 1) * (63504 / 10000 - x6))

(* prove that p > 0 \/ p' > 0 on the above defined box *)
let check_p_pos =
  Format.printf "@[<v>@[<v 2>Let p (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@." Sos.pp p;
  Format.printf "@[<v>@[<v 2>Let b1 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@." Sos.pp b1;
  Format.printf "@[<v>@[<v 2>Let b2 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@." Sos.pp b2;
  Format.printf "@[<v>@[<v 2>Let b3 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@." Sos.pp b3;
  Format.printf "@[<v>@[<v 2>Let b4 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@." Sos.pp b4;
  Format.printf "@[<v>@[<v 2>Let b5 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@." Sos.pp b5;
  Format.printf "@[<v>@[<v 2>Let b6 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@." Sos.pp b6;
  let deg = Sos.degree p in
  let rup n = (n + 1) / 2 * 2 in
  let sigma, _ = Sos.var_poly "s1" 6 0 in 
  let sigma', _ = Sos.var_poly "s1" 6 0 in 
  let sigma1, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma2, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma3, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma4, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma5, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma6, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let e = Sos.(sigma * p + sigma' * p' - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4 - sigma5 * b5 - sigma6 * b6) in
  let ret, _, vals, _ =
    Sos.solve ~options Sos.Purefeas [e; sigma; sigma'; sigma1; sigma2; sigma3; sigma4; sigma5; sigma6] in
  let sigma = Sos.value_poly sigma vals in
  Format.printf "@[<v>@[<v 2>Let sigma (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma;
  let sigma' = Sos.value_poly sigma' vals in
  Format.printf "@[<v>@[<v 2>Let sigma' (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma';
  let sigma1 = Sos.value_poly sigma1 vals in
  Format.printf "@[<v>@[<v 2>Let sigma1 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma1;
  let sigma2 = Sos.value_poly sigma2 vals in
  Format.printf "@[<v>@[<v 2>Let sigma2 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma2;
  let sigma3 = Sos.value_poly sigma3 vals in
  Format.printf "@[<v>@[<v 2>Let sigma3 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma3;
  let sigma4 = Sos.value_poly sigma4 vals in
  Format.printf "@[<v>@[<v 2>Let sigma4 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma4;
  let sigma5 = Sos.value_poly sigma5 vals in
  Format.printf "@[<v>@[<v 2>Let sigma5 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma5;
  let sigma6 = Sos.value_poly sigma6 vals in
  Format.printf "@[<v>@[<v 2>Let sigma6 (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma6;
  ret = Osdp.SdpRet.Success

let _ =
  Format.printf "Bounds proved: %B@." check_p_pos
