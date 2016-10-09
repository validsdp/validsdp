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

let p = Sos.(2 / 25
  * ((- 2/1) * x4 * x4 * x4 * x4 * x4 * x1
     + 256/1
       * (x5 + (- 1/1) * x6) * (x5 + (- 1/1) * x6) * (x5 + (- 1/1) * x6)
         * (x2 + (- 1/1) * x3)
       + x4 * x4 * x4
         * (2/1 * ((- 256/1) + x5 * x5 + (- 2/1) * x5 * x6 + x6 * x6) * x1
            + (x5 * x5 * ((- 8/1) + x6)
               + (- 16/1) * x5 * (3/1 + x6) + 16/1 * (16/1 + 9/1 * x6))
              * x2
              + (x5 * (144/1 + (- 16/1) * x6 + x6 * x6)
                 + (- 8/1) * ((- 32/1) + 6/1 * x6 + x6 * x6))
                * x3)
         + 2/1
           * x4 * x4 * x4 * x4
             * (32/1 * x1 + 3/1 * (((- 8/1) + x5) * x2 + ((- 8/1) + x6) * x3))
           + 200/1
             * (x4 * x4 * x1
                + 8/1 * (x5 + (- 1/1) * x6) * (x2 + (- 1/1) * x3)
                  + (- 1/1)
                    * x4
                      * (16/1 * x1
                         + ((- 8/1) + x5) * x2 + ((- 8/1) + x6) * x3))
               * (x4 * x4 * x1
                  + 8/1 * (x5 + (- 1/1) * x6) * (x2 + (- 1/1) * x3)
                    + (- 1/1)
                      * x4
                        * (16/1 * x1
                           + ((- 8/1) + x5) * x2 + ((- 8/1) + x6) * x3))
             + 2/1
               * x4 * x4
                 * (x5 + (- 1/1) * x6)
                   * (x5 * x5 * x2
                      + 8/1 * x6 * (4/1 * x1 + 9/1 * x2 + (- 7/1) * x3)
                        + 384/1 * (x2 + (- 1/1) * x3)
                          + (- 1/1) * x6 * x6 * x3
                            + x5
                              * ((- 32/1) * x1
                                 + (56/1 + (- 9/1) * x6) * x2
                                   + 9/1 * ((- 8/1) + x6) * x3))
               + (- 16/1)
                 * x4
                   * (x5 + (- 1/1) * x6)
                     * (x5 * x5 * (x2 + (- 3/1) * x3)
                        + (- 4/1)
                          * x5
                            * (8/1 * x1
                               + ((- 20/1) + 3/1 * x6) * x2
                                 + (- 3/1) * ((- 4/1) + x6) * x3)
                          + x6
                            * (32/1 * x1
                               + 3/1 * (16/1 + x6) * x2
                                 + (- 1/1) * (80/1 + x6) * x3))))
                    
(* bound on x1 : x1 \in [1, 1.17547965573] *)
let b1 = Sos.((x1 - 1 / 1) * (117547965573 / 100000000000 - x1))
(* bound on x2 : x2 \in [1, 1.17547965573] *)
let b2 = Sos.((x2 - 1 / 1) * (117547965573 / 100000000000 - x2))
(* bound on x3 : x3 \in [1, 1.17547965573] *)
let b3 = Sos.((x3 - 1 / 1) * (117547965573 / 100000000000 - x3))
(* bound on x4 : x4 \in [2.51952632905, 15.53] *)
let b4 = Sos.((x4 - 251952632905 / 100000000000) * (1553 / 100 - x4))
(* bound on x5 : x5 \in [2.51952632905, 16] *)
let b5 = Sos.((x5 - 251952632905 / 100000000000) * (16 / 1 - x5))
(* bound on x6 : x6 \in [2.51952632905, 16] *)
let b6 = Sos.((x6 - 251952632905 / 100000000000) * (16 / 1 - x6))

(* prove that p > 0 on the above defined box *)
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
  let sigma1, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma2, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma3, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma4, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma5, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let sigma6, _ = Sos.var_poly "s1" 6 (rup (deg - 2)) in 
  let e = Sos.(sigma * p - sigma1 * b1 - sigma2 * b2 - sigma3 * b3 - sigma4 * b4 - sigma5 * b5 - sigma6 * b6) in
  let ret, _, vals, _ =
    Sos.solve ~options Sos.Purefeas [e; sigma; sigma1; sigma2; sigma3; sigma4; sigma5; sigma6] in
  let sigma = Sos.value_poly sigma vals in
  Format.printf "@[<v>@[<v 2>Let sigma (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma;
  let sigma1 = Sos.value_poly sigma1 vals in
  Format.printf "@[<v>@[<v 2>Let sigma (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma1;
  let sigma2 = Sos.value_poly sigma2 vals in
  Format.printf "@[<v>@[<v 2>Let sigma (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma2;
  let sigma3 = Sos.value_poly sigma3 vals in
  Format.printf "@[<v>@[<v 2>Let sigma (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma3;
  let sigma4 = Sos.value_poly sigma4 vals in
  Format.printf "@[<v>@[<v 2>Let sigma (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma4;
  let sigma5 = Sos.value_poly sigma5 vals in
  Format.printf "@[<v>@[<v 2>Let sigma (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma5;
  let sigma6 = Sos.value_poly sigma6 vals in
  Format.printf "@[<v>@[<v 2>Let sigma (x0 x1 x2 x3 x4 x5 : R) :=@ %a.@]@ @]@."
                Sos.Poly.pp sigma6;
  ret = Osdp.SdpRet.Success

let _ =
  Format.printf "Bounds proved: %B@." check_p_pos
