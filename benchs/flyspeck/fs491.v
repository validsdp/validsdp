From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 x3 x4 x5 : R) :=
  0
  - (x0 * x3 * (0 - x0 + x1 + x2 - x3 + x4 + x5)
     + x1 * x4 * (x0 - x1 + x2 + x3 - x4 + x5)
     + x2 * x5 * (x0 + x1 - x2 + x3 + x4 - x5) - x1 * x2 * x3 - x0 * x2 * x4
     - x0 * x1 * x5 - x3 * x4 * x5).

Let p' (x0 x1 x2 x3 x4 x5 : R) :=
  7/50
  + x0 * x3 * (0 - x0 + x1 + x2 - x3 + x4 + x5)
    + x1 * x4 * (x0 - x1 + x2 + x3 - x4 + x5)
    + x2 * x5 * (x0 + x1 - x2 + x3 + x4 - x5) - x1 * x2 * x3 - x0 * x2 * x4
    - x0 * x1 * x5 - x3 * x4 * x5.

Let p'' (x0 x1 x2 x3 x4 x5 : R) :=
  -25
  + (0 - x1) * x2 - x0 * x3 + x1 * x4 + x2 * x5 - x4 * x5
    + x0 * (0 - x0 + x1 + x2 - x3 + x4 + x5).

Let b1 (x0 x1 x2 x3 x4 x5 : R) :=
  (x0 - 606887582536/100000000000) * (702674064/100000000 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 : R) :=
  (x1 - 4) * (8 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 : R) :=
  (x2 - 2) * (2 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 : R) :=
  (x3 - 2) * (2 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 : R) :=
  (x4 - 2) * (2 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 : R) :=
  (x5 - 4) * (8 - x5).

Let sigma (x0 x1 x2 x3 x4 x5 : R) :=
  8619801803206319/1125899906842624.

Let sigma' (x0 x1 x2 x3 x4 x5 : R) :=
  8615783493300031/1125899906842624.

Let sigma'' (x0 x1 x2 x3 x4 x5 : R) :=
  1901061532161349/590295810358705651712
  + -1813372394519565/618970019642690137449562112 * x0
  + 762568095924153/618970019642690137449562112 * x1
  + -2005075585899739/618970019642690137449562112 * x2
  + -174297674133019/618970019642690137449562112 * x3
  + -2004829484277301/618970019642690137449562112 * x4
  + 762598792936995/618970019642690137449562112 * x5
  + 4617076033614557/147573952589676412928 * x0^2
  + 4951977514153869/36893488147419103232 * x0 * x1
  + 1495095062599463/4611686018427387904 * x1^2
  + -8141356801938397/590295810358705651712 * x0 * x2
  + -4867223342078693/73786976294838206464 * x1 * x2
  + 7803060918275673/1180591620717411303424 * x2^2
  + 1210789455692115/4835703278458516698824704 * x0 * x3
  + 373948820742687/604462909807314587353088 * x1 * x3
  + -2201394698939351/38685626227668133590597632 * x2 * x3
  + 7604115300524289/2361183241434822606848 * x3^2
  + -8140947927851339/590295810358705651712 * x0 * x4
  + 1670990230660093/154742504910672534362390528 * x1 * x4
  + -644837869116379/618970019642690137449562112 * x2 * x4
  + -8807366271462245/154742504910672534362390528 * x3 * x4
  + 3901080909334861/590295810358705651712 * x4^2
  + 4952343174779685/36893488147419103232 * x0 * x5
  + 2044540309770343/77371252455336267181195264 * x1 * x5
  + 6683694629511133/618970019642690137449562112 * x2 * x5
  + 365271966961/590295810358705651712 * x3 * x5
  + -1216683340740895/18446744073709551616 * x4 * x5
  + 5980518748735603/18446744073709551616 * x5^2.

Let sigma1 (x0 x1 x2 x3 x4 x5 : R) :=
  3802048759584393/1180591620717411303424
  + 1129746356832213/19342813113834066795298816 * x0
  + 2671358003450599/618970019642690137449562112 * x1
  + 762305445808813/618970019642690137449562112 * x2
  + 960107250321837/618970019642690137449562112 * x3
  + 381156288857385/309485009821345068724781056 * x4
  + 2671319823439847/618970019642690137449562112 * x5
  + 3867078917460829/2305843009213693952 * x0^2
  + 4171060998241547/2305843009213693952 * x0 * x1
  + 2287356650723423/2305843009213693952 * x1^2
  + 1436151206413929/154742504910672534362390528 * x0 * x2
  + 3219625963840485/154742504910672534362390528 * x1 * x2
  + 7604113171433627/2361183241434822606848 * x2^2
  + 4124600266412141/618970019642690137449562112 * x0 * x3
  + 7252509690051897/618970019642690137449562112 * x1 * x3
  + 2507475248314229/309485009821345068724781056 * x2 * x3
  + 7604129000713877/2361183241434822606848 * x3^2
  + 5744575515687323/618970019642690137449562112 * x0 * x4
  + 8802779009187927/618970019642690137449562112 * x1 * x4
  + 150888340712173/19342813113834066795298816 * x2 * x4
  + 2507502801637519/309485009821345068724781056 * x3 * x4
  + 29703567076343/9223372036854775808 * x4^2
  + 8341865235369229/4611686018427387904 * x0 * x5
  + 4559781953893329/2305843009213693952 * x1 * x5
  + 8802838685939939/618970019642690137449562112 * x2 * x5
  + 7252533972175759/618970019642690137449562112 * x3 * x5
  + 402454981774463/19342813113834066795298816 * x4 * x5
  + 4574554279015119/4611686018427387904 * x5^2.

Let sigma2 (x0 x1 x2 x3 x4 x5 : R) :=
  7604098599620607/2361183241434822606848
  + 364705197968545/618970019642690137449562112 * x0
  + 591999381166069/154742504910672534362390528 * x1
  + 124317425174337/309485009821345068724781056 * x2
  + 228066331600071/618970019642690137449562112 * x3
  + -529004091548419/618970019642690137449562112 * x4
  + -5771941157295931/618970019642690137449562112 * x5
  + 8756071172017339/147573952589676412928 * x0^2
  + -4346985162320919/36893488147419103232 * x0 * x1
  + 5589065522787567/9223372036854775808 * x1^2
  + -1198855988141779/154742504910672534362390528 * x0 * x2
  + 2508110679003/1208925819614629174706176 * x1 * x2
  + 3802070013896177/1180591620717411303424 * x2^2
  + 787028315598773/4835703278458516698824704 * x0 * x3
  + -7008274386258895/38685626227668133590597632 * x1 * x3
  + 121089791795851/19342813113834066795298816 * x2 * x3
  + 237630127199293/73786976294838206464 * x3^2
  + 2840361352616793/618970019642690137449562112 * x0 * x4
  + -1955834484494169/309485009821345068724781056 * x1 * x4
  + -3505662487067353/154742504910672534362390528 * x2 * x4
  + -3664664572072063/618970019642690137449562112 * x3 * x4
  + 7604153833554043/2361183241434822606848 * x4^2
  + -617765220655119/154742504910672534362390528 * x0 * x5
  + -4196711446403437/2305843009213693952 * x1 * x5
  + -2228827566491643/618970019642690137449562112 * x2 * x5
  + -2354018615609629/154742504910672534362390528 * x3 * x5
  + -1459962776976859/154742504910672534362390528 * x4 * x5
  + 7075511815062621/4611686018427387904 * x5^2.

Let sigma3 (x0 x1 x2 x3 x4 x5 : R) :=
  3802053329841741/1180591620717411303424
  + 3926373541961595/618970019642690137449562112 * x0
  + 2187588272731369/618970019642690137449562112 * x1
  + 1312715697258181/309485009821345068724781056 * x2
  + 2195380259951985/618970019642690137449562112 * x3
  + 786857066372527/618970019642690137449562112 * x4
  + 1527219075448371/618970019642690137449562112 * x5
  + 4300431971082221/288230376151711744 * x0^2
  + 5004922341223007/4835703278458516698824704 * x0 * x1
  + 7283479338122483/36893488147419103232 * x1^2
  + 380548585101373/38685626227668133590597632 * x0 * x2
  + 2129955072480825/618970019642690137449562112 * x1 * x2
  + 1883452484068921/9223372036854775808 * x2^2
  + 3821818841242465/154742504910672534362390528 * x0 * x3
  + 1455580410610099/618970019642690137449562112 * x1 * x3
  + -1964306431110397/618970019642690137449562112 * x2 * x3
  + 481446907764923/9223372036854775808 * x3^2
  + 1302808784269799/77371252455336267181195264 * x0 * x4
  + 1172802259074509/154742504910672534362390528 * x1 * x4
  + -6655027120628849/154742504910672534362390528 * x2 * x4
  + 5081409462766043/309485009821345068724781056 * x3 * x4
  + 3066331491522009/18446744073709551616 * x4^2
  + 8780753606876217/576460752303423488 * x0 * x5
  + 4155962446109577/18446744073709551616 * x1 * x5
  + 1231682496510173/77371252455336267181195264 * x2 * x5
  + -197472915092693/309485009821345068724781056 * x3 * x5
  + 2876112075010997/618970019642690137449562112 * x4 * x5
  + 1171030135123591/288230376151711744 * x5^2.

Let sigma4 (x0 x1 x2 x3 x4 x5 : R) :=
  7604106852379017/2361183241434822606848
  + 3571120527024373/618970019642690137449562112 * x0
  + 1095698808970819/309485009821345068724781056 * x1
  + 64661959742665/38685626227668133590597632 * x2
  + 2250807088414423/309485009821345068724781056 * x3
  + 517300849498777/309485009821345068724781056 * x4
  + 2191403087766781/618970019642690137449562112 * x5
  + 1613995019623755/18014398509481984 * x0^2
  + 6345920209605651/144115188075855872 * x0 * x1
  + 3232795184412241/576460752303423488 * x1^2
  + 7022516127115983/618970019642690137449562112 * x0 * x2
  + 8232849236118341/618970019642690137449562112 * x1 * x2
  + 7604199567565191/2361183241434822606848 * x2^2
  + 3140579270583353/154742504910672534362390528 * x0 * x3
  + 1467497383406297/618970019642690137449562112 * x1 * x3
  + 6941719575982619/618970019642690137449562112 * x2 * x3
  + 7907573028936207/36893488147419103232 * x3^2
  + 7022587755143667/618970019642690137449562112 * x0 * x4
  + 879316105546093/77371252455336267181195264 * x1 * x4
  + 827290643513905/309485009821345068724781056 * x2 * x4
  + 6941928703678961/618970019642690137449562112 * x3 * x4
  + 7604199568790649/2361183241434822606848 * x4^2
  + 99152861761287/2251799813685248 * x0 * x5
  + 6461745712975061/576460752303423488 * x1 * x5
  + 7034669971344551/618970019642690137449562112 * x2 * x5
  + 733769070227511/309485009821345068724781056 * x3 * x5
  + 8232656031651851/618970019642690137449562112 * x4 * x5
  + 6465327042864247/1152921504606846976 * x5^2.

Let sigma5 (x0 x1 x2 x3 x4 x5 : R) :=
  3802053329842073/1180591620717411303424
  + 981593107417825/154742504910672534362390528 * x0
  + 23862808050179/9671406556917033397649408 * x1
  + 786857948148499/618970019642690137449562112 * x2
  + 2195381247387885/618970019642690137449562112 * x3
  + 2625421533789711/618970019642690137449562112 * x4
  + 1093798262210943/309485009821345068724781056 * x5
  + 4300547967738487/288230376151711744 * x0^2
  + 8780875964017889/576460752303423488 * x0 * x1
  + 4684141570905407/1152921504606846976 * x1^2
  + 2605641246869255/154742504910672534362390528 * x0 * x2
  + 719007290833693/154742504910672534362390528 * x1 * x2
  + 6132957924545581/36893488147419103232 * x2^2
  + 1910891949876257/77371252455336267181195264 * x0 * x3
  + -98728192497545/154742504910672534362390528 * x1 * x3
  + 635198057854111/38685626227668133590597632 * x2 * x3
  + 7705172948438195/147573952589676412928 * x3^2
  + 3044422668800381/309485009821345068724781056 * x0 * x4
  + 2463336287524699/154742504910672534362390528 * x1 * x4
  + -3327536499197613/77371252455336267181195264 * x2 * x4
  + -982137502313551/309485009821345068724781056 * x3 * x4
  + 7533421027158479/36893488147419103232 * x4^2
  + 625922240072409/604462909807314587353088 * x0 * x5
  + 8309773819487609/36893488147419103232 * x1 * x5
  + 2345572006469541/309485009821345068724781056 * x2 * x5
  + 1455708163636563/618970019642690137449562112 * x3 * x5
  + 2130041593028357/618970019642690137449562112 * x4 * x5
  + 3642330623795495/18446744073709551616 * x5^2.

Let sigma6 (x0 x1 x2 x3 x4 x5 : R) :=
  7604098599620041/2361183241434822606848
  + 364699925666221/618970019642690137449562112 * x0
  + -2885970990969867/309485009821345068724781056 * x1
  + -528995711542029/618970019642690137449562112 * x2
  + 28508095907913/77371252455336267181195264 * x3
  + 124312802545129/309485009821345068724781056 * x4
  + 1184002332681409/309485009821345068724781056 * x5
  + 8756673987331077/147573952589676412928 * x0^2
  + -1235561118780299/309485009821345068724781056 * x0 * x1
  + 1768866967477215/1152921504606846976 * x1^2
  + 2840354994604063/618970019642690137449562112 * x0 * x2
  + -1460000712826241/154742504910672534362390528 * x1 * x2
  + 3802076916835929/1180591620717411303424 * x2^2
  + 1574010033143681/9671406556917033397649408 * x0 * x3
  + -2354026534961835/154742504910672534362390528 * x1 * x3
  + -229040184177023/38685626227668133590597632 * x2 * x3
  + 7604164070508573/2361183241434822606848 * x3^2
  + -2397763858224005/309485009821345068724781056 * x0 * x4
  + -278588990592801/77371252455336267181195264 * x1 * x4
  + -1752801785482349/77371252455336267181195264 * x2 * x4
  + 1937455230790315/309485009821345068724781056 * x3 * x4
  + 7604140026988965/2361183241434822606848 * x4^2
  + -1086825430545721/9223372036854775808 * x0 * x5
  + -8393371338189991/4611686018427387904 * x1 * x5
  + -1955834564730973/309485009821345068724781056 * x2 * x5
  + -219002502695041/1208925819614629174706176 * x3 * x5
  + 1284240888436017/618970019642690137449562112 * x4 * x5
  + 5589076847678119/9223372036854775808 * x5^2.

Lemma relax_pos (x0 x1 x2 x3 x4 x5 : R) :
  sigma x0 x1 x2 x3 x4 x5 * p x0 x1 x2 x3 x4 x5
  + sigma' x0 x1 x2 x3 x4 x5 * p' x0 x1 x2 x3 x4 x5
  + sigma'' x0 x1 x2 x3 x4 x5 * p'' x0 x1 x2 x3 x4 x5
  - sigma1 x0 x1 x2 x3 x4 x5 * b1 x0 x1 x2 x3 x4 x5
  - sigma2 x0 x1 x2 x3 x4 x5 * b2 x0 x1 x2 x3 x4 x5
  - sigma3 x0 x1 x2 x3 x4 x5 * b3 x0 x1 x2 x3 x4 x5
  - sigma4 x0 x1 x2 x3 x4 x5 * b4 x0 x1 x2 x3 x4 x5
  - sigma5 x0 x1 x2 x3 x4 x5 * b5 x0 x1 x2 x3 x4 x5
  - sigma6 x0 x1 x2 x3 x4 x5 * b6 x0 x1 x2 x3 x4 x5 - 1/100000000 >= 0.
Proof.
rewrite /sigma /p /sigma' /p' /sigma'' /p'' /sigma1 /b1 /sigma2 /b2 /sigma3 /b3 /sigma4 /b4 /sigma5 /b5 /sigma6 /b6.
do_sdp.
Qed.

Lemma sigma_pos (x0 x1 x2 x3 x4 x5 : R) : sigma x0 x1 x2 x3 x4 x5 > 0.
Proof. rewrite /sigma. interval. Qed.

Lemma sigma'_pos (x0 x1 x2 x3 x4 x5 : R) : sigma' x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma'. interval. Qed.

Lemma sigma''_pos (x0 x1 x2 x3 x4 x5 : R) : sigma'' x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma''. do_sdp. Qed.

Lemma sigma1_pos (x0 x1 x2 x3 x4 x5 : R) : sigma1 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma1. do_sdp. Qed.

Lemma sigma2_pos (x0 x1 x2 x3 x4 x5 : R) : sigma2 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma2. do_sdp. Qed.

Lemma sigma3_pos (x0 x1 x2 x3 x4 x5 : R) : sigma3 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma3. do_sdp. Qed.

Lemma sigma4_pos (x0 x1 x2 x3 x4 x5 : R) : sigma4 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma4. do_sdp. Qed.

Lemma sigma5_pos (x0 x1 x2 x3 x4 x5 : R) : sigma5 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma5. do_sdp. Qed.

Lemma sigma6_pos (x0 x1 x2 x3 x4 x5 : R) : sigma6 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma6. do_sdp. Qed.

Lemma var_bounds (x l u : R) : l <= x <= u -> (x - l) * (u - x) >= 0.
Proof.
move=> [Hl Hu].
apply Rle_ge.
by apply Interval_missing.Rmult_le_pos_pos; apply Fcore_Raux.Rle_0_minus.
Qed.

Lemma relax (x y z : R) : x >= 0 -> y >= 0 -> z - x * y > 0 -> z > 0.
Proof.
move=> HX Hy.
apply Rge_gt_trans, Rle_ge.
rewrite -{2}(Rminus_0_r z).
apply Rplus_le_compat_l, Ropp_le_contravar.
by apply Interval_missing.Rmult_le_pos_pos; apply Rge_le.
Qed.
  
Lemma relax' (x y z : R) : x >= 0 -> y <= 0 -> z + x * y > 0 -> z > 0.
Proof.
move=> HX Hy.
apply Rge_gt_trans, Rle_ge.
rewrite -{2}(Rplus_0_r z) Rmult_comm.
by apply Rplus_le_compat_l, Interval_missing.Rmult_le_neg_pos; [|apply Rge_le].
Qed.
  
Theorem p_pos (x0 x1 x2 x3 x4 x5 x6 : R) :
  606887582536 / 100000000000 <= x0 <= 702674064 / 100000000 ->
  4 <= x1 <= 8 ->
  2 <= x2 <= 2 ->
  2 <= x3 <= 2 ->
  2 <= x4 <= 2 ->
  4 <= x5 <= 8 ->
  (p x0 x1 x2 x3 x4 x5 > 0 \/ p' x0 x1 x2 x3 x4 x5 > 0 \/ p'' x0 x1 x2 x3 x4 x5 > 0).
Proof.
move=> H1 H2 H3 H4 H5 H6.
have Hb0 : b1 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds. }
have Hb1 : b2 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds. }
have Hb2 : b3 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds. }
have Hb3 : b4 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds. }
have Hb4 : b5 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds. }
have Hb5 : b6 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds. }
elim (Rlt_or_le R0 (p' x0 x1 x2 x3 x4 x5))=> Hp'; [by right; left|].
elim (Rlt_or_le R0 (p'' x0 x1 x2 x3 x4 x5))=> Hp''; [by right; right|].
left.
apply (Rmult_lt_reg_l (sigma x0 x1 x2 x3 x4 x5)); [by apply sigma_pos|].
rewrite Rmult_0_r.
apply (relax' _ _ _ (sigma'_pos x0 x1 x2 x3 x4 x5) Hp').
apply (relax' _ _ _ (sigma''_pos x0 x1 x2 x3 x4 x5) Hp'').
apply (relax _ _ _ (sigma1_pos x0 x1 x2 x3 x4 x5) Hb0).
apply (relax _ _ _ (sigma2_pos x0 x1 x2 x3 x4 x5) Hb1).
apply (relax _ _ _ (sigma3_pos x0 x1 x2 x3 x4 x5) Hb2).
apply (relax _ _ _ (sigma4_pos x0 x1 x2 x3 x4 x5) Hb3).
apply (relax _ _ _ (sigma5_pos x0 x1 x2 x3 x4 x5) Hb4).
apply (relax _ _ _ (sigma6_pos x0 x1 x2 x3 x4 x5) Hb5).
move: (relax_pos x0 x1 x2 x3 x4 x5).
apply Rgt_ge_trans.
rewrite -{1}(Rplus_0_r (_ - _)).
apply (Rplus_gt_compat_l).
interval.
Qed.