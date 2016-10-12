From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 x3 x4 x5 : R) :=
  -4/1
  * (x3 * x3 * x0 + 8/1 * (x4 - x5) * (x1 - x2)
     - x3 * (16/1 * x0 + (x4 - 8/1) * x1 + (x5 - 8/1) * x2)).

Let b1 (x0 x1 x2 x3 x4 x5 : R) :=
  (x0 - 1) * (117547965573/100000000000 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 : R) :=
  (x1 - 1) * (117547965573/100000000000 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 : R) :=
  (x2 - 1) * (117547965573/100000000000 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 : R) :=
  (x3 - 251952632905/100000000000) * (90601/10000 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 : R) :=
  (x4 - 56644/10000) * (1553/100 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 : R) :=
  (x5 - 56644/10000) * (1553/100 - x5).

Let sigma (x0 x1 x2 x3 x4 x5 : R) :=
  4445458128749569/274877906944.

Let sigma1 (x0 x1 x2 x3 x4 x5 : R) :=
  6175447085540487/549755813888 + 497461732092215/549755813888 * x0
  + 107641781733245/274877906944 * x1 + 215283563466341/549755813888 * 
  x2 + 269849316282635/137438953472 * x3 + 27142131804909/17179869184 * 
  x4 + 868548217758003/549755813888 * x5
  + 5147769598638565/274877906944 * x0^2
  + 15689078045041/137438953472 * x0 * x1
  + 3800633096532749/274877906944 * x1^2
  + 62756312180751/549755813888 * x0 * x2
  + 207345788653597/549755813888 * x1 * x2
  + 950158274133173/68719476736 * x2^2
  + 205731320030229/274877906944 * x0 * x3
  + 560394868254601/274877906944 * x1 * x3
  + 35024679265925/17179869184 * x2 * x3
  + 3851383669963317/137438953472 * x3^2
  + 14335279395155/34359738368 * x0 * x4
  + 973715214608659/549755813888 * x1 * x4
  + 459909892109487/274877906944 * x2 * x4
  + 1319685078848825/137438953472 * x3 * x4
  + 6882574115245305/274877906944 * x4^2
  + 229364470322905/549755813888 * x0 * x5
  + 459909892109935/274877906944 * x1 * x5
  + 973715214609809/549755813888 * x2 * x5
  + 5278740315401065/549755813888 * x3 * x5
  + 2176830676162007/274877906944 * x4 * x5
  + 215080441101729/8589934592 * x5^2.

Let sigma2 (x0 x1 x2 x3 x4 x5 : R) :=
  3044295853974191/274877906944 + 84329656655889/549755813888 * x0
  + 475827902523821/549755813888 * x1 + 114376771969699/549755813888 * 
  x2 + 235317655108049/549755813888 * x3 + 340793408149453/549755813888 * 
  x4 + 554158580335521/549755813888 * x5
  + 7432407085050923/549755813888 * x0^2
  + 6380569993947/274877906944 * x0 * x1
  + 5188917287232013/274877906944 * x1^2
  + 39931520310429/274877906944 * x0 * x2
  + -100987218529/68719476736 * x1 * x2
  + 3747103459384205/274877906944 * x2^2
  + 200537200288737/549755813888 * x0 * x3
  + 45979889883205/274877906944 * x1 * x3
  + 300234606774257/549755813888 * x2 * x3
  + 1147110022260917/68719476736 * x3^2
  + 296385073222715/549755813888 * x0 * x4
  + 14999072768919/68719476736 * x1 * x4
  + 424065768244479/549755813888 * x2 * x4
  + 166649069683033/68719476736 * x3 * x4
  + 5568815169661977/274877906944 * x4^2
  + 396123623269751/549755813888 * x0 * x5
  + 98234060299245/274877906944 * x1 * x5
  + 583305278121481/549755813888 * x2 * x5
  + 1353695230585001/549755813888 * x3 * x5
  + 530294862644927/137438953472 * x4 * x5
  + 3021975993707161/137438953472 * x5^2.

Let sigma3 (x0 x1 x2 x3 x4 x5 : R) :=
  3044295853974085/274877906944 + 42164828327855/274877906944 * x0
  + 114376771969311/549755813888 * x1 + 475827902524037/549755813888 * 
  x2 + 3676838361069/8589934592 * x3 + 277079290166791/274877906944 * 
  x4 + 170396704074285/274877906944 * x5 + 116131360703923/8589934592 * 
  x0^2 + 4991440038773/34359738368 * x0 * x1
  + 3747103459383909/274877906944 * x1^2
  + 6380569994119/274877906944 * x0 * x2
  + -403948874025/274877906944 * x1 * x2 + 648614660904095/34359738368 * 
  x2^2 + 200537200288731/549755813888 * x0 * x3
  + 2345582865423/4294967296 * x1 * x3
  + 91959779768607/549755813888 * x2 * x3
  + 4588440089044141/274877906944 * x3^2
  + 198061811634319/274877906944 * x0 * x4
  + 583305278118137/549755813888 * x1 * x4
  + 98234060299641/274877906944 * x2 * x4
  + 676847615292159/274877906944 * x3 * x4
  + 1510987996857897/68719476736 * x4^2
  + 296385073221137/549755813888 * x0 * x5
  + 424065768243115/549755813888 * x1 * x5
  + 59996291075739/274877906944 * x2 * x5
  + 1333192557463969/549755813888 * x3 * x5
  + 265147431321691/68719476736 * x4 * x5 + 87012737025653/4294967296 * 
  x5^2.

Let sigma4 (x0 x1 x2 x3 x4 x5 : R) :=
  8365485667451311/1099511627776 + 245972569033155/274877906944 * x0
  + -485251264276549/549755813888 * x1 + -60656408034373/68719476736 * 
  x2 + -235778853990567/274877906944 * x3
  + -325354581316939/549755813888 * x4 + -325354581305433/549755813888 * 
  x5 + 1246772811194997/137438953472 * x0^2
  + 1632598358229/68719476736 * x0 * x1
  + 4369885249352517/549755813888 * x1^2
  + 6530393433319/274877906944 * x0 * x2
  + -646953915415867/549755813888 * x1 * x2
  + 8739770498705279/1099511627776 * x2^2
  + -1289466333121027/549755813888 * x0 * x3
  + -530635866978265/274877906944 * x1 * x3
  + -1061271733960799/549755813888 * x2 * x3
  + 543039916167879/137438953472 * x3^2
  + 1597240488557/274877906944 * x0 * x4
  + 1406561235877/549755813888 * x1 * x4
  + -421777801733345/549755813888 * x2 * x4
  + -314968958562683/137438953472 * x3 * x4
  + 316917567838625/137438953472 * x4^2
  + 3194480975185/549755813888 * x0 * x5
  + -421777801725977/549755813888 * x1 * x5
  + 1406561244663/549755813888 * x2 * x5
  + -1259875834223037/549755813888 * x3 * x5
  + -1155905518557463/549755813888 * x4 * x5
  + 39614695979261/17179869184 * x5^2.

Let sigma5 (x0 x1 x2 x3 x4 x5 : R) :=
  4210103583427431/1099511627776 + -76862366360203/137438953472 * x0
  + -129347104087587/549755813888 * x1 + 132861422094045/137438953472 * 
  x2 + -14448696237333/137438953472 * x3 + -255831522176179/549755813888 * 
  x4 + 2683786450691/137438953472 * x5
  + 4702105919165889/1099511627776 * x0^2
  + -233898991179385/274877906944 * x0 * x1
  + 275423252788883/68719476736 * x1^2
  + -490463078593019/549755813888 * x0 * x2
  + 212080595504189/549755813888 * x1 * x2
  + 5522151950573771/1099511627776 * x2^2
  + -619992382642867/549755813888 * x0 * x3
  + 449774081503041/549755813888 * x1 * x3
  + 137346730383927/137438953472 * x2 * x3
  + 891124670955059/549755813888 * x3^2
  + -59560749902915/274877906944 * x0 * x4
  + -328192524097359/549755813888 * x1 * x4
  + -792655661838941/549755813888 * x2 * x4
  + -514690511315797/549755813888 * x3 * x4
  + 255022736407573/274877906944 * x4^2
  + -3663648676499/68719476736 * x0 * x5
  + -123418891700407/274877906944 * x1 * x5
  + 87176111756877/137438953472 * x2 * x5
  + -175956685171589/549755813888 * x3 * x5
  + -677088360370247/549755813888 * x4 * x5
  + 515087618616517/549755813888 * x5^2.

Let sigma6 (x0 x1 x2 x3 x4 x5 : R) :=
  2105051791713537/549755813888 + -307449465438473/549755813888 * x0
  + 531445688374501/549755813888 * x1 + -1010524250709/4294967296 * x2
  + -14448696237229/137438953472 * x3 + 10735145802483/549755813888 * 
  x4 + -127915761088115/274877906944 * x5
  + 4702105919167713/1099511627776 * x0^2
  + -490463078589473/549755813888 * x0 * x1
  + 5522151950559603/1099511627776 * x1^2
  + -58474747794559/68719476736 * x0 * x2
  + 212080595501617/549755813888 * x1 * x2
  + 2203386022305397/549755813888 * x2^2
  + -309996191318489/274877906944 * x0 * x3
  + 549386921528321/549755813888 * x1 * x3
  + 224887040748711/274877906944 * x2 * x3
  + 445562335475805/274877906944 * x3^2
  + -14654594709803/274877906944 * x0 * x4
  + 348704447026561/549755813888 * x1 * x4
  + -246837783398301/549755813888 * x2 * x4
  + -87978342590357/274877906944 * x3 * x4
  + 515087618622949/549755813888 * x4^2
  + -59560749902867/274877906944 * x0 * x5
  + -198163915458169/137438953472 * x1 * x5
  + -164096262048485/274877906944 * x2 * x5
  + -514690511305741/549755813888 * x3 * x5
  + -338544180185205/274877906944 * x4 * x5
  + 31877842050773/34359738368 * x5^2.

Lemma relax_pos (x0 x1 x2 x3 x4 x5 : R) :
  sigma x0 x1 x2 x3 x4 x5 * p x0 x1 x2 x3 x4 x5
  - sigma1 x0 x1 x2 x3 x4 x5 * b1 x0 x1 x2 x3 x4 x5
  - sigma2 x0 x1 x2 x3 x4 x5 * b2 x0 x1 x2 x3 x4 x5
  - sigma3 x0 x1 x2 x3 x4 x5 * b3 x0 x1 x2 x3 x4 x5
  - sigma4 x0 x1 x2 x3 x4 x5 * b4 x0 x1 x2 x3 x4 x5
  - sigma5 x0 x1 x2 x3 x4 x5 * b5 x0 x1 x2 x3 x4 x5
  - sigma6 x0 x1 x2 x3 x4 x5 * b6 x0 x1 x2 x3 x4 x5 - 1/100000000 >= 0.
Proof.
rewrite /sigma /p /sigma1 /b1 /sigma2 /b2 /sigma3 /b3 /sigma4 /b4 /sigma5 /b5 /sigma6 /b6.
do_sdp.
Qed.

Lemma sigma_pos (x0 x1 x2 x3 x4 x5 : R) : sigma x0 x1 x2 x3 x4 x5 > 0.
Proof. rewrite /sigma. interval. Qed.

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
  
Theorem p_pos (x0 x1 x2 x3 x4 x5 x6 : R) :
  1 <= x0 <= 117547965573 / 100000000000 ->
  1 <= x1 <= 117547965573 / 100000000000 ->
  1 <= x2 <= 117547965573 / 100000000000 ->
  251952632905 / 100000000000 <= x3 <= 90601 / 10000 ->
  56644 / 10000 <= x4 <= 1553 / 100 ->
  56644 / 10000 <= x5 <= 1553 / 100 ->
  p x0 x1 x2 x3 x4 x5 > 0.
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
apply (Rmult_lt_reg_l (sigma x0 x1 x2 x3 x4 x5)); [by apply sigma_pos|].
rewrite Rmult_0_r.
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