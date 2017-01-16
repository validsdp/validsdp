Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

(* Attempt to prove that p >= 0 with p below is an
 * inductive invariant, for the program
 *
x1 = rand(0.9, 1.1);
x2 = rand(0, 0.2);
x3 = rand(0, 0.2);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2; pre_x3 = x3;
  if (x1^2 + x2^2 + x3^2 <= 1) {
    x1 = 0.25 * (0.8 * pre_x1^2 + 1.4 * pre_x2 - 0.5 * pre_x3^2);
    x2 = 0.25 * (1.3 * pre_x1 + 0.5 * pre_x3^2);
    x3 = 0.25 * (1.4 * pre_x2 + 0.8 * pre_x3^2);
  } else {
    x1 = 0.25 * (0.8 * pre_x1 + 0.4 * pre_x2^2);
    x2 = 0.25 * (-0.6 * pre_x2^2 + 0.3 * pre_x3^2);
    x3 = 0.25 * (0.5 * pre_x3 + 0.4 * pre_x1^2);
  }
}
 *)

(* initial condition 0.9 <= x1 <= 1.1 encoded as (x1 - 0.9)*(1.1 - x1) (>= 0) *)
Let pI1 (x0 x1 x2 : R) := (x0 - 9 / 10) * (11 / 10 - x0).
(* initial condition 0 <= x2 <= 0.2 *)
Let pI2 (x0 x1 x2 : R) := x1 * (2 / 10 - x1).
(* initial condition 0 <= x3 <= 0.2 *)
Let pI3 (x0 x1 x2 : R) := x2 * (2 / 10 - x2).
(* guard x1^2 + x2^2 + x3^2 <= 1 (then branch) *)
Let g0 x0 x1 x2 := 1 - (x0^2 + x1^2 + x2^2).
(* assignment in then branch *)
Let t0_x0 (x0 x1 x2 : R) := 1 / 4 * (8 / 10 * x0^2 + 14 / 10 * x1 - 5 / 10 * x2^2).
Let t0_x1 (x0 x1 x2 : R) := 1 / 4 * (13 / 10 * x0^2 + 5 / 10 * x2^2).
Let t0_x2 (x0 x1 x2 : R) := 1 / 4 * (14 / 10 * x1 + 8 / 10 * x2^2).
(* guard x1^2 + x2^2 + x3^2 >= 1 (else branch) *)
Let g1 x0 x1 x2 := (x0^2 + x1^2 + x2^2) - 1.
(* assignment in else branch *)
Let t1_x0 (x0 x1 x2 : R) := 1 / 4 * (8 / 10 * x0 + 4 / 10 * x1^2).
Let t1_x1 (x0 x1 x2 : R) := 1 / 4 * ((-6) / 10 * x1^2 + 3 / 10 * x2^2).
Let t1_x2 (x0 x1 x2 : R) := 1 / 4 * (5 / 10 * x2 + 4 / 10 * x0^2).

Let p x0 x1 x2 :=
  1404077481943518369/1152921504606846976
  + -4690730753774973/73786976294838206464 * x0
  + -1478009611459397/18446744073709551616 * x1
  + -6548811114947155/147573952589676412928 * x2
  + -2536496104439687/562949953421312 * x0^2
  + 2713734883229551/1125899906842624 * x0 * x1
  + -5388539986756451/1125899906842624 * x1^2
  + 331894980663973/140737488355328 * x0 * x2
  + 6703002984600757/36028797018963968 * x1 * x2
  + -1980646845255775/281474976710656 * x2^2
  + 2340730080101209/281474976710656 * x0^3
  + -1232702115117079/1125899906842624 * x0^2 * x1
  + 186084735812651/70368744177664 * x0 * x1^2
  + 7006429411529925/2251799813685248 * x1^3
  + -4867430770531313/9007199254740992 * x0^2 * x2
  + -2099569215370443/9007199254740992 * x0 * x1 * x2
  + 2799561618927169/9007199254740992 * x1^2 * x2
  + 7064849778944369/2251799813685248 * x0 * x2^2
  + 7371041094253453/18014398509481984 * x1 * x2^2
  + 1973536375667699/2251799813685248 * x2^3
  + -8263176341015451/2251799813685248 * x0^4
  + -3519673828710119/2251799813685248 * x0^3 * x1
  + -5501497524318127/1125899906842624 * x0^2 * x1^2
  + -2112892006518257/4503599627370496 * x0 * x1^3
  + -3858682229966235/562949953421312 * x1^4
  + -1172881297619675/1125899906842624 * x0^3 * x2
  + -332015849128509/562949953421312 * x0^2 * x1 * x2
  + -1866063945097653/72057594037927936 * x0 * x1^2 * x2
  + 5869393813214985/72057594037927936 * x1^3 * x2
  + -6175765965710763/2251799813685248 * x0^2 * x2^2
  + -7840966508126785/1152921504606846976 * x0 * x1 * x2^2
  + -6408527872230229/1125899906842624 * x1^2 * x2^2
  + 8739116262643759/18014398509481984 * x0 * x2^3
  + 6486629365517265/36028797018963968 * x1 * x2^3
  + -7845640891965281/1125899906842624 * x2^4
  + -5441413420351855/1125899906842624 * x0^5
  + -5281001973055283/4503599627370496 * x0^4 * x1
  + 8528427349938751/2251799813685248 * x0^3 * x1^2
  + -5707484586558783/9007199254740992 * x0^2 * x1^3
  + 8200580681240641/4503599627370496 * x0 * x1^4
  + 3008714871278631/4503599627370496 * x1^5
  + -5271532722781403/4503599627370496 * x0^4 * x2
  + -8685539241268985/18014398509481984 * x0^3 * x1 * x2
  + 4768859649698729/9007199254740992 * x0^2 * x1^2 * x2
  + 434508408791389/2251799813685248 * x0 * x1^3 * x2
  + 8792862375429941/1152921504606846976 * x1^4 * x2
  + 2350613034067383/562949953421312 * x0^3 * x2^2
  + 2794266994535109/4503599627370496 * x0^2 * x1 * x2^2
  + 7956221001046949/18014398509481984 * x0 * x1^2 * x2^2
  + -2211711120874207/18014398509481984 * x1^3 * x2^2
  + 5546577559517811/4503599627370496 * x0^2 * x2^3
  + 1918827278194925/4503599627370496 * x0 * x1 * x2^3
  + -8583722242535393/72057594037927936 * x1^2 * x2^3
  + 2393475270362875/2251799813685248 * x0 * x2^4
  + 2071699630397073/9007199254740992 * x1 * x2^4
  + -7640765733328111/72057594037927936 * x2^5
  + -6758302317586811/1125899906842624 * x0^6
  + 3802283543052687/18014398509481984 * x0^5 * x1
  + 479771562634651/281474976710656 * x0^4 * x1^2
  + 3088921046353593/562949953421312 * x0^3 * x1^3
  + -474386513098783/70368744177664 * x0^2 * x1^4
  + 1136755962367225/140737488355328 * x0 * x1^5
  + -2935463847438889/281474976710656 * x1^6
  + -1708304504009039/1125899906842624 * x0^5 * x2
  + 7537177207466601/18014398509481984 * x0^4 * x1 * x2
  + -760308488270199/4503599627370496 * x0^3 * x1^2 * x2
  + 893636199608221/562949953421312 * x0^2 * x1^3 * x2
  + -8677800910826745/9007199254740992 * x0 * x1^4 * x2
  + 206322440431913/140737488355328 * x1^5 * x2
  + 3552748017208757/1125899906842624 * x0^4 * x2^2
  + 6856749714766433/4503599627370496 * x0^3 * x1 * x2^2
  + -6604053592605293/2251799813685248 * x0^2 * x1^2 * x2^2
  + 6472498497361563/4503599627370496 * x0 * x1^3 * x2^2
  + -4330072629347327/1125899906842624 * x1^4 * x2^2
  + 6293759220265695/4503599627370496 * x0^3 * x2^3
  + 5475287585247257/4503599627370496 * x0^2 * x1 * x2^3
  + -6698535089107439/9007199254740992 * x0 * x1^2 * x2^3
  + 8727648267319441/9007199254740992 * x1^3 * x2^3
  + -6222388546121277/4503599627370496 * x0^2 * x2^4
  + 7951540282360195/9007199254740992 * x0 * x1 * x2^4
  + -7100637882549083/2251799813685248 * x1^2 * x2^4
  + -349969088867887/2251799813685248 * x0 * x2^5
  + 631930830178211/1125899906842624 * x1 * x2^5
  + -4776949905972299/1125899906842624 * x2^6
  + 5332919167176789/281474976710656 * x0^7
  + 1427225690207245/2251799813685248 * x0^6 * x1
  + 6245785285410135/562949953421312 * x0^5 * x1^2
  + 4729589326186315/1125899906842624 * x0^4 * x1^3
  + 6923100697933705/4503599627370496 * x0^3 * x1^4
  + 6186795586509573/2251799813685248 * x0^2 * x1^5
  + 1396707232815443/562949953421312 * x0 * x1^6
  + 5907179855851675/576460752303423488 * x1^7
  + -382420518756523/72057594037927936 * x0^6 * x2
  + 2923496082947383/9007199254740992 * x0^5 * x1 * x2
  + 3291314216595703/4503599627370496 * x0^4 * x1^2 * x2
  + 5350033724801201/4503599627370496 * x0^3 * x1^3 * x2
  + 6912109572810549/18014398509481984 * x0^2 * x1^4 * x2
  + 6303912249995553/72057594037927936 * x0 * x1^5 * x2
  + 2557558784579281/4503599627370496 * x1^6 * x2
  + 3245271898644809/281474976710656 * x0^5 * x2^2
  + 6329603215289623/4503599627370496 * x0^4 * x1 * x2^2
  + 5052074948120249/4503599627370496 * x0^3 * x1^2 * x2^2
  + 5494410255156573/72057594037927936 * x0^2 * x1^3 * x2^2
  + 7542374306625671/4503599627370496 * x0 * x1^4 * x2^2
  + -5436541877888809/18014398509481984 * x1^5 * x2^2
  + 2785922998900665/1125899906842624 * x0^4 * x2^3
  + 3661633640618673/4503599627370496 * x0^3 * x1 * x2^3
  + 7421187107509169/18014398509481984 * x0^2 * x1^2 * x2^3
  + -5139161992752075/18014398509481984 * x0 * x1^3 * x2^3
  + 1580198398130303/2251799813685248 * x1^4 * x2^3
  + 5339839836235037/1125899906842624 * x0^3 * x2^4
  + 6278340083133101/9007199254740992 * x0^2 * x1 * x2^4
  + 5918295359896203/4503599627370496 * x0 * x1^2 * x2^4
  + -5129042746317965/72057594037927936 * x1^3 * x2^4
  + 4625859054996289/4503599627370496 * x0^2 * x2^5
  + 6632774179275995/144115188075855872 * x0 * x1 * x2^5
  + 5132763764943325/9007199254740992 * x1^2 * x2^5
  + 1440141004517167/562949953421312 * x0 * x2^6
  + 1968461622735257/18014398509481984 * x1 * x2^6
  + 1554903578069647/1125899906842624 * x2^7
  + -1306859823122925/140737488355328 * x0^8
  + 1390184850181887/2251799813685248 * x0^7 * x1
  + -6561717839745337/562949953421312 * x0^6 * x1^2
  + -2194287792928379/1125899906842624 * x0^5 * x1^3
  + -5996627871917977/562949953421312 * x0^4 * x1^4
  + -2832885327087951/281474976710656 * x0^3 * x1^5
  + -2684101849574601/562949953421312 * x0^2 * x1^6
  + -341235760672839/17592186044416 * x0 * x1^7
  + -6593139126922967/562949953421312 * x1^8
  + 4406626387675797/2251799813685248 * x0^7 * x2
  + -3295616118476455/4503599627370496 * x0^6 * x1 * x2
  + 5893178493427421/2251799813685248 * x0^5 * x1^2 * x2
  + -6821643251668163/4503599627370496 * x0^4 * x1^3 * x2
  + 2680214762209249/1125899906842624 * x0^3 * x1^4 * x2
  + -8865629213587893/4503599627370496 * x0^2 * x1^5 * x2
  + 2985651752625837/1125899906842624 * x0 * x1^6 * x2
  + -3155812340100005/1125899906842624 * x1^7 * x2
  + -3957444548482123/281474976710656 * x0^6 * x2^2
  + 4642083274258973/9007199254740992 * x0^5 * x1 * x2^2
  + -206291306656113/17592186044416 * x0^4 * x1^2 * x2^2
  + -2470673628419849/1125899906842624 * x0^3 * x1^3 * x2^2
  + -2580458126641787/281474976710656 * x0^2 * x1^4 * x2^2
  + -837851048441189/281474976710656 * x0 * x1^5 * x2^2
  + -2521303658435251/140737488355328 * x1^6 * x2^2
  + 1375950706179403/562949953421312 * x0^5 * x2^3
  + -4985664719913117/4503599627370496 * x0^4 * x1 * x2^3
  + 6354858290784471/2251799813685248 * x0^3 * x1^2 * x2^3
  + -4318450417393931/1125899906842624 * x0^2 * x1^3 * x2^3
  + 649899217251995/140737488355328 * x0 * x1^4 * x2^3
  + -4359020209468295/1125899906842624 * x1^5 * x2^3
  + -5076732857597831/281474976710656 * x0^4 * x2^4
  + -8248933102050869/9007199254740992 * x0^3 * x1 * x2^4
  + -2966525781542513/281474976710656 * x0^2 * x1^2 * x2^4
  + -6394148556325935/2251799813685248 * x0 * x1^3 * x2^4
  + -1200316728006013/70368744177664 * x1^4 * x2^4
  + 6714758371464879/4503599627370496 * x0^3 * x2^5
  + -7440601840996515/4503599627370496 * x0^2 * x1 * x2^5
  + 2903411336340129/1125899906842624 * x0 * x1^2 * x2^5
  + -4910099446910159/2251799813685248 * x1^3 * x2^5
  + -5221786196187869/281474976710656 * x0^2 * x2^6
  + -5240026763654467/4503599627370496 * x0 * x1 * x2^6
  + -4956925183119031/281474976710656 * x1^2 * x2^6
  + 4566524972446513/2251799813685248 * x0 * x2^7
  + -3872808106483703/4503599627370496 * x1 * x2^7
  + -1448228184768257/70368744177664 * x2^8.
  
Theorem init (x0 x1 x2 : R) :
  pI1 x0 x1 x2 >= 0 -> pI2 x0 x1 x2 >= 0 -> pI3 x0 x1 x2 >= 0 ->
  p x0 x1 x2 >= 0.
Proof.
unfold pI1, pI2, pI3, p.
validsdp.
Qed.

Theorem ind0 (x0 x1 x2 : R) :
  p x0 x1 x2 >= 0 -> g0 x0 x1 x2 >= 0 -> 
  p (t0_x0 x0 x1 x2) (t0_x1 x0 x1 x2) (t0_x2 x0 x1 x2) >= 0.
Proof.
unfold p, g0, t0_x0, t0_x1, t0_x2.
validsdp.
Qed.

Theorem ind1 (x0 x1 x2 : R) :
  p x0 x1 x2 >= 0 -> g1 x0 x1 x2 >= 0 ->
  p (t1_x0 x0 x1 x2) (t1_x1 x0 x1 x2) (t1_x2 x0 x1 x2) >= 0.
Proof.
unfold p, g1, t1_x0, t1_x1, t1_x2.
validsdp.
Qed.
