From mathcomp Require Import ssreflect.
Require Import Reals.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

(* Attempt to prove that p >= 0 with p below is an
 * inductive invariant, for the program
 *
x1 = rand(0.5, 0.7);
x2 = rand(0.5, 0.7);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2;
  if (x1^2 + x2^2 <= 1) {
    x1 = pre_x1^2 + pre_x2^3;
    x2 = pre_x1^3 + pre_x2^2;
  } else {
    x1 = 0.5 * pre_x1^3 + 0.4 * pre_x2^2;
    x2 = -0.6 * pre_x1^2 + 0.3 * pre_x2^2;
  }
}
 *)

(* initial condition 0.5 <= x1 <= 0.7 encoded as (x1 - 0.5)*(0.7 - x1) (>= 0) *)
Let pI1 (x0 x1 : R) := (x0 - 5 / 10) * (7 / 10 - x0).
(* initial condition 0.5 <= x2 <= 0.7 *)
Let pI2 (x0 x1 : R) := (x1 - 5 / 10) * (7 / 10 - x1).
(* guard x1^2 + x2^2 <= 1 (then branch) *)
Let g0 x0 x1 := 1 - (x0^2 + x1^2).
(* assignment in then branch *)
Let t0_x0 (x0 x1 : R) := x0^2 + x1^3.
Let t0_x1 (x0 x1 : R) := x0^3 + x1^2.
(* guard x1^2 + x2^2 >= 1 (else branch) *)
Let g1 x0 x1 := (x0^2 + x1^2) - 1.
(* assignment in else branch *)
Let t1_x0 (x0 x1 : R) := 5 / 10 * x0^3 + 4 / 10 * x1^2.
Let t1_x1 (x0 x1 : R) := (-6) / 10 * x0^2 + 3 / 10 * x1^2.

Let p x0 x1 :=
  128676781657/35184372088832 + 5936533188087895/1152921504606846976 * 
  x0 + -5230768883648489/18446744073709551616 * x1
  + -7219569841125045/288230376151711744 * x0^2
  + 6762644639133095/1152921504606846976 * x0 * x1
  + -1394133347692873/144115188075855872 * x1^2
  + 856506940949991/72057594037927936 * x0^3
  + -507149751329383/36028797018963968 * x0^2 * x1
  + 8312134809735735/576460752303423488 * x0 * x1^2
  + 8438999796757737/288230376151711744 * x1^3
  + -2814603216904403/288230376151711744 * x0^4
  + -1982831447875497/9223372036854775808 * x0^3 * x1
  + 8922750143978795/288230376151711744 * x0^2 * x1^2
  + 179041025134977/72057594037927936 * x0 * x1^3
  + -3249250773001133/72057594037927936 * x1^4.
  
Let init_sigma1 x0 x1 :=
  7019264510689479/72057594037927936
  + -7024791364135575/72057594037927936 * x0
  + -2935817909816531/36028797018963968 * x1
  + 6509361164813447/36028797018963968 * x0^2
  + -2959264899769387/36028797018963968 * x0 * x1
  + 5611325041580107/36028797018963968 * x1^2.
  
Let init_sigma2 x0 x1 :=
  1620172820685253/18014398509481984
  + -7535312143315291/72057594037927936 * x0
  + -6233911130111195/72057594037927936 * x1
  + 2597590236502567/18014398509481984 * x0^2
  + -6610391564740097/72057594037927936 * x0 * x1
  + 7429967200179683/36028797018963968 * x1^2.
  
Let ind0_sigma x0 x1 :=
  7323900344779583/18014398509481984
  + -6449470945007025/36028797018963968 * x0
  + -4040326342536237/18014398509481984 * x1
  + 11099171131569/35184372088832 * x0^2
  + -6034167776083649/36028797018963968 * x0 * x1
  + 1231278566432359/4503599627370496 * x1^2
  + -4447836744661945/72057594037927936 * x0^3
  + -7072190406828427/72057594037927936 * x0^2 * x1
  + -5837223489102711/72057594037927936 * x0 * x1^2
  + -3833501317057561/36028797018963968 * x1^3
  + 1274469358782875/4503599627370496 * x0^4
  + -5531166182060749/72057594037927936 * x0^3 * x1
  + 4540853867681339/72057594037927936 * x0^2 * x1^2
  + -3204697930089611/36028797018963968 * x0 * x1^3
  + 4378062065733121/18014398509481984 * x1^4
  + -5073085294161843/288230376151711744 * x0^5
  + -7201372354278879/144115188075855872 * x0^4 * x1
  + -3704422158366523/144115188075855872 * x0^3 * x1^2
  + -5715750941593921/144115188075855872 * x0^2 * x1^3
  + -2825514472900883/72057594037927936 * x0 * x1^4
  + -5881497303318003/144115188075855872 * x1^5
  + 8150199931183415/36028797018963968 * x0^6
  + -284633355204855/9007199254740992 * x0^5 * x1
  + 4676649197533931/72057594037927936 * x0^4 * x1^2
  + -627980541404389/18014398509481984 * x0^3 * x1^3
  + 2098221174195071/36028797018963968 * x0^2 * x1^4
  + -5549735869823123/144115188075855872 * x0 * x1^5
  + 7223440237383799/36028797018963968 * x1^6
  + -6998197184056349/1152921504606846976 * x0^7
  + -5844488758426591/288230376151711744 * x0^6 * x1
  + -2960327612388055/576460752303423488 * x0^5 * x1^2
  + -2463732051004733/144115188075855872 * x0^4 * x1^3
  + -8426754250539843/576460752303423488 * x0^3 * x1^4
  + -8084834635509327/576460752303423488 * x0^2 * x1^5
  + -7488503934606553/576460752303423488 * x0 * x1^6
  + -898972290678965/72057594037927936 * x1^7
  + 887599786293199/4503599627370496 * x0^8
  + -4375718648457075/576460752303423488 * x0^7 * x1
  + 1781436109797427/18014398509481984 * x0^6 * x1^2
  + -370297205248139/36028797018963968 * x0^5 * x1^3
  + 6532456841877161/72057594037927936 * x0^4 * x1^4
  + -2926149648789151/288230376151711744 * x0^3 * x1^5
  + 6883045296534941/72057594037927936 * x0^2 * x1^6
  + -3035418550763881/288230376151711744 * x0 * x1^7
  + 3365346059079695/18014398509481984 * x1^8.
  
Let ind0_sigma0 x0 x1 :=
  2053113614325053/2305843009213693952
  + -7668075693991709/9223372036854775808 * x0
  + 6977224525040075/18446744073709551616 * x1
  + 5369177541705251/576460752303423488 * x0^2
  + -2382579202854241/2305843009213693952 * x0 * x1
  + 6052609509447875/2305843009213693952 * x1^2
  + -5430184798570979/2305843009213693952 * x0^3
  + 3504975538862215/2305843009213693952 * x0^2 * x1
  + -3410565493922595/576460752303423488 * x0 * x1^2
  + -5623574890405209/2305843009213693952 * x1^3
  + 6068359741859699/2305843009213693952 * x0^4
  + 45822762687527/36028797018963968 * x0^3 * x1
  + 5148434321861035/1152921504606846976 * x0^2 * x1^2
  + 2350790674492893/288230376151711744 * x0 * x1^3
  + 7309912895887/562949953421312 * x1^4
  + -4918900260340481/1152921504606846976 * x0^5
  + 2591327535597805/576460752303423488 * x0^4 * x1
  + -5198839157921745/144115188075855872 * x0^3 * x1^2
  + -4506766845800971/144115188075855872 * x0^2 * x1^3
  + -8941938952293685/2305843009213693952 * x0 * x1^4
  + -8851760662725701/2305843009213693952 * x1^5
  + -3590860673162401/288230376151711744 * x0^6
  + -5030910554749155/576460752303423488 * x0^5 * x1
  + 6262561621691195/288230376151711744 * x0^4 * x1^2
  + -7260449421167563/576460752303423488 * x0^3 * x1^3
  + 3587596903684831/72057594037927936 * x0^2 * x1^4
  + -2365129596140191/288230376151711744 * x0 * x1^5
  + 6363926736536179/4611686018427387904 * x1^6
  + -2260381375189159/72057594037927936 * x0^7
  + 6031632779940831/1152921504606846976 * x0^6 * x1
  + -6933057276115893/288230376151711744 * x0^5 * x1^2
  + -3141948210792407/144115188075855872 * x0^4 * x1^3
  + -6916343576668749/2305843009213693952 * x0^3 * x1^4
  + -5713492850064269/144115188075855872 * x0^2 * x1^5
  + -664321052202791/72057594037927936 * x0 * x1^6
  + -423731850494951/18014398509481984 * x1^7
  + 6650690034965047/4611686018427387904 * x0^8
  + -586385093503247/72057594037927936 * x0^7 * x1
  + 690974384494141/9007199254740992 * x0^6 * x1^2
  + -6964037675416891/288230376151711744 * x0^5 * x1^3
  + 375194317455171/4503599627370496 * x0^4 * x1^4
  + -3466030851868123/144115188075855872 * x0^3 * x1^5
  + 5134883256635455/72057594037927936 * x0^2 * x1^6
  + -2475999304352383/144115188075855872 * x0 * x1^7
  + -7466102966575311/576460752303423488 * x1^8
  + -3731613169480167/144115188075855872 * x0^9
  + -1111212941228517/576460752303423488 * x0^8 * x1
  + 37239174968863/2251799813685248 * x0^7 * x1^2
  + -5539261079409253/288230376151711744 * x0^6 * x1^3
  + -4036654337161293/1152921504606846976 * x0^5 * x1^4
  + -633417084043187/36028797018963968 * x0^4 * x1^5
  + -7201971662869261/288230376151711744 * x0^3 * x1^6
  + -5710130273273625/576460752303423488 * x0^2 * x1^7
  + -203382912614625/9007199254740992 * x0 * x1^8
  + -4536440761990553/144115188075855872 * x1^9
  + 2461363866873391/18014398509481984 * x0^10
  + -5967134105644901/2305843009213693952 * x0^9 * x1
  + 6968080103218187/72057594037927936 * x0^8 * x1^2
  + -2691959558707721/288230376151711744 * x0^7 * x1^3
  + 849123581522941/9007199254740992 * x0^6 * x1^4
  + -3272911168363375/1152921504606846976 * x0^5 * x1^5
  + 7134943101653055/72057594037927936 * x0^4 * x1^6
  + -291472385059013/36028797018963968 * x0^3 * x1^7
  + 3576409526297767/36028797018963968 * x0^2 * x1^8
  + -2500477416919763/288230376151711744 * x0 * x1^9
  + 8305996239736813/72057594037927936 * x1^10.
  
Let ind1_sigma x0 x1 :=
  5348898675779807/1099511627776 + -4731745624920891/274877906944 * x0
  + -109246040079727/8589934592 * x1 + 4414069514127567/137438953472 * 
  x0^2 + 2006991879546395/274877906944 * x0 * x1
  + 7286249933348687/274877906944 * x1^2
  + -2917931354041249/137438953472 * x0^3
  + -5462014557797591/4398046511104 * x0^2 * x1
  + -3206333824321407/1099511627776 * x0 * x1^2
  + -1757811914507609/68719476736 * x1^3
  + 4678260387336511/1125899906842624 * x0^4
  + -4603676723792027/274877906944 * x0^3 * x1
  + 6086068024862617/274877906944 * x0^2 * x1^2
  + -2445984764820111/137438953472 * x0 * x1^3
  + 6079793475102249/549755813888 * x1^4
  + -2658486322458449/274877906944 * x0^5
  + -1619297187534733/137438953472 * x0^4 * x1
  + -2305378395673611/549755813888 * x0^3 * x1^2
  + -5777733938183497/549755813888 * x0^2 * x1^3
  + -7572589530447067/4398046511104 * x0 * x1^4
  + -980729258220403/137438953472 * x1^5
  + 6494009297874043/137438953472 * x0^6
  + 8744468126555789/549755813888 * x0^5 * x1
  + 74257848141389/2147483648 * x0^4 * x1^2
  + -3295598069299743/274877906944 * x0^3 * x1^3
  + 4290653463436125/137438953472 * x0^2 * x1^4
  + 7536800809492127/549755813888 * x0 * x1^5
  + 8385741551705061/274877906944 * x1^6
  + -6712010422447007/137438953472 * x0^7
  + -2499998408701971/274877906944 * x0^6 * x1
  + 38920017280917/8589934592 * x0^5 * x1^2
  + -4120227441791119/137438953472 * x0^4 * x1^3
  + -5333797908469897/274877906944 * x0^3 * x1^4
  + -4693305283907115/2199023255552 * x0^2 * x1^5
  + -6270451239271111/1099511627776 * x0 * x1^6
  + -2893892347894751/68719476736 * x1^7
  + 7588906405255685/274877906944 * x0^8
  + -6017300883189067/137438953472 * x0^7 * x1
  + 1998095939449661/34359738368 * x0^6 * x1^2
  + -7747734109350211/274877906944 * x0^5 * x1^3
  + 1347276708647237/68719476736 * x0^4 * x1^4
  + -5624460330036025/274877906944 * x0^3 * x1^5
  + 1354651119115549/34359738368 * x0^2 * x1^6
  + -7843655858664423/274877906944 * x0 * x1^7
  + 6659867633182129/274877906944 * x1^8.
  
Let ind1_sigma1 x0 x1 :=
  2596181279148647/8796093022208 + -3474641175662521/4398046511104 * 
  x0 + -2552783027232731/2199023255552 * x1
  + 7222233080706825/4398046511104 * x0^2
  + 2874422421195337/4398046511104 * x0 * x1
  + 6420689257252173/2199023255552 * x1^2
  + -1353897502834451/549755813888 * x0^3
  + 8378049888553207/17592186044416 * x0^2 * x1
  + -1315164129296985/2199023255552 * x0 * x1^2
  + -4753606906868393/1099511627776 * x1^3
  + 5921374735485321/2199023255552 * x0^4
  + -8823865228871783/8796093022208 * x0^3 * x1
  + -2728587292046239/1099511627776 * x0^2 * x1^2
  + 3755928777351711/2199023255552 * x0 * x1^3
  + 7089783784913637/2199023255552 * x1^4
  + -4871515091980853/2199023255552 * x0^5
  + 8660566246953479/8796093022208 * x0^4 * x1
  + 841736884265827/549755813888 * x0^3 * x1^2
  + 5019040271099375/2199023255552 * x0^2 * x1^3
  + -8807667144886979/4398046511104 * x0 * x1^4
  + -8961059394198905/8796093022208 * x1^5
  + 6840145381032323/4398046511104 * x0^6
  + -1879776386532151/2199023255552 * x0^5 * x1
  + -5421921299042885/35184372088832 * x0^4 * x1^2
  + -8660498781460167/140737488355328 * x0^3 * x1^3
  + -8060498788579703/8796093022208 * x0^2 * x1^4
  + 1433571113467433/17592186044416 * x0 * x1^5
  + 4523090084136611/4398046511104 * x1^6
  + -2161369179145007/2199023255552 * x0^7
  + 3556949048257979/8796093022208 * x0^6 * x1
  + 123299560608299/274877906944 * x0^5 * x1^2
  + -3006577850504329/2199023255552 * x0^4 * x1^3
  + -5608580470152695/4398046511104 * x0^3 * x1^4
  + 2810535113489443/2199023255552 * x0^2 * x1^5
  + 2824684152639555/4398046511104 * x0 * x1^6
  + -4688670213913391/2199023255552 * x1^7
  + 6540696146314349/8796093022208 * x0^8
  + -842086643277927/1099511627776 * x0^7 * x1
  + -3042654965743261/17592186044416 * x0^6 * x1^2
  + 7282068190607203/8796093022208 * x0^5 * x1^3
  + 8123282063832443/4398046511104 * x0^4 * x1^4
  + -6432038689603595/8796093022208 * x0^3 * x1^5
  + -1187726431088473/4398046511104 * x0^2 * x1^6
  + -6035623340487947/17592186044416 * x0 * x1^7
  + 8891497698661087/4398046511104 * x1^8
  + -6743893213621269/17592186044416 * x0^9
  + 8291975426691245/17592186044416 * x0^8 * x1
  + 1737220769070619/8796093022208 * x0^7 * x1^2
  + -4849562101514111/17592186044416 * x0^6 * x1^3
  + -3451490500635647/4398046511104 * x0^5 * x1^4
  + 1018861652583765/17592186044416 * x0^4 * x1^5
  + -2838583374594309/8796093022208 * x0^3 * x1^6
  + 614289701446695/1099511627776 * x0^2 * x1^7
  + 1031637996716869/8796093022208 * x0 * x1^8
  + -2463096227734627/2199023255552 * x1^9
  + 128414373499897/1099511627776 * x0^10
  + -394361102152661/2199023255552 * x0^9 * x1
  + -1403754646853025/8796093022208 * x0^8 * x1^2
  + 3745468391913473/8796093022208 * x0^7 * x1^3
  + 2973949531240667/562949953421312 * x0^6 * x1^4
  + -143354741287159/274877906944 * x0^5 * x1^5
  + 5266566147122987/8796093022208 * x0^4 * x1^6
  + -226883517933903/2199023255552 * x0^3 * x1^7
  + 7063663169223519/70368744177664 * x0^2 * x1^8
  + -7523778018964099/17592186044416 * x0 * x1^9
  + 7456438379416221/17592186044416 * x1^10.
  
Lemma init_pos (x0 x1 : R) :
  p x0 x1
  - init_sigma1 x0 x1 * pI1 x0 x1
  - init_sigma2 x0 x1 * pI2 x0 x1 >= 0.
Proof.
rewrite /p /init_sigma1 /pI1 /init_sigma2 /pI2.
validsdp.
Qed.

Lemma init_sigma1_pos (x0 x1 : R) : init_sigma1 x0 x1 >= 0.
Proof. rewrite /init_sigma1. validsdp. Qed.

Lemma init_sigma2_pos (x0 x1 : R) : init_sigma2 x0 x1 >= 0.
Proof. rewrite /init_sigma2. validsdp. Qed.

Lemma ind0_pos (x0 x1 : R) :
  p (t0_x0 x0 x1) (t0_x1 x0 x1)
  - ind0_sigma x0 x1 * p x0 x1
  - ind0_sigma0 x0 x1 * g0 x0 x1 >= 0.
Proof.
rewrite /p /t0_x0 /t0_x1 /ind0_sigma /ind0_sigma0 /g0.
validsdp.
Qed.

Lemma ind0_sigma_pos (x0 x1 : R) : ind0_sigma x0 x1 >= 0.
Proof. rewrite /ind0_sigma. validsdp. Qed.

Lemma ind0_sigma0_pos (x0 x1 : R) : ind0_sigma0 x0 x1 >= 0.
Proof. rewrite /ind0_sigma0. validsdp. Qed.

Lemma ind1_pos (x0 x1 : R) :
  p (t1_x0 x0 x1) (t1_x1 x0 x1)
  - ind1_sigma x0 x1 * p x0 x1
  - ind1_sigma1 x0 x1 * g1 x0 x1 >= 0.
Proof.
rewrite /p /t1_x0 /t1_x1 /ind1_sigma /ind1_sigma1 /g1.
validsdp.
Qed.

Lemma ind1_sigma_pos (x0 x1 : R) : ind1_sigma x0 x1 >= 0.
Proof. rewrite /ind1_sigma. validsdp. Qed.

Lemma ind1_sigma1_pos (x0 x1 : R) : ind1_sigma1 x0 x1 >= 0.
Proof. rewrite /ind1_sigma1. validsdp. Qed.

Theorem init (x0 x1 x2 : R) :
  pI1 x0 x1 >= 0 -> pI2 x0 x1 >= 0 ->
  p x0 x1 >= 0.
Proof.
move=> H1 H2.
apply (Rge_trans _ (p x0 x1 - init_sigma1 x0 x1 * pI1 x0 x1)).
{ rewrite -{1}(Rminus_0_r (p _ _)).
  apply Rplus_ge_compat_l, Ropp_ge_contravar.
  by apply Rle_ge, Rmult_le_pos; apply Rge_le; [apply init_sigma1_pos|]. }
apply (Rge_trans _ (p x0 x1 - init_sigma1 x0 x1 * pI1 x0 x1
                    - init_sigma2 x0 x1 * pI2 x0 x1)).
{ rewrite -{1}(Rminus_0_r (_ - _)).
  apply Rplus_ge_compat_l, Ropp_ge_contravar.
  by apply Rle_ge, Rmult_le_pos; apply Rge_le; [apply init_sigma2_pos|]. }
apply init_pos.
Qed.

Theorem ind0 (x0 x1 : R) :
  p x0 x1 >= 0 -> g0 x0 x1 >= 0 -> 
  p (t0_x0 x0 x1) (t0_x1 x0 x1) >= 0.
Proof.
move=> H1 H2.
apply (Rge_trans _ (p (t0_x0 x0 x1) (t0_x1 x0 x1)
                    - ind0_sigma x0 x1 * p x0 x1)).
{ rewrite -{1}(Rminus_0_r (p _ _)).
  apply Rplus_ge_compat_l, Ropp_ge_contravar.
  by apply Rle_ge, Rmult_le_pos; apply Rge_le; [apply ind0_sigma_pos|]. }
apply (Rge_trans _ (p (t0_x0 x0 x1) (t0_x1 x0 x1)
                    - ind0_sigma x0 x1 * p x0 x1
                    - ind0_sigma0 x0 x1 * g0 x0 x1)).
{ rewrite -{1}(Rminus_0_r (_ - _)).
  apply Rplus_ge_compat_l, Ropp_ge_contravar.
  by apply Rle_ge, Rmult_le_pos; apply Rge_le; [apply ind0_sigma0_pos|]. }
apply ind0_pos.
Qed.

Theorem ind1 (x0 x1 : R) :
  p x0 x1 >= 0 -> g1 x0 x1 >= 0 ->
  p (t1_x0 x0 x1) (t1_x1 x0 x1) >= 0.
Proof.
move=> H1 H2.
apply (Rge_trans _ (p (t1_x0 x0 x1) (t1_x1 x0 x1)
                    - ind1_sigma x0 x1 * p x0 x1)).
{ rewrite -{1}(Rminus_0_r (p _ _)).
  apply Rplus_ge_compat_l, Ropp_ge_contravar.
  by apply Rle_ge, Rmult_le_pos; apply Rge_le; [apply ind1_sigma_pos|]. }
apply (Rge_trans _ (p (t1_x0 x0 x1) (t1_x1 x0 x1)
                    - ind1_sigma x0 x1 * p x0 x1
                    - ind1_sigma1 x0 x1 * g1 x0 x1)).
{ rewrite -{1}(Rminus_0_r (_ - _)).
  apply Rplus_ge_compat_l, Ropp_ge_contravar.
  by apply Rle_ge, Rmult_le_pos; apply Rge_le; [apply ind1_sigma1_pos|]. }
apply ind1_pos.
Qed.
