From mathcomp Require Import ssreflect.
Require Import Reals.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

(* Attempt to prove that p >= 0 with p below is an
 * inductive invariant, for the program
 *
x1 = rand(-1.0, 1.0);
x2 = rand(-1.0, 1.0);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2;
  if (x2 <= x1) {
    x1 = 0.687 * pre_x1 + 0.558 * pre_x2 - 0.0001 * pre_x1 * pre_x2;
    x2 = -0.292 * pre_x1 + 0.773 * pre_x2;
  } else {
    x1 = 0.369 * pre_x1 + 0.532 * pre_x2 - 0.0001 * pre_x1^2;
    x2 = -1.27 * pre_x1 + 0.12 * pre_x2 - 0.0001 * pre_x1 * pre_x2;
  }
}
 *)

(* initial condition -1 <= x1 <= 1 encoded as (x1 - 1)*(1 - x1) (>= 0) *)
Let pI1 (x0 x1 : R) := (x0 - 1) * (1 - x0).
(* initial condition -1 <= x2 <= 1 *)
Let pI2 (x0 x1 : R) := (x1 - 1) * (1 - x1).
(* guard x2 <= x1 (then branch) *)
Let g0 x0 x1 := x0 - x1.
(* assignment in then branch *)
Let t0_x0 (x0 x1 : R) := 687 / 1000 * x0 + 558 / 1000 * x1 - 1 / 10000 * x0 * x1.
Let t0_x1 (x0 x1 : R) := (-292) / 1000 * x0 + 773 / 1000 * x1.
(* guard x2 >= x1 (else branch) *)
Let g1 x0 x1 := x1 - x0.
(* assignment in else branch *)
Let t1_x0 (x0 x1 : R) := 369 / 1000 * x0 + 532 / 1000 * x1 - 1 / 10000 * x0^2.
Let t1_x1 (x0 x1 : R) := (-127) / 100 * x0 + 12 / 100 * x1 - 1 / 10000 * x0 * x1.

Let p x0 x1 :=
  5584530192314348247/2305843009213693952
  + -7572809488173297/9223372036854775808 * x0^2
  + -3351319056397295/18446744073709551616 * x0 * x1
  + -1492313528838919/2305843009213693952 * x1^2
  + 792638027624227/36028797018963968 * x0^3
  + -649936176779617/18014398509481984 * x0^2 * x1
  + -7460504984132229/1152921504606846976 * x0 * x1^2
  + 6003265749214105/144115188075855872 * x1^3
  + -7802755816940159/2251799813685248 * x0^4
  + 7871713735635417/9007199254740992 * x0^3 * x1
  + -802162565287219/281474976710656 * x0^2 * x1^2
  + -7969935046478383/4503599627370496 * x0 * x1^3
  + -8058122533384465/4503599627370496 * x1^4
  + 6304886668598741/9007199254740992 * x0^5
  + -5879759571302991/4503599627370496 * x0^4 * x1
  + 1428135615671919/2251799813685248 * x0^3 * x1^2
  + 4624725334774435/4503599627370496 * x0^2 * x1^3
  + -3323827362212477/36028797018963968 * x0 * x1^4
  + 6213501134428863/36028797018963968 * x1^5
  + 3727613646058315/1125899906842624 * x0^6
  + -1302175560826897/562949953421312 * x0^5 * x1
  + 1351230835517577/281474976710656 * x0^4 * x1^2
  + 7845834977982049/9007199254740992 * x0^3 * x1^3
  + 5776381725141309/2251799813685248 * x0^2 * x1^4
  + 4916019723437323/2251799813685248 * x0 * x1^5
  + 526050222753071/562949953421312 * x1^6
  + -1885987045132373/4503599627370496 * x0^7
  + 2839487403187877/2251799813685248 * x0^6 * x1
  + -694782655065743/562949953421312 * x0^5 * x1^2
  + -8567388626964367/9007199254740992 * x0^4 * x1^3
  + 6154435898600785/9007199254740992 * x0^3 * x1^4
  + -7340678541293277/36028797018963968 * x0^2 * x1^5
  + -75528841553669/281474976710656 * x0 * x1^6
  + 5086071880772377/288230376151711744 * x1^7
  + -5027189675597491/4503599627370496 * x0^8
  + 7707974361870977/4503599627370496 * x0^7 * x1
  + -6623572786886881/2251799813685248 * x0^6 * x1^2
  + -6741416623377335/36028797018963968 * x0^5 * x1^3
  + -4820895189255331/9007199254740992 * x0^4 * x1^4
  + -1136271989758663/1125899906842624 * x0^3 * x1^5
  + -4247790739650063/4503599627370496 * x0^2 * x1^6
  + -8900501477532809/18014398509481984 * x0 * x1^7
  + -7713695984503821/36028797018963968 * x1^8.
  
Let init_sigma1 x0 x1 :=
  2323024130747713/140737488355328 + 1095440046704033/281474976710656 * 
  x0 + 1854872582417295/562949953421312 * x1
  + 7275636014655679/562949953421312 * x0^2
  + 522782685162045/281474976710656 * x0 * x1
  + 3717493009195581/281474976710656 * x1^2
  + 2657139674078893/2251799813685248 * x0^3
  + 409675308839059/140737488355328 * x0^2 * x1
  + 5696099427607513/2251799813685248 * x0 * x1^2
  + 2997782430598957/1125899906842624 * x1^3
  + 7386421888394441/562949953421312 * x0^4
  + 1305345090880725/562949953421312 * x0^3 * x1
  + 5240637738548661/562949953421312 * x0^2 * x1^2
  + 6356427045931871/2251799813685248 * x0 * x1^3
  + 7590087968114881/562949953421312 * x1^4
  + 4604876067185361/562949953421312 * x0^5
  + 4107315389588781/1125899906842624 * x0^4 * x1
  + 1029012921330305/281474976710656 * x0^3 * x1^2
  + 6514970340392341/2251799813685248 * x0^2 * x1^3
  + 2215546595889973/562949953421312 * x0 * x1^4
  + 6810533373506033/2251799813685248 * x1^5
  + 721906536142529/35184372088832 * x0^6
  + -1497730340389063/2251799813685248 * x0^5 * x1
  + 3882267171320373/281474976710656 * x0^4 * x1^2
  + 3058877922484409/2251799813685248 * x0^3 * x1^3
  + 7826885987852825/562949953421312 * x0^2 * x1^4
  + 1430131070138381/1125899906842624 * x0 * x1^5
  + 4926562098639835/281474976710656 * x1^6.
  
Let init_sigma2 x0 x1 :=
  2292221135256251/140737488355328 + 3384433403941609/1125899906842624 * 
  x0 + 8182238670934571/2251799813685248 * x1
  + 7290757138893569/562949953421312 * x0^2
  + 6857681504876865/4503599627370496 * x0 * x1
  + 1788256019459507/140737488355328 * x1^2
  + 1308726929111049/562949953421312 * x0^3
  + 4961070440229459/2251799813685248 * x0^2 * x1
  + 1388590415672489/562949953421312 * x0 * x1^2
  + 1421694723034927/1125899906842624 * x1^3
  + 7237418557046307/562949953421312 * x0^4
  + 5756991007702001/2251799813685248 * x0^3 * x1
  + 1270023889786091/140737488355328 * x0^2 * x1^2
  + 1059048598106471/562949953421312 * x0 * x1^3
  + 1832199454528689/140737488355328 * x1^4
  + 2925319665081741/1125899906842624 * x0^5
  + 8220819188987719/2251799813685248 * x0^4 * x1
  + 2874017966322193/1125899906842624 * x0^3 * x1^2
  + 449035441400005/140737488355328 * x0^2 * x1^3
  + 4565660941839009/1125899906842624 * x0 * x1^4
  + 7897455898223765/1125899906842624 * x1^5
  + 4967007783790545/281474976710656 * x0^6
  + 321786254461773/562949953421312 * x0^5 * x1
  + 7687744746013797/562949953421312 * x0^4 * x1^2
  + 5167264656306275/4503599627370496 * x0^3 * x1^3
  + 3716986201992567/281474976710656 * x0^2 * x1^4
  + -4808542038618493/36028797018963968 * x0 * x1^5
  + 1376567420156505/70368744177664 * x1^6.
  
Let ind0_sigma x0 x1 :=
  4562592300646611/9007199254740992 + -5404753535145099/9007199254740992 * 
  x0 + 5336178165605433/9007199254740992 * x1
  + 1245507207334575/1125899906842624 * x0^2
  + -6918107800833631/1125899906842624 * x0 * x1
  + 1100916278848337/562949953421312 * x1^2
  + -424999083415459/70368744177664 * x0^3
  + 5112640043038447/562949953421312 * x0^2 * x1
  + -6393071714920561/562949953421312 * x0 * x1^2
  + 2733151274767323/281474976710656 * x1^3
  + 6432563192731217/562949953421312 * x0^4
  + -292489808344243/35184372088832 * x0^3 * x1
  + 5981101681343577/562949953421312 * x0^2 * x1^2
  + -7535103181674351/2251799813685248 * x0 * x1^3
  + 2927370559145445/281474976710656 * x1^4
  + -1453967428688861/1125899906842624 * x0^5
  + 584483875850795/70368744177664 * x0^4 * x1
  + -5326261660583193/1125899906842624 * x0^3 * x1^2
  + 4674226052796107/2251799813685248 * x0^2 * x1^3
  + 8992716610373171/4503599627370496 * x0 * x1^4
  + -3204427114075639/281474976710656 * x1^5
  + -5847017347852465/4503599627370496 * x0^6
  + -1415320884512763/140737488355328 * x0^5 * x1
  + 8902398426677309/18014398509481984 * x0^4 * x1^2
  + -484539276897279/35184372088832 * x0^3 * x1^3
  + 4748558432861441/1125899906842624 * x0^2 * x1^4
  + -1831171817661319/140737488355328 * x0 * x1^5
  + -8820865862008017/1125899906842624 * x1^6
  + -2987178716437081/281474976710656 * x0^7
  + 2507357493525181/140737488355328 * x0^6 * x1
  + -4812450129954231/562949953421312 * x0^5 * x1^2
  + 2111551485487123/281474976710656 * x0^4 * x1^3
  + -8904203787431627/1125899906842624 * x0^3 * x1^4
  + 5329813653960479/562949953421312 * x0^2 * x1^5
  + -423137582010273/17592186044416 * x0 * x1^6
  + 5843292955830993/281474976710656 * x1^7
  + 8301381089096917/1125899906842624 * x0^8
  + -6505177955041863/562949953421312 * x0^7 * x1
  + 4789505221580079/562949953421312 * x0^6 * x1^2
  + 5143556837498033/4503599627370496 * x0^5 * x1^3
  + 4534183961225151/562949953421312 * x0^4 * x1^4
  + 8463059917196461/2251799813685248 * x0^3 * x1^5
  + 4909683602971917/1125899906842624 * x0^2 * x1^6
  + -1660412622302613/140737488355328 * x0 * x1^7
  + 2108629229089959/140737488355328 * x1^8.
  
Let ind0_sigma0 x0 x1 :=
  7620614590913555/1125899906842624 + -4986430697687727/281474976710656 * 
  x0 + 5146944124580077/281474976710656 * x1
  + 4934369417744563/281474976710656 * x0^2
  + -308088030753891/8796093022208 * x0 * x1
  + 393431512308707/17592186044416 * x1^2
  + -8158658809848877/562949953421312 * x0^3
  + 2558273932138561/140737488355328 * x0^2 * x1
  + -5465903921452071/281474976710656 * x0 * x1^2
  + 2399708508728131/140737488355328 * x1^3
  + 8929477401419283/562949953421312 * x0^4
  + -2478772945399449/140737488355328 * x0^3 * x1
  + -5353916057009015/562949953421312 * x0^2 * x1^2
  + -271822731303049/17592186044416 * x0 * x1^3
  + 1479922959069071/140737488355328 * x1^4
  + -1730058966015049/140737488355328 * x0^5
  + 5303215383177443/281474976710656 * x0^4 * x1
  + -1535096018918749/1125899906842624 * x0^3 * x1^2
  + -4710144679529001/4503599627370496 * x0^2 * x1^3
  + -1425927077127221/70368744177664 * x0 * x1^4
  + 1189018995907283/70368744177664 * x1^5
  + 1319521909207357/70368744177664 * x0^6
  + -1765867017874431/1125899906842624 * x0^5 * x1
  + -271804343143019/281474976710656 * x0^4 * x1^2
  + -3713532297682409/281474976710656 * x0^3 * x1^3
  + 6379652676841563/2251799813685248 * x0^2 * x1^4
  + -6020122527922295/1125899906842624 * x0 * x1^5
  + 6635229386135297/281474976710656 * x1^6
  + -4697278985463623/281474976710656 * x0^7
  + 5806476988096099/562949953421312 * x0^6 * x1
  + -6866740369323365/36028797018963968 * x0^5 * x1^2
  + 6245794913925251/1125899906842624 * x0^4 * x1^3
  + -429205872586561/70368744177664 * x0^3 * x1^4
  + -6588858877127391/288230376151711744 * x0^2 * x1^5
  + -7936356694875909/1125899906842624 * x0 * x1^6
  + 736348043790145/70368744177664 * x1^7
  + 6929151520465537/1125899906842624 * x0^8
  + -6661297274732877/562949953421312 * x0^7 * x1
  + 8265939323874821/1125899906842624 * x0^6 * x1^2
  + 8465277764291871/36028797018963968 * x0^5 * x1^3
  + 5094146954466393/562949953421312 * x0^4 * x1^4
  + 1857932663235181/2251799813685248 * x0^3 * x1^5
  + 5398139170737689/1125899906842624 * x0^2 * x1^6
  + -4670195433750109/281474976710656 * x0 * x1^7
  + 6634278782607529/562949953421312 * x1^8
  + -3879928443231963/281474976710656 * x0^9
  + 3813931498260835/562949953421312 * x0^8 * x1
  + 6031873291947693/1125899906842624 * x0^7 * x1^2
  + 6053998057277411/562949953421312 * x0^6 * x1^3
  + -1863684807657809/9007199254740992 * x0^5 * x1^4
  + 4397143346132095/2251799813685248 * x0^4 * x1^5
  + -6847230240715017/562949953421312 * x0^3 * x1^6
  + -4952618232757799/1125899906842624 * x0^2 * x1^7
  + -3510731253012117/281474976710656 * x0 * x1^8
  + 8039792875055227/562949953421312 * x1^9
  + 302611536073717/140737488355328 * x0^10
  + -5488199367588173/281474976710656 * x0^9 * x1
  + 1386950108163147/281474976710656 * x0^8 * x1^2
  + -2435009558357251/562949953421312 * x0^7 * x1^3
  + 5540238006396363/562949953421312 * x0^6 * x1^4
  + 2409409933938609/2251799813685248 * x0^5 * x1^5
  + 4921938420559637/1125899906842624 * x0^4 * x1^6
  + -3141440163678913/562949953421312 * x0^3 * x1^7
  + -2550836500265265/1125899906842624 * x0^2 * x1^8
  + -4267204880998129/281474976710656 * x0 * x1^9
  + -8439025213140119/4503599627370496 * x1^10
  + 420947440229885/35184372088832 * x0^11
  + 1480355032009517/70368744177664 * x0^10 * x1
  + 1966886546974935/1125899906842624 * x0^9 * x1^2
  + 3391489327444089/562949953421312 * x0^8 * x1^3
  + 6698949735847165/2251799813685248 * x0^7 * x1^4
  + 6430408087174395/1125899906842624 * x0^6 * x1^5
  + -2379529815554977/562949953421312 * x0^5 * x1^6
  + 4325115925433693/9007199254740992 * x0^4 * x1^7
  + -2474101223918743/281474976710656 * x0^3 * x1^8
  + -4008405488427929/562949953421312 * x0^2 * x1^9
  + -8408804640789315/281474976710656 * x0 * x1^10
  + 5926368701663933/562949953421312 * x1^11
  + 7493815976038685/562949953421312 * x0^12
  + -3666492653967529/140737488355328 * x0^11 * x1
  + -5102200207376009/562949953421312 * x0^10 * x1^2
  + -705389949366185/70368744177664 * x0^9 * x1^3
  + 6876721234930621/1125899906842624 * x0^8 * x1^4
  + -3325978545462897/281474976710656 * x0^7 * x1^5
  + 220384261779357/140737488355328 * x0^6 * x1^6
  + -3971150751111373/562949953421312 * x0^5 * x1^7
  + 3093807814690327/1125899906842624 * x0^4 * x1^8
  + -7135192978271115/281474976710656 * x0^3 * x1^9
  + -6719967637257119/1125899906842624 * x0^2 * x1^10
  + -7035425446657169/281474976710656 * x0 * x1^11
  + 4623677516731493/140737488355328 * x1^12
  + -7459182879933149/281474976710656 * x0^13
  + 1152323029825461/35184372088832 * x0^12 * x1
  + -4491168125246157/281474976710656 * x0^11 * x1^2
  + 5544342228705369/4503599627370496 * x0^10 * x1^3
  + -7849125099568933/281474976710656 * x0^9 * x1^4
  + -6349254442854399/4503599627370496 * x0^8 * x1^5
  + -7410580625576215/1125899906842624 * x0^7 * x1^6
  + 3488369617115001/140737488355328 * x0^6 * x1^7
  + -3970960444232237/1125899906842624 * x0^5 * x1^8
  + 3524238249427887/281474976710656 * x0^4 * x1^9
  + -3563165659216565/281474976710656 * x0^3 * x1^10
  + 1887134254734421/281474976710656 * x0^2 * x1^11
  + -3303076809342641/562949953421312 * x0 * x1^12
  + 3348064482574259/140737488355328 * x1^13
  + 2708030107433331/281474976710656 * x0^14
  + -8051761842824407/562949953421312 * x0^13 * x1
  + 8173786203551961/562949953421312 * x0^12 * x1^2
  + 130926369147987/140737488355328 * x0^11 * x1^3
  + 2983296499063771/281474976710656 * x0^10 * x1^4
  + 4443487962153073/2251799813685248 * x0^9 * x1^5
  + 4924994063395887/562949953421312 * x0^8 * x1^6
  + 3596189823012291/2251799813685248 * x0^7 * x1^7
  + 2039820212495289/140737488355328 * x0^6 * x1^8
  + -4271930357658547/2251799813685248 * x0^5 * x1^9
  + 8037066178702599/1125899906842624 * x0^4 * x1^10
  + 3934292244120927/2251799813685248 * x0^3 * x1^11
  + 1314629938463971/281474976710656 * x0^2 * x1^12
  + 7472210542211575/18014398509481984 * x0 * x1^13
  + 817387970540801/140737488355328 * x1^14.
  
Let ind1_sigma x0 x1 :=
  2338320362716181/4503599627370496 + 170895143261561/140737488355328 * 
  x0 + -1334308469612309/1125899906842624 * x1
  + 6475322148347831/1125899906842624 * x0^2
  + -8007429400214577/562949953421312 * x0 * x1
  + 6311997630288057/1125899906842624 * x1^2
  + 5017036204727215/281474976710656 * x0^3
  + -4901461061529183/140737488355328 * x0^2 * x1
  + 3283049513615901/140737488355328 * x0 * x1^2
  + -4272675548656317/562949953421312 * x1^3
  + 5170193617380397/281474976710656 * x0^4
  + -8408053214241299/281474976710656 * x0^3 * x1
  + 7748404557588205/281474976710656 * x0^2 * x1^2
  + 4696029196606179/4503599627370496 * x0 * x1^3
  + 1100783048083211/562949953421312 * x1^4
  + -3155507780834083/562949953421312 * x0^5
  + -1223496245709139/140737488355328 * x0^4 * x1
  + 188945334925703/70368744177664 * x0^3 * x1^2
  + 7643103442720209/562949953421312 * x0^2 * x1^3
  + 5828715417326073/562949953421312 * x0 * x1^4
  + -1084319754266217/140737488355328 * x1^5
  + -5071378893987895/1125899906842624 * x0^6
  + -2880823972880685/140737488355328 * x0^5 * x1
  + 3647130553137189/281474976710656 * x0^4 * x1^2
  + -5228142881307255/562949953421312 * x0^3 * x1^3
  + 6272600586435545/281474976710656 * x0^2 * x1^4
  + -8937193731781895/140737488355328 * x0 * x1^5
  + 6870247991454963/281474976710656 * x1^6
  + 1353431175266409/70368744177664 * x0^7
  + -1410307668300799/35184372088832 * x0^6 * x1
  + 3133188597581983/70368744177664 * x0^5 * x1^2
  + -4660025706676615/140737488355328 * x0^4 * x1^3
  + 2220474079272055/70368744177664 * x0^3 * x1^4
  + -8488324680134189/140737488355328 * x0^2 * x1^5
  + 976546138170571/17592186044416 * x0 * x1^6
  + -6134087757417489/281474976710656 * x1^7
  + 7237205075783299/562949953421312 * x0^8
  + -5779154625373195/281474976710656 * x0^7 * x1
  + 6903109031305041/281474976710656 * x0^6 * x1^2
  + -8677567836727659/562949953421312 * x0^5 * x1^3
  + 668840282457931/35184372088832 * x0^4 * x1^4
  + -1025273017801143/70368744177664 * x0^3 * x1^5
  + 3556010924321357/140737488355328 * x0^2 * x1^6
  + -7703210527403321/562949953421312 * x0 * x1^7
  + 876274339177965/140737488355328 * x1^8.
  
Let ind1_sigma1 x0 x1 :=
  4523080467996403/562949953421312 + 8543669452391873/281474976710656 * 
  x0 + -4550803079519621/140737488355328 * x1
  + 7984454900598739/140737488355328 * x0^2
  + -6442097208983215/70368744177664 * x0 * x1
  + 6914927312198993/140737488355328 * x1^2
  + 7892638963268963/140737488355328 * x0^3
  + -3171889583718873/35184372088832 * x0^2 * x1
  + 5951895634597121/70368744177664 * x0 * x1^2
  + -1244566344806537/35184372088832 * x1^3
  + 5167798363183691/281474976710656 * x0^4
  + -2287459969589041/35184372088832 * x0^3 * x1
  + 1172785912873877/562949953421312 * x0^2 * x1^2
  + -5538967029047781/140737488355328 * x0 * x1^3
  + 4685164142307045/140737488355328 * x1^4
  + 2860453531895833/140737488355328 * x0^5
  + -268897666904475/4398046511104 * x0^4 * x1
  + -6236389766045515/281474976710656 * x0^3 * x1^2
  + 6411909682484831/562949953421312 * x0^2 * x1^3
  + 8481682460541245/140737488355328 * x0 * x1^4
  + -1472577652998239/35184372088832 * x1^5
  + 4527508347207127/70368744177664 * x0^6
  + -8026619312356537/281474976710656 * x0^5 * x1
  + 424393908148421/17592186044416 * x0^4 * x1^2
  + -199463235254539/8796093022208 * x0^3 * x1^3
  + 4074027659643233/140737488355328 * x0^2 * x1^4
  + -3294074887868121/70368744177664 * x0 * x1^5
  + 2803986116969083/70368744177664 * x1^6
  + 5466284374823473/140737488355328 * x0^7
  + -7307879836701819/281474976710656 * x0^6 * x1
  + 5062874257191751/562949953421312 * x0^5 * x1^2
  + -4477418413163969/281474976710656 * x0^4 * x1^3
  + 2135519145601935/70368744177664 * x0^3 * x1^4
  + 4893585669360345/562949953421312 * x0^2 * x1^5
  + 2685203367029361/140737488355328 * x0 * x1^6
  + -6916923033728153/140737488355328 * x1^7
  + 6360799779823757/281474976710656 * x0^8
  + -8957074416903825/281474976710656 * x0^7 * x1
  + 571870677822817/70368744177664 * x0^6 * x1^2
  + 2789894741832287/281474976710656 * x0^5 * x1^3
  + 2794159131619807/140737488355328 * x0^4 * x1^4
  + 866448303582609/281474976710656 * x0^3 * x1^5
  + 5042312169720643/1125899906842624 * x0^2 * x1^6
  + -2608775272336647/70368744177664 * x0 * x1^7
  + 2460753342842523/70368744177664 * x1^8
  + 6949812695732829/140737488355328 * x0^9
  + -3467679478992855/140737488355328 * x0^8 * x1
  + 2977228473100339/140737488355328 * x0^7 * x1^2
  + -5237437125092013/281474976710656 * x0^6 * x1^3
  + 6264395762914383/281474976710656 * x0^5 * x1^4
  + -1461132918781177/140737488355328 * x0^4 * x1^5
  + 5580301904376667/281474976710656 * x0^3 * x1^6
  + -1292427120991889/35184372088832 * x0^2 * x1^7
  + 7504547819000203/281474976710656 * x0 * x1^8
  + 1764743535616655/562949953421312 * x1^9
  + -19140941556345/2199023255552 * x0^10
  + -3569590743281847/70368744177664 * x0^9 * x1
  + 2056896119773707/281474976710656 * x0^8 * x1^2
  + -1417354442005561/562949953421312 * x0^7 * x1^3
  + 8415520488692043/281474976710656 * x0^6 * x1^4
  + 8043634089150591/4503599627370496 * x0^5 * x1^5
  + 7795419612600907/281474976710656 * x0^4 * x1^6
  + 7742083395027841/1125899906842624 * x0^3 * x1^7
  + -6777647799733629/2251799813685248 * x0^2 * x1^8
  + -6779093671853945/140737488355328 * x0 * x1^9
  + 4020568488081751/562949953421312 * x1^10
  + -4339695838503533/140737488355328 * x0^11
  + -2434679774375751/35184372088832 * x0^10 * x1
  + -8916957392746721/562949953421312 * x0^9 * x1^2
  + -7988581915293399/562949953421312 * x0^8 * x1^3
  + -8837147645621569/2251799813685248 * x0^7 * x1^4
  + -6236853610124821/562949953421312 * x0^6 * x1^5
  + -4910883699099545/4503599627370496 * x0^5 * x1^6
  + -4571624101606605/281474976710656 * x0^4 * x1^7
  + 1195860604316785/70368744177664 * x0^3 * x1^8
  + 1201185495518211/70368744177664 * x0^2 * x1^9
  + 7081568292783419/70368744177664 * x0 * x1^10
  + -6418990188620223/140737488355328 * x1^11
  + 3746725655256993/70368744177664 * x0^12
  + -2997830225374587/35184372088832 * x0^11 * x1
  + 5878013693852599/1125899906842624 * x0^10 * x1^2
  + -3059501672994391/140737488355328 * x0^9 * x1^3
  + 1551730207238241/70368744177664 * x0^8 * x1^4
  + -365576005855197/8796093022208 * x0^7 * x1^5
  + 927792262465767/2251799813685248 * x0^6 * x1^6
  + -7176151387715401/140737488355328 * x0^5 * x1^7
  + 2083224242909987/70368744177664 * x0^4 * x1^8
  + -5577645703378477/140737488355328 * x0^3 * x1^9
  + 3311682110335867/140737488355328 * x0^2 * x1^10
  + -2789473991842659/35184372088832 * x0 * x1^11
  + 6397482403319767/140737488355328 * x1^12
  + 2538334061110823/35184372088832 * x0^13
  + -2645707927344327/35184372088832 * x0^12 * x1
  + 2750650127120735/70368744177664 * x0^11 * x1^2
  + 1864293893103305/1125899906842624 * x0^10 * x1^3
  + 2182485392179773/35184372088832 * x0^9 * x1^4
  + -3793523125675109/140737488355328 * x0^8 * x1^5
  + 8717214854101441/281474976710656 * x0^7 * x1^6
  + -7766177800345071/281474976710656 * x0^6 * x1^7
  + 7060375156335091/281474976710656 * x0^5 * x1^8
  + -3611973365467443/70368744177664 * x0^4 * x1^9
  + 3520108669336057/1125899906842624 * x0^3 * x1^10
  + -2291200303556849/70368744177664 * x0^2 * x1^11
  + 3411348360488957/140737488355328 * x0 * x1^12
  + -2644386195022467/140737488355328 * x1^13
  + 3100166331669239/140737488355328 * x0^14
  + -1774022312114581/70368744177664 * x0^13 * x1
  + 357253041868657/17592186044416 * x0^12 * x1^2
  + 7876423940686885/2251799813685248 * x0^11 * x1^3
  + 8378427403924347/281474976710656 * x0^10 * x1^4
  + -7894146720819499/2251799813685248 * x0^9 * x1^5
  + 8252482355714443/562949953421312 * x0^8 * x1^6
  + -8251835020169317/1125899906842624 * x0^7 * x1^7
  + 4445865336479785/281474976710656 * x0^6 * x1^8
  + 946480610102203/281474976710656 * x0^5 * x1^9
  + 1535093211114103/70368744177664 * x0^4 * x1^10
  + 1830918570734765/281474976710656 * x0^3 * x1^11
  + 5557006951352869/562949953421312 * x0^2 * x1^12
  + -4691451529203469/2251799813685248 * x0 * x1^13
  + 6636101055145181/2251799813685248 * x1^14.
  
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
