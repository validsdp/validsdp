From mathcomp Require Import ssreflect.
Require Import Reals.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

(* Attempt to prove that p >= 0 with p below is an
 * inductive invariant, for the program
 *
x1 = rand(0.9, 1.1);
x2 = rand(0, 0.2);
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

(* initial condition 0.9 <= x1 <= 1.1 encoded as (x1 - 0.9)*(1.1 - x1) (>= 0) *)
Let pI1 (x0 x1 : R) := (x0 - 9 / 10) * (11 / 10 - x0).
(* initial condition 0 <= x2 <= 0.2 *)
Let pI2 (x0 x1 : R) := x1 * (2 / 10 - x1).
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
  11724193731320667/9007199254740992
  + 5363509247042945/1152921504606846976 * x0
  + 6697439732049177/576460752303423488 * x1
  + -2538921022898767/1125899906842624 * x0^2
  + -158622508368809/140737488355328 * x0 * x1
  + -2153763193131945/1125899906842624 * x1^2
  + 1261645552858613/562949953421312 * x0^3
  + 6720054296628647/4503599627370496 * x0^2 * x1
  + 2787072307930385/2251799813685248 * x0 * x1^2
  + 8841768526834515/18014398509481984 * x1^3
  + -5548502078413043/4503599627370496 * x0^4
  + -6352973998063161/36028797018963968 * x0^3 * x1
  + 7355223013039007/2251799813685248 * x0^2 * x1^2
  + 7116910381908169/4503599627370496 * x0 * x1^3
  + -575281306133581/2251799813685248 * x1^4
  + 368553632223861/2251799813685248 * x0^5
  + -3554591502428539/9007199254740992 * x0^4 * x1
  + -1808382380122255/1125899906842624 * x0^3 * x1^2
  + -2806808898838291/2251799813685248 * x0^2 * x1^3
  + -36108254505365/9007199254740992 * x0 * x1^4
  + 843150192031495/1125899906842624 * x1^5
  + -8782095016692183/1152921504606846976 * x0^6
  + 6544640190593663/288230376151711744 * x0^5 * x1
  + 3334276451595169/144115188075855872 * x0^4 * x1^2
  + -4918224622344679/36028797018963968 * x0^3 * x1^3
  + -4677603389160537/9007199254740992 * x0^2 * x1^4
  + -1667155699402415/2251799813685248 * x0 * x1^5
  + -4984497334918313/9007199254740992 * x1^6.
  
Let init_sigma1 x0 x1 :=
  4520406430719581/2251799813685248 + 1928284961919501/2251799813685248 * 
  x0 + 2669078052883095/576460752303423488 * x1
  + 5995295453047125/2251799813685248 * x0^2
  + 2108070266934955/9007199254740992 * x0 * x1
  + 1498624248720199/1125899906842624 * x1^2
  + 2736955711777207/2251799813685248 * x0^3
  + 3921288309368391/36028797018963968 * x0^2 * x1
  + 8394012508501267/18014398509481984 * x0 * x1^2
  + 4367362257923493/36028797018963968 * x1^3
  + 5399133090884855/2251799813685248 * x0^4
  + 7486131096858869/144115188075855872 * x0^3 * x1
  + 4751969335332643/4503599627370496 * x0^2 * x1^2
  + -5532464661262431/72057594037927936 * x0 * x1^3
  + 3795425776038587/2251799813685248 * x1^4.
  
Let init_sigma2 x0 x1 :=
  2718159694300061/2251799813685248 + -2100492451181023/2251799813685248 * 
  x0 + -1841556919118149/9007199254740992 * x1
  + -8480389496880317/72057594037927936 * x0^2
  + -4980108502690409/18014398509481984 * x0 * x1
  + 7470395322766607/4503599627370496 * x1^2
  + -587121989648959/562949953421312 * x0^3
  + -2101476419335023/36028797018963968 * x0^2 * x1
  + 3542372622067465/4503599627370496 * x0 * x1^2
  + -5206984409910579/144115188075855872 * x1^3
  + 8471232966932981/9007199254740992 * x0^4
  + -1518777957440863/18014398509481984 * x0^3 * x1
  + 7659377864839141/4503599627370496 * x0^2 * x1^2
  + 8195615872877453/36028797018963968 * x0 * x1^3
  + 2864670593571683/1125899906842624 * x1^4.
  
Let ind0_sigma x0 x1 :=
  3084781268841947/9007199254740992
  + -5295441113169607/18014398509481984 * x0
  + -3591103061437905/18014398509481984 * x1
  + 2572958165746223/9007199254740992 * x0^2
  + 7322929924777553/1152921504606846976 * x0 * x1
  + 5945589364630011/18014398509481984 * x1^2
  + -8188463895852757/18014398509481984 * x0^3
  + 4843569473390095/18014398509481984 * x0^2 * x1
  + -4904212826160467/9007199254740992 * x0 * x1^2
  + -2949848883192545/9007199254740992 * x1^3
  + 7898979905152099/18014398509481984 * x0^4
  + 33635785511621/281474976710656 * x0^3 * x1
  + 6316570708120673/36028797018963968 * x0^2 * x1^2
  + 6716196470715877/18014398509481984 * x0 * x1^3
  + 6291901269116755/18014398509481984 * x1^4
  + -4361734974386707/9007199254740992 * x0^5
  + 6900160702186045/288230376151711744 * x0^4 * x1
  + -2827822930348189/4503599627370496 * x0^3 * x1^2
  + 4643812455046253/36028797018963968 * x0^2 * x1^3
  + -916347848112307/2251799813685248 * x0 * x1^4
  + -6262949957592299/18014398509481984 * x1^5
  + 2388382351920437/4503599627370496 * x0^6
  + -8499486501942339/36028797018963968 * x0^5 * x1
  + 4465354402506711/9007199254740992 * x0^4 * x1^2
  + 2817955585644795/18014398509481984 * x0^3 * x1^3
  + 3983094884566949/18014398509481984 * x0^2 * x1^4
  + 5741579192141133/144115188075855872 * x0 * x1^5
  + 5750261110460251/18014398509481984 * x1^6
  + -5440565271613269/9007199254740992 * x0^7
  + 4508009660235533/72057594037927936 * x0^6 * x1
  + -8575788862080259/36028797018963968 * x0^5 * x1^2
  + 4760544778619281/36028797018963968 * x0^4 * x1^3
  + -1939999528099913/4503599627370496 * x0^3 * x1^4
  + 6542726240169675/18014398509481984 * x0^2 * x1^5
  + -3681524914098877/9007199254740992 * x0 * x1^6
  + -1410256406583167/2251799813685248 * x1^7
  + 8707882788582451/36028797018963968 * x0^8
  + -6109882051050355/72057594037927936 * x0^7 * x1
  + 6219845489459117/9007199254740992 * x0^6 * x1^2
  + 1159661719484379/144115188075855872 * x0^5 * x1^3
  + 2997627899241659/4503599627370496 * x0^4 * x1^4
  + -7221401122965483/288230376151711744 * x0^3 * x1^5
  + 731502594776601/1125899906842624 * x0^2 * x1^6
  + -1847795153704597/18014398509481984 * x0 * x1^7
  + 1691269221949007/4503599627370496 * x1^8
  + -7141490558706257/9007199254740992 * x0^9
  + -7707305221728265/288230376151711744 * x0^8 * x1
  + 7245279859976949/72057594037927936 * x0^7 * x1^2
  + -8194602607305895/36028797018963968 * x0^6 * x1^3
  + -6649251673285225/72057594037927936 * x0^5 * x1^4
  + 3370017771507617/36028797018963968 * x0^4 * x1^5
  + -2847653510491553/9007199254740992 * x0^3 * x1^6
  + 4420448495659271/18014398509481984 * x0^2 * x1^7
  + -5361804229829005/9007199254740992 * x0 * x1^8
  + -873246834944279/2251799813685248 * x1^9
  + 5429422059245637/9007199254740992 * x0^10
  + -7710851049579455/72057594037927936 * x0^9 * x1
  + 1012715084280823/1125899906842624 * x0^8 * x1^2
  + -8013457472343467/288230376151711744 * x0^7 * x1^3
  + 1164739522775903/2251799813685248 * x0^6 * x1^4
  + -4084182610951355/288230376151711744 * x0^5 * x1^5
  + 2768949317187691/9007199254740992 * x0^4 * x1^6
  + 2285214846515953/36028797018963968 * x0^3 * x1^7
  + 3120952399544721/4503599627370496 * x0^2 * x1^8
  + -5052481478528741/18014398509481984 * x0 * x1^9
  + 4579361309134189/4503599627370496 * x1^10
  + -1032515854099289/2251799813685248 * x0^11
  + 5088501143916647/36028797018963968 * x0^10 * x1
  + -1650201879000483/18014398509481984 * x0^9 * x1^2
  + -1339058672739789/9007199254740992 * x0^8 * x1^3
  + -3282249452733421/9007199254740992 * x0^7 * x1^4
  + -4753179267775525/36028797018963968 * x0^6 * x1^5
  + -6188285689230873/36028797018963968 * x0^5 * x1^6
  + -2072079877684731/9007199254740992 * x0^4 * x1^7
  + -6372919074469819/72057594037927936 * x0^3 * x1^8
  + -3214611024452113/72057594037927936 * x0^2 * x1^9
  + -6085889597083451/18014398509481984 * x0 * x1^10
  + -5111626394514277/18014398509481984 * x1^11
  + 2596744614407277/2251799813685248 * x0^12
  + -6351900002536851/36028797018963968 * x0^11 * x1
  + 4536916858748231/4503599627370496 * x0^10 * x1^2
  + -2958828698626907/18014398509481984 * x0^9 * x1^3
  + 1046621828667919/1125899906842624 * x0^8 * x1^4
  + -3019972003019113/9007199254740992 * x0^7 * x1^5
  + 8969427947220077/9007199254740992 * x0^6 * x1^6
  + -4308861843164495/36028797018963968 * x0^5 * x1^7
  + 1922145540996245/2251799813685248 * x0^4 * x1^8
  + -6143602246799011/72057594037927936 * x0^3 * x1^9
  + 1210974032087487/1125899906842624 * x0^2 * x1^10
  + -2882008915376959/9007199254740992 * x0 * x1^11
  + 6237971065263543/4503599627370496 * x1^12.
  
Let ind0_sigma0 x0 x1 :=
  2785989264256669/9007199254740992 + 483124896472275/18014398509481984 * 
  x0 + 6768394332611763/4611686018427387904 * x1
  + 7294301800195187/18014398509481984 * x0^2
  + -7744377861962907/144115188075855872 * x0 * x1
  + 2949370665677863/18014398509481984 * x1^2
  + -1916993265872771/4503599627370496 * x0^3
  + -153404758131459/281474976710656 * x0^2 * x1
  + -7934013049402969/36028797018963968 * x0 * x1^2
  + -2841398605369111/18014398509481984 * x1^3
  + 1103915987298479/4503599627370496 * x0^4
  + 846940259829633/18014398509481984 * x0^3 * x1
  + 1166388730379597/1125899906842624 * x0^2 * x1^2
  + 118887432979895/2251799813685248 * x0 * x1^3
  + 2675417479936537/36028797018963968 * x1^4
  + -7028588855113225/9007199254740992 * x0^5
  + 462514487416663/9007199254740992 * x0^4 * x1
  + 7570061459627441/18014398509481984 * x0^3 * x1^2
  + 610823816293625/18014398509481984 * x0^2 * x1^3
  + 2238285514574523/18014398509481984 * x0 * x1^4
  + -7210024773349381/18014398509481984 * x1^5
  + 7944127340727523/18014398509481984 * x0^6
  + 5158252854879077/18014398509481984 * x0^5 * x1
  + 6658180274559799/4503599627370496 * x0^4 * x1^2
  + 8045422427976953/18014398509481984 * x0^3 * x1^3
  + 6255806795660061/4503599627370496 * x0^2 * x1^4
  + 2952224857675545/9007199254740992 * x0 * x1^5
  + 8530130329849367/36028797018963968 * x1^6
  + -2449207462784259/4503599627370496 * x0^7
  + 3611073317036895/9007199254740992 * x0^6 * x1
  + 494519286171743/562949953421312 * x0^5 * x1^2
  + 3338586257257895/4503599627370496 * x0^4 * x1^3
  + 8179340083443741/9007199254740992 * x0^3 * x1^4
  + 5295745006486453/9007199254740992 * x0^2 * x1^5
  + 1703620044930155/4503599627370496 * x0 * x1^6
  + -4814110974248861/18014398509481984 * x1^7
  + 6030336407730863/9007199254740992 * x0^8
  + 8346559150421165/18014398509481984 * x0^7 * x1
  + 3918207432405141/2251799813685248 * x0^6 * x1^2
  + 6659103543371493/9007199254740992 * x0^5 * x1^3
  + 7791153558779541/4503599627370496 * x0^4 * x1^4
  + 3142548138699067/4503599627370496 * x0^3 * x1^5
  + 3717655657889789/2251799813685248 * x0^2 * x1^6
  + 8463616584022903/18014398509481984 * x0 * x1^7
  + 2888621763802757/4503599627370496 * x1^8
  + -2245933856845479/9007199254740992 * x0^9
  + 292834178004241/562949953421312 * x0^8 * x1
  + 2842856719121967/2251799813685248 * x0^7 * x1^2
  + 7212722826837585/9007199254740992 * x0^6 * x1^3
  + 5377640600775073/4503599627370496 * x0^5 * x1^4
  + 8251603404064541/9007199254740992 * x0^4 * x1^5
  + 1083476049910897/1125899906842624 * x0^3 * x1^6
  + 8287931796660401/9007199254740992 * x0^2 * x1^7
  + 8653388329900013/18014398509481984 * x0 * x1^8
  + 4641423481103537/1152921504606846976 * x1^9
  + 4709754966717383/4503599627370496 * x0^10
  + 1284598028982287/2251799813685248 * x0^9 * x1
  + 1051010582538943/562949953421312 * x0^8 * x1^2
  + 1006006683785025/1125899906842624 * x0^7 * x1^3
  + 7253332024624231/4503599627370496 * x0^6 * x1^4
  + 2326723007092149/2251799813685248 * x0^5 * x1^5
  + 209819579430253/140737488355328 * x0^4 * x1^6
  + 4051451639593327/4503599627370496 * x0^3 * x1^7
  + 7061514102634099/4503599627370496 * x0^2 * x1^8
  + 2559635221247331/4503599627370496 * x0 * x1^9
  + 2222629129564443/2251799813685248 * x1^10
  + 8556022295266311/36028797018963968 * x0^11
  + 1507402371158103/2251799813685248 * x0^10 * x1
  + 5712983637512377/4503599627370496 * x0^9 * x1^2
  + 4694114435334861/4503599627370496 * x0^8 * x1^3
  + 5512952113718031/4503599627370496 * x0^7 * x1^4
  + 4601807901378649/4503599627370496 * x0^6 * x1^5
  + 2683545696687739/2251799813685248 * x0^5 * x1^6
  + 4162536853891625/4503599627370496 * x0^4 * x1^7
  + 5218206650399775/4503599627370496 * x0^3 * x1^8
  + 3781334642685015/4503599627370496 * x0^2 * x1^9
  + 6094808740809767/9007199254740992 * x0 * x1^10
  + 1477044776257665/9007199254740992 * x1^11
  + 5686825495041147/4503599627370496 * x0^12
  + 1398364010572793/2251799813685248 * x0^11 * x1
  + 8629654831939675/4503599627370496 * x0^10 * x1^2
  + 2163137885380943/2251799813685248 * x0^9 * x1^3
  + 8201050331271885/4503599627370496 * x0^8 * x1^4
  + 8412580043737561/9007199254740992 * x0^7 * x1^5
  + 982371718602951/562949953421312 * x0^6 * x1^6
  + 8419560897736619/9007199254740992 * x0^5 * x1^7
  + 1752827582199489/1125899906842624 * x0^4 * x1^8
  + 4224695982717091/4503599627370496 * x0^3 * x1^9
  + 6640238431235239/4503599627370496 * x0^2 * x1^10
  + 1465919061553031/2251799813685248 * x0 * x1^11
  + 1239665906911697/1125899906842624 * x1^12
  + 8530488459034417/18014398509481984 * x0^13
  + 2874417524922311/4503599627370496 * x0^12 * x1
  + 6673604456807171/4503599627370496 * x0^11 * x1^2
  + 8554864520283801/9007199254740992 * x0^10 * x1^3
  + 6524561462469349/4503599627370496 * x0^9 * x1^4
  + 4585497169630587/4503599627370496 * x0^8 * x1^5
  + 5459840131560647/4503599627370496 * x0^7 * x1^6
  + 1190806580813173/1125899906842624 * x0^6 * x1^7
  + 4519950382959455/4503599627370496 * x0^5 * x1^8
  + 8696640814414795/9007199254740992 * x0^4 * x1^9
  + 4234442706032487/4503599627370496 * x0^3 * x1^10
  + 3602174233927685/4503599627370496 * x0^2 * x1^11
  + 5775800636604121/9007199254740992 * x0 * x1^12
  + 3521686853129273/18014398509481984 * x1^13
  + 5346932017644497/2251799813685248 * x0^14
  + 5743283600389103/9007199254740992 * x0^13 * x1
  + 1439103322030147/562949953421312 * x0^12 * x1^2
  + 8542107481059289/9007199254740992 * x0^11 * x1^3
  + 4680535036288915/2251799813685248 * x0^10 * x1^4
  + 2345130766568123/2251799813685248 * x0^9 * x1^5
  + 8112867392584043/4503599627370496 * x0^8 * x1^6
  + 8727413556513323/9007199254740992 * x0^7 * x1^7
  + 3894595489038339/2251799813685248 * x0^6 * x1^8
  + 955282099833507/1125899906842624 * x0^5 * x1^9
  + 7739964901452335/4503599627370496 * x0^4 * x1^10
  + 3418136450993305/4503599627370496 * x0^3 * x1^11
  + 8314154286307159/4503599627370496 * x0^2 * x1^12
  + 165183137568189/281474976710656 * x0 * x1^13
  + 8546761546708217/4503599627370496 * x1^14
  + 5236494147219105/9007199254740992 * x0^15
  + 8541806280738583/18014398509481984 * x0^14 * x1
  + 2739376381537197/2251799813685248 * x0^13 * x1^2
  + 1002394009612213/1125899906842624 * x0^12 * x1^3
  + 2308211995390141/2251799813685248 * x0^11 * x1^4
  + 4429669051784689/4503599627370496 * x0^10 * x1^5
  + 8753436966019163/9007199254740992 * x0^9 * x1^6
  + 8229245599474437/9007199254740992 * x0^8 * x1^7
  + 1064510890875817/1125899906842624 * x0^7 * x1^8
  + 7606796926110587/9007199254740992 * x0^6 * x1^9
  + 7144906902511815/9007199254740992 * x0^5 * x1^10
  + 1784239500542043/2251799813685248 * x0^4 * x1^11
  + 22788250407969/35184372088832 * x0^3 * x1^12
  + 5913344113592967/9007199254740992 * x0^2 * x1^13
  + 7612944961241207/18014398509481984 * x0 * x1^14
  + 730324811291431/2251799813685248 * x1^15
  + 6792723448414373/2251799813685248 * x0^16
  + 3704481929831877/9007199254740992 * x0^15 * x1
  + 2699557769721173/1125899906842624 * x0^14 * x1^2
  + 3017839498158649/4503599627370496 * x0^13 * x1^3
  + 2359374710842203/1125899906842624 * x0^12 * x1^4
  + 3079178051694023/4503599627370496 * x0^11 * x1^5
  + 4563873750476011/2251799813685248 * x0^10 * x1^6
  + 3171584693636669/4503599627370496 * x0^9 * x1^7
  + 4706918902644211/2251799813685248 * x0^8 * x1^8
  + 6137376012338725/9007199254740992 * x0^7 * x1^9
  + 8459089256133537/4503599627370496 * x0^6 * x1^10
  + 2514663527812169/4503599627370496 * x0^5 * x1^11
  + 8418401522791161/4503599627370496 * x0^4 * x1^12
  + 7970981955711721/18014398509481984 * x0^3 * x1^13
  + 8565375724101069/4503599627370496 * x0^2 * x1^14
  + 6170117368992347/36028797018963968 * x0 * x1^15
  + 322826671847981/140737488355328 * x1^16.
  
Let ind1_sigma x0 x1 :=
  6602605542043277/35184372088832 + -5152101744781667/8796093022208 * 
  x0 + -184944724588473/2199023255552 * x1
  + 3068015831420181/4398046511104 * x0^2
  + 6606015208325743/17592186044416 * x0 * x1
  + -6323777639115219/35184372088832 * x1^2
  + -3134881278694285/4398046511104 * x0^3
  + -900982715762863/2199023255552 * x0^2 * x1
  + -1967174104106163/281474976710656 * x0 * x1^2
  + -1896219703798031/8796093022208 * x1^3
  + 4671843819550835/4398046511104 * x0^4
  + -228015697051115/549755813888 * x0^3 * x1
  + 8450880888272439/8796093022208 * x0^2 * x1^2
  + 2208063739203889/4398046511104 * x0 * x1^3
  + 4761048825843909/17592186044416 * x1^4
  + -510438068768057/549755813888 * x0^5
  + 2955926448821941/4398046511104 * x0^4 * x1
  + -7034926153118767/8796093022208 * x0^3 * x1^2
  + -3041069782895659/17592186044416 * x0^2 * x1^3
  + -6019830436873121/8796093022208 * x0 * x1^4
  + 6758818830178725/17592186044416 * x1^5
  + 6092468507488351/35184372088832 * x0^6
  + 1542613088156197/2199023255552 * x0^5 * x1
  + 7258855185920135/70368744177664 * x0^4 * x1^2
  + -6605935719849507/35184372088832 * x0^3 * x1^3
  + 5548771286647927/17592186044416 * x0^2 * x1^4
  + -3748437011830031/35184372088832 * x0 * x1^5
  + 4767041605699079/140737488355328 * x1^6
  + -7694605808213987/70368744177664 * x0^7
  + -5582613215131571/8796093022208 * x0^6 * x1
  + -3907350359331689/4398046511104 * x0^5 * x1^2
  + 8751859648761719/140737488355328 * x0^4 * x1^3
  + 7357330366709639/140737488355328 * x0^3 * x1^4
  + -2834673636861597/2199023255552 * x0^2 * x1^5
  + 5470757025676509/70368744177664 * x0 * x1^6
  + -4720197778058145/8796093022208 * x1^7
  + 640753682706663/549755813888 * x0^8
  + -1639471938689815/1099511627776 * x0^7 * x1
  + 8012256932159465/8796093022208 * x0^6 * x1^2
  + -5203668291706337/17592186044416 * x0^5 * x1^3
  + 3709282487252169/4398046511104 * x0^4 * x1^4
  + 6321050857825755/35184372088832 * x0^3 * x1^5
  + 6059880336533303/35184372088832 * x0^2 * x1^6
  + 7449487294739849/8796093022208 * x0 * x1^7
  + -5896670342291143/17592186044416 * x1^8
  + -4822631906837223/2199023255552 * x0^9
  + 4880334805280295/4398046511104 * x0^8 * x1
  + -2333703025515035/4398046511104 * x0^7 * x1^2
  + 5088380754415785/8796093022208 * x0^6 * x1^3
  + -3303688346148681/2199023255552 * x0^5 * x1^4
  + 8767192671676873/4398046511104 * x0^4 * x1^5
  + -3081170079036817/2199023255552 * x0^3 * x1^6
  + 5541374020406203/70368744177664 * x0^2 * x1^7
  + -5741627947725391/17592186044416 * x0 * x1^8
  + 2937340500627861/17592186044416 * x1^9
  + 8879458261217877/4398046511104 * x0^10
  + 6073401919406463/4398046511104 * x0^9 * x1
  + 3312885235155209/2199023255552 * x0^8 * x1^2
  + -736076350673403/2199023255552 * x0^7 * x1^3
  + 2931960858661969/2199023255552 * x0^6 * x1^4
  + -507901440905325/1099511627776 * x0^5 * x1^5
  + 4177279152325681/2199023255552 * x0^4 * x1^6
  + -8581791676427283/8796093022208 * x0^3 * x1^7
  + 8510719334064061/4398046511104 * x0^2 * x1^8
  + 1285050218479555/4398046511104 * x0 * x1^9
  + 2028391452910465/2199023255552 * x1^10
  + -4257824240492925/4398046511104 * x0^11
  + -7471888756687329/4398046511104 * x0^10 * x1
  + -6655803502295835/4398046511104 * x0^9 * x1^2
  + 2429296156932553/35184372088832 * x0^8 * x1^3
  + -2146900035484731/2199023255552 * x0^7 * x1^4
  + -4968486112431101/4398046511104 * x0^6 * x1^5
  + -7254144372383935/8796093022208 * x0^5 * x1^6
  + -5281956035705547/562949953421312 * x0^4 * x1^7
  + -4165785708040675/2199023255552 * x0^3 * x1^8
  + 6645402454307809/17592186044416 * x0^2 * x1^9
  + -3384089876233077/2199023255552 * x0 * x1^10
  + -3304865442856465/4398046511104 * x1^11
  + 6818260055987783/35184372088832 * x0^12
  + 4351812559989285/8796093022208 * x0^11 * x1
  + 1884209424878077/4398046511104 * x0^10 * x1^2
  + -7589725566380631/281474976710656 * x0^9 * x1^3
  + 3423534407264735/8796093022208 * x0^8 * x1^4
  + 5004134931212959/8796093022208 * x0^7 * x1^5
  + -5504804415204863/70368744177664 * x0^6 * x1^6
  + 6757495119775669/35184372088832 * x0^5 * x1^7
  + 3885813672390443/4398046511104 * x0^4 * x1^8
  + -5004056220120859/17592186044416 * x0^3 * x1^9
  + 4597139924048417/17592186044416 * x0^2 * x1^10
  + 4031563005896295/8796093022208 * x0 * x1^11
  + 7263065860267573/35184372088832 * x1^12.
  
Let ind1_sigma1 x0 x1 :=
  978540170124443/2199023255552 + -411047178075021/274877906944 * x0
  + -4706841534177227/140737488355328 * x1
  + 2195212828345935/1099511627776 * x0^2
  + 7575315391079151/17592186044416 * x0 * x1
  + -3158323985066343/8796093022208 * x1^2
  + -6085842194477163/4398046511104 * x0^3
  + -7200738004316093/8796093022208 * x0^2 * x1
  + 165704683528145/274877906944 * x0 * x1^2
  + -652669967762159/2199023255552 * x1^3
  + 101767958334791/137438953472 * x0^4
  + -2101193272960171/17592186044416 * x0^3 * x1
  + 3553417685472001/8796093022208 * x0^2 * x1^2
  + 3143391064781685/4398046511104 * x0 * x1^3
  + -4654986192872103/140737488355328 * x1^4
  + -6589828509309961/8796093022208 * x0^5
  + 5360227921516877/4398046511104 * x0^4 * x1
  + -2920399416664551/2199023255552 * x0^3 * x1^2
  + -7664797134021627/17592186044416 * x0^2 * x1^3
  + -5908226084929009/35184372088832 * x0 * x1^4
  + 3407937377035227/140737488355328 * x1^5
  + 6759769354706709/8796093022208 * x0^6
  + -6484758785160421/17592186044416 * x0^5 * x1
  + 3044408714823779/4398046511104 * x0^4 * x1^2
  + -210488238149591/1099511627776 * x0^3 * x1^3
  + 1981398075518677/8796093022208 * x0^2 * x1^4
  + 6898566433792895/70368744177664 * x0 * x1^5
  + 6970683302951713/17592186044416 * x1^6
  + -3285158447224093/8796093022208 * x0^7
  + -5626469762167197/8796093022208 * x0^6 * x1
  + -406756100778665/17592186044416 * x0^5 * x1^2
  + 329098132184885/1099511627776 * x0^4 * x1^3
  + -6225562603367737/140737488355328 * x0^3 * x1^4
  + -2929096888813453/8796093022208 * x0^2 * x1^5
  + -4606014909079451/8796093022208 * x0 * x1^6
  + -1717178021393315/35184372088832 * x1^7
  + 1391634828595445/4398046511104 * x0^8
  + 4228925982209061/140737488355328 * x0^7 * x1
  + 6414577935184951/17592186044416 * x0^6 * x1^2
  + -126154855364417/1099511627776 * x0^5 * x1^3
  + 95644957167161/137438953472 * x0^4 * x1^4
  + 2765606698417541/17592186044416 * x0^3 * x1^5
  + 7053604431376137/2251799813685248 * x0^2 * x1^6
  + 7303158816864151/17592186044416 * x0 * x1^7
  + 2142568864227053/70368744177664 * x1^8
  + -2123313203235459/2199023255552 * x0^9
  + 1200522906893907/2199023255552 * x0^8 * x1
  + -6505041237529121/8796093022208 * x0^7 * x1^2
  + 4460972027381353/17592186044416 * x0^6 * x1^3
  + -7170783476527669/8796093022208 * x0^5 * x1^4
  + 3039982960013397/8796093022208 * x0^4 * x1^5
  + -5198717710238855/17592186044416 * x0^3 * x1^6
  + -222722167593225/1099511627776 * x0^2 * x1^7
  + -7493859691547767/17592186044416 * x0 * x1^8
  + -1645757926961979/8796093022208 * x1^9
  + 3164421016648149/2199023255552 * x0^10
  + -571729220845949/4398046511104 * x0^9 * x1
  + 5537357241166063/8796093022208 * x0^8 * x1^2
  + -4051640944831873/35184372088832 * x0^7 * x1^3
  + 163921718402319/8796093022208 * x0^6 * x1^4
  + -1878550635287917/4398046511104 * x0^5 * x1^5
  + 1932746011092855/2199023255552 * x0^4 * x1^6
  + -6170168277360295/8796093022208 * x0^3 * x1^7
  + 6703024912085869/8796093022208 * x0^2 * x1^8
  + 5161339807698503/17592186044416 * x0 * x1^9
  + 6233475743226431/17592186044416 * x1^10
  + -1311705114092429/1099511627776 * x0^11
  + -6766440584991343/17592186044416 * x0^10 * x1
  + -6841857356969309/17592186044416 * x0^9 * x1^2
  + -1271409049815737/2199023255552 * x0^8 * x1^3
  + -7821505873639201/17592186044416 * x0^7 * x1^4
  + 7500827275317593/562949953421312 * x0^6 * x1^5
  + -4798296272691327/8796093022208 * x0^5 * x1^6
  + 3207718761071481/35184372088832 * x0^4 * x1^7
  + -5214411332298779/8796093022208 * x0^3 * x1^8
  + 1542685045905125/8796093022208 * x0^2 * x1^9
  + -2148503432751585/2199023255552 * x0 * x1^10
  + -2960283934363845/8796093022208 * x1^11
  + 1426168373326541/2199023255552 * x0^12
  + 8334438670573623/17592186044416 * x0^11 * x1
  + 6712533821158507/70368744177664 * x0^10 * x1^2
  + 2363827549559029/8796093022208 * x0^9 * x1^3
  + 6119987426348153/8796093022208 * x0^8 * x1^4
  + 3557672173747595/8796093022208 * x0^7 * x1^5
  + 7954339535463619/140737488355328 * x0^6 * x1^6
  + 7376540223791235/17592186044416 * x0^5 * x1^7
  + 704942308608289/2199023255552 * x0^4 * x1^8
  + -3654130893670977/17592186044416 * x0^3 * x1^9
  + 2189761024061649/4398046511104 * x0^2 * x1^10
  + 4384401697569051/8796093022208 * x0 * x1^11
  + 3199399545255989/35184372088832 * x1^12
  + -8586208938054243/35184372088832 * x0^13
  + -571650033131995/2199023255552 * x0^12 * x1
  + 55810922589987/274877906944 * x0^11 * x1^2
  + 754106591563695/1099511627776 * x0^10 * x1^3
  + 1147325335885069/4398046511104 * x0^9 * x1^4
  + -4997434954014315/17592186044416 * x0^8 * x1^5
  + -3301758465806259/70368744177664 * x0^7 * x1^6
  + 7743208992597621/35184372088832 * x0^6 * x1^7
  + 8531150081392233/562949953421312 * x0^5 * x1^8
  + -7947403894382469/35184372088832 * x0^4 * x1^9
  + 1539940108171345/4398046511104 * x0^3 * x1^10
  + 5760039848921519/70368744177664 * x0^2 * x1^11
  + -343965129747499/2199023255552 * x0 * x1^12
  + -3205535556356763/17592186044416 * x1^13
  + 3952568125649129/70368744177664 * x0^14
  + 7127698810101703/140737488355328 * x0^13 * x1
  + -7348776999606883/35184372088832 * x0^12 * x1^2
  + -5525755445729649/8796093022208 * x0^11 * x1^3
  + -4924107741051319/8796093022208 * x0^10 * x1^4
  + -4583232514919499/70368744177664 * x0^9 * x1^5
  + 314247489544039/1099511627776 * x0^8 * x1^6
  + 5972707731504595/70368744177664 * x0^7 * x1^7
  + -2005057315734851/70368744177664 * x0^6 * x1^8
  + 2295244553638801/8796093022208 * x0^5 * x1^9
  + -6824530043912867/281474976710656 * x0^4 * x1^10
  + -5323630787074783/17592186044416 * x0^3 * x1^11
  + 6628912025013983/140737488355328 * x0^2 * x1^12
  + 5433496096744065/8796093022208 * x0 * x1^13
  + 1554089467144983/4398046511104 * x1^14
  + -6073160030508241/1125899906842624 * x0^15
  + 2272669667592779/562949953421312 * x0^14 * x1
  + 3640416808643137/70368744177664 * x0^13 * x1^2
  + 8950747465121375/70368744177664 * x0^12 * x1^3
  + 5665965270589055/35184372088832 * x0^11 * x1^4
  + 5615698135082391/70368744177664 * x0^10 * x1^5
  + -2469304647604279/8796093022208 * x0^9 * x1^6
  + -8913560564750877/17592186044416 * x0^8 * x1^7
  + -8349245206665321/35184372088832 * x0^7 * x1^8
  + -4505072336280651/70368744177664 * x0^6 * x1^9
  + -4984121790331509/17592186044416 * x0^5 * x1^10
  + -7366901079338721/35184372088832 * x0^4 * x1^11
  + -3124631388917907/1125899906842624 * x0^3 * x1^12
  + -6262517859583939/17592186044416 * x0^2 * x1^13
  + -672016201734641/1099511627776 * x0 * x1^14
  + -1806416013172583/8796093022208 * x1^15
  + 8967485713196019/36028797018963968 * x0^16
  + 6161397457684513/18014398509481984 * x0^15 * x1
  + 3119782047377361/1125899906842624 * x0^14 * x1^2
  + 1100542586818507/140737488355328 * x0^13 * x1^3
  + 66380828749345/8796093022208 * x0^12 * x1^4
  + 4906776586786637/562949953421312 * x0^11 * x1^5
  + 1222506017687989/17592186044416 * x0^10 * x1^6
  + 2970221472612139/17592186044416 * x0^9 * x1^7
  + 3026607250926797/17592186044416 * x0^8 * x1^8
  + 1815883506841247/35184372088832 * x0^7 * x1^9
  + 340839531503175/8796093022208 * x0^6 * x1^10
  + 5034993048739979/35184372088832 * x0^5 * x1^11
  + 6706932315926115/70368744177664 * x0^4 * x1^12
  + 1742230999605865/35184372088832 * x0^3 * x1^13
  + 6100020853519431/35184372088832 * x0^2 * x1^14
  + 4984244725734171/35184372088832 * x0 * x1^15
  + 3174598536528347/70368744177664 * x1^16.
  
Lemma init_pos (x0 x1 : R) :
  p x0 x1
  - init_sigma1 x0 x1 * pI1 x0 x1
  - init_sigma2 x0 x1 * pI2 x0 x1 >= 0.
Proof.
rewrite /p /init_sigma1 /pI1 /init_sigma2 /pI2.
do_sdp.
Qed.

Lemma init_sigma1_pos (x0 x1 : R) : init_sigma1 x0 x1 >= 0.
Proof. rewrite /init_sigma1. do_sdp. Qed.

Lemma init_sigma2_pos (x0 x1 : R) : init_sigma2 x0 x1 >= 0.
Proof. rewrite /init_sigma2. do_sdp. Qed.

Lemma ind0_pos (x0 x1 : R) :
  p (t0_x0 x0 x1) (t0_x1 x0 x1)
  - ind0_sigma x0 x1 * p x0 x1
  - ind0_sigma0 x0 x1 * g0 x0 x1 >= 0.
Proof.
rewrite /p /t0_x0 /t0_x1 /ind0_sigma /ind0_sigma0 /g0.
do_sdp.
Qed.

Lemma ind0_sigma_pos (x0 x1 : R) : ind0_sigma x0 x1 >= 0.
Proof. rewrite /ind0_sigma. do_sdp. Qed.

Lemma ind0_sigma0_pos (x0 x1 : R) : ind0_sigma0 x0 x1 >= 0.
Proof. rewrite /ind0_sigma0. do_sdp. Qed.

Lemma ind1_pos (x0 x1 : R) :
  p (t1_x0 x0 x1) (t1_x1 x0 x1)
  - ind1_sigma x0 x1 * p x0 x1
  - ind1_sigma1 x0 x1 * g1 x0 x1 >= 0.
Proof.
rewrite /p /t1_x0 /t1_x1 /ind1_sigma /ind1_sigma1 /g1.
do_sdp.
Qed.

Lemma ind1_sigma_pos (x0 x1 : R) : ind1_sigma x0 x1 >= 0.
Proof. rewrite /ind1_sigma. do_sdp. Qed.

Lemma ind1_sigma1_pos (x0 x1 : R) : ind1_sigma1 x0 x1 >= 0.
Proof. rewrite /ind1_sigma1. do_sdp. Qed.

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
