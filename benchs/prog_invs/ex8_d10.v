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
  2751369891250564829/1152921504606846976
  + -3097717965715433/4611686018427387904 * x0^2
  + -1669577382630305/9223372036854775808 * x0 * x1
  + -5087457629923805/9223372036854775808 * x1^2
  + 6178333010432029/288230376151711744 * x0^3
  + -3733807525210169/144115188075855872 * x0^2 * x1
  + -447350411140235/288230376151711744 * x0 * x1^2
  + 5058697133185035/144115188075855872 * x1^3
  + -5935474593424963/2251799813685248 * x0^4
  + -1443237039368917/18014398509481984 * x0^3 * x1
  + -6165992812696583/2251799813685248 * x0^2 * x1^2
  + -5507320924791329/4503599627370496 * x0 * x1^3
  + -3338002160059011/2251799813685248 * x1^4
  + 6088129726249333/9007199254740992 * x0^5
  + -2289635847447407/562949953421312 * x0^4 * x1
  + -6419735255785315/1125899906842624 * x0^3 * x1^2
  + -6929173244553837/9007199254740992 * x0^2 * x1^3
  + 5067333275040391/9007199254740992 * x0 * x1^4
  + 635849871328907/562949953421312 * x1^5
  + -6250058693782407/4503599627370496 * x0^6
  + 5204505599971377/1125899906842624 * x0^5 * x1
  + -1859305396320963/281474976710656 * x0^4 * x1^2
  + -1499262564252091/281474976710656 * x0^3 * x1^3
  + 2565118736069077/4503599627370496 * x0^2 * x1^4
  + 7265881697497037/144115188075855872 * x0 * x1^5
  + 5157199432811747/36028797018963968 * x1^6
  + -4541437987623649/36028797018963968 * x0^7
  + 5452079272378425/1125899906842624 * x0^6 * x1
  + 7274817664941309/1125899906842624 * x0^5 * x1^2
  + 1356130390825973/281474976710656 * x0^4 * x1^3
  + 6507847885036715/1125899906842624 * x0^3 * x1^4
  + 357150797539963/1125899906842624 * x0^2 * x1^5
  + -8252781156878691/9007199254740992 * x0 * x1^6
  + -1616838843261621/1125899906842624 * x1^7
  + 2927675830487615/562949953421312 * x0^8
  + -2995864767016941/281474976710656 * x0^7 * x1
  + 4647104799839235/281474976710656 * x0^6 * x1^2
  + 4979819182879587/562949953421312 * x0^5 * x1^3
  + 399859618481861/70368744177664 * x0^4 * x1^4
  + 4424465019862403/1125899906842624 * x0^3 * x1^5
  + 3262997926439249/1125899906842624 * x0^2 * x1^6
  + 1856928467829909/1125899906842624 * x0 * x1^7
  + 1598341012866239/2251799813685248 * x1^8
  + -7942014041546771/72057594037927936 * x0^9
  + -3333308530813159/2251799813685248 * x0^8 * x1
  + -5124471921815915/2251799813685248 * x0^7 * x1^2
  + -4825820819707963/2251799813685248 * x0^6 * x1^3
  + -1904091811909683/562949953421312 * x0^5 * x1^4
  + -2380173841684083/1125899906842624 * x0^4 * x1^5
  + -390726982423727/281474976710656 * x0^3 * x1^6
  + 6893291745192459/18014398509481984 * x0^2 * x1^7
  + 1901642351442651/4503599627370496 * x0 * x1^8
  + 2462301735840719/4503599627370496 * x1^9
  + -5659452882657849/2251799813685248 * x0^10
  + 6939325838569607/1125899906842624 * x0^9 * x1
  + -4805160669944875/562949953421312 * x0^8 * x1^2
  + -2333274266582637/562949953421312 * x0^7 * x1^3
  + -8599682961494615/2251799813685248 * x0^6 * x1^4
  + -1314413742743423/1125899906842624 * x0^5 * x1^5
  + -4961001981841713/2251799813685248 * x0^4 * x1^6
  + -4784778027034377/2251799813685248 * x0^3 * x1^7
  + -1809084932745541/1125899906842624 * x0^2 * x1^8
  + -6471928452385259/9007199254740992 * x0 * x1^9
  + -3092960601051931/9007199254740992 * x1^10.
  
Let init_sigma1 x0 x1 :=
  2658056165012223/70368744177664 + 3938143345181711/562949953421312 * 
  x0 + 8492428881009705/1125899906842624 * x1
  + 3903508168608453/140737488355328 * x0^2
  + 1959783852336711/562949953421312 * x0 * x1
  + 8212068448707683/281474976710656 * x1^2
  + 7766580604852387/2251799813685248 * x0^3
  + 6015614905342179/1125899906842624 * x0^2 * x1
  + 317573245936949/70368744177664 * x0 * x1^2
  + 3151951068549259/562949953421312 * x1^3
  + 3720645479268933/140737488355328 * x0^4
  + 777317279491003/281474976710656 * x0^3 * x1
  + 5321596971559913/281474976710656 * x0^2 * x1^2
  + 8861410466522161/2251799813685248 * x0 * x1^3
  + 3971176472520683/140737488355328 * x1^4
  + 1587424126588725/562949953421312 * x0^5
  + 6214477762679021/1125899906842624 * x0^4 * x1
  + 3358369108938917/1125899906842624 * x0^3 * x1^2
  + 5237550190734361/1125899906842624 * x0^2 * x1^3
  + 1130141857391633/281474976710656 * x0 * x1^4
  + 6311693354717599/1125899906842624 * x1^5
  + 7668075537156435/281474976710656 * x0^6
  + 4729131418383369/1125899906842624 * x0^5 * x1
  + 5254029647741561/281474976710656 * x0^4 * x1^2
  + 2288852254812011/562949953421312 * x0^3 * x1^3
  + 5378564850804605/281474976710656 * x0^2 * x1^4
  + 4760176602895719/1125899906842624 * x0 * x1^5
  + 4090848392321647/140737488355328 * x1^6
  + 6969970828575479/562949953421312 * x0^7
  + 7231141453064509/1125899906842624 * x0^6 * x1
  + 6599837142118101/1125899906842624 * x0^5 * x1^2
  + 6785608374204509/1125899906842624 * x0^4 * x1^3
  + 2709896621385459/562949953421312 * x0^3 * x1^4
  + 6361177951753133/1125899906842624 * x0^2 * x1^5
  + 6446603140639847/1125899906842624 * x0 * x1^6
  + 1804337385666195/281474976710656 * x1^7
  + 773973912022861/17592186044416 * x0^8
  + -5278401319585187/2251799813685248 * x0^7 * x1
  + 8379263283496681/281474976710656 * x0^6 * x1^2
  + 1135528389814531/562949953421312 * x0^5 * x1^3
  + 8159257479555029/281474976710656 * x0^4 * x1^4
  + 8514313389306805/4503599627370496 * x0^3 * x1^5
  + 2071031279894205/70368744177664 * x0^2 * x1^6
  + 7342623715570269/4503599627370496 * x0 * x1^7
  + 1381636489439759/35184372088832 * x1^8.
  
Let init_sigma2 x0 x1 :=
  5287894521886141/140737488355328 + 8171720580606943/1125899906842624 * 
  x0 + 7612396373130961/1125899906842624 * x1
  + 4068082680560141/140737488355328 * x0^2
  + 3561663897865577/1125899906842624 * x0 * x1
  + 7741522618192483/281474976710656 * x1^2
  + 5988825135684417/1125899906842624 * x0^3
  + 4667841830295483/1125899906842624 * x0^2 * x1
  + 5671897348623031/1125899906842624 * x0 * x1^2
  + 7362119625659671/2251799813685248 * x1^3
  + 1961870237022769/70368744177664 * x0^4
  + 491291061049567/140737488355328 * x0^3 * x1
  + 2631144649119959/140737488355328 * x0^2 * x1^2
  + 5811819499278675/2251799813685248 * x0 * x1^3
  + 1841778538304631/70368744177664 * x1^4
  + 6076864399612927/1125899906842624 * x0^5
  + 4073239210604651/1125899906842624 * x0^4 * x1
  + 2454059339708063/562949953421312 * x0^3 * x1^2
  + 6390165226777259/2251799813685248 * x0^2 * x1^3
  + 2823650975726557/562949953421312 * x0 * x1^4
  + 6806604941418727/2251799813685248 * x1^5
  + 2013589564569071/70368744177664 * x0^6
  + 1137762349273247/281474976710656 * x0^5 * x1
  + 5291802374369727/281474976710656 * x0^4 * x1^2
  + 8381246394229203/2251799813685248 * x0^3 * x1^3
  + 1293975176881925/70368744177664 * x0^2 * x1^4
  + 7342044128093115/2251799813685248 * x0 * x1^5
  + 3875717106431175/140737488355328 * x1^6
  + 6375513092451271/1125899906842624 * x0^7
  + 3242415121169411/562949953421312 * x0^6 * x1
  + 5991850551792683/1125899906842624 * x0^5 * x1^2
  + 4927049888379287/1125899906842624 * x0^4 * x1^3
  + 3097548968973733/562949953421312 * x0^3 * x1^4
  + 2800733674159795/562949953421312 * x0^2 * x1^5
  + 8154616108696085/1125899906842624 * x0 * x1^6
  + 6545978431636303/562949953421312 * x1^7
  + 2773961823141561/70368744177664 * x0^8
  + 5094941069501391/4503599627370496 * x0^7 * x1
  + 8222671754434755/281474976710656 * x0^6 * x1^2
  + 5886783644777203/4503599627370496 * x0^5 * x1^3
  + 8008867660228517/281474976710656 * x0^4 * x1^4
  + 8018802295796377/4503599627370496 * x0^3 * x1^5
  + 8172839174826527/281474976710656 * x0^2 * x1^6
  + -6948274763448071/9007199254740992 * x0 * x1^7
  + 6114712277115403/140737488355328 * x1^8.
  
Let ind0_sigma x0 x1 :=
  8748478933488289/18014398509481984 + -2148864576456069/562949953421312 * 
  x0 + 7714100082225909/2251799813685248 * x1
  + 495067596885933/35184372088832 * x0^2
  + -1530993061837649/70368744177664 * x0 * x1
  + 2944605997806219/281474976710656 * x1^2
  + -5690729725713165/562949953421312 * x0^3
  + 6323564696930795/140737488355328 * x0^2 * x1
  + -1342942952414499/35184372088832 * x0 * x1^2
  + 6301231700811697/1125899906842624 * x1^3
  + -4797041029357375/1125899906842624 * x0^4
  + -5419801772904023/140737488355328 * x0^3 * x1
  + 6834900934779149/140737488355328 * x0^2 * x1^2
  + -6908447740970809/140737488355328 * x0 * x1^3
  + 532371754195355/70368744177664 * x1^4
  + -641701353324127/17592186044416 * x0^5
  + 6947033015989701/140737488355328 * x0^4 * x1
  + -4613564243829507/140737488355328 * x0^3 * x1^2
  + 5383126224325669/140737488355328 * x0^2 * x1^3
  + -5029068607194059/70368744177664 * x0 * x1^4
  + 3709969365747605/70368744177664 * x1^5
  + 8719349516072787/140737488355328 * x0^6
  + -5332509849689505/70368744177664 * x0^5 * x1
  + 4678761626577235/70368744177664 * x0^4 * x1^2
  + -5720033284657827/1125899906842624 * x0^3 * x1^3
  + 4351730256700289/70368744177664 * x0^2 * x1^4
  + -8907081338072905/562949953421312 * x0 * x1^5
  + 5081055688217875/140737488355328 * x1^6
  + 2811381482203565/1125899906842624 * x0^7
  + 7625028679730923/140737488355328 * x0^6 * x1
  + -310700300641423/4398046511104 * x0^5 * x1^2
  + 8488340751411713/1125899906842624 * x0^4 * x1^3
  + -5857132774092805/281474976710656 * x0^3 * x1^4
  + 1636405781597707/35184372088832 * x0^2 * x1^5
  + 6134057915741723/281474976710656 * x0 * x1^6
  + -6730258334719347/140737488355328 * x1^7
  + 183906151170085/281474976710656 * x0^8
  + -4673200482296045/70368744177664 * x0^7 * x1
  + 5150668367177825/140737488355328 * x0^6 * x1^2
  + -5374541964365929/140737488355328 * x0^5 * x1^3
  + 7811724122207357/281474976710656 * x0^4 * x1^4
  + -8089524460020785/140737488355328 * x0^3 * x1^5
  + 5867233150079107/281474976710656 * x0^2 * x1^6
  + -3526222354073455/35184372088832 * x0 * x1^7
  + -516042685904633/9007199254740992 * x1^8
  + -984297873746633/17592186044416 * x0^9
  + 7176971135284201/70368744177664 * x0^8 * x1
  + -3909739418466803/70368744177664 * x0^7 * x1^2
  + 2016856682000467/70368744177664 * x0^6 * x1^3
  + -8219922882379139/140737488355328 * x0^5 * x1^4
  + 294018484720821/4398046511104 * x0^4 * x1^5
  + -315383991081315/17592186044416 * x0^3 * x1^6
  + 7905013034704969/140737488355328 * x0^2 * x1^7
  + -5033658677680827/35184372088832 * x0 * x1^8
  + 2919139323184749/35184372088832 * x1^9
  + 8824171721761981/281474976710656 * x0^10
  + -7041340998437137/140737488355328 * x0^9 * x1
  + 2766998270910217/70368744177664 * x0^8 * x1^2
  + -3773394764685165/1125899906842624 * x0^7 * x1^3
  + 727311002575011/35184372088832 * x0^6 * x1^4
  + -661672759757281/17592186044416 * x0^5 * x1^5
  + 2034437253736713/70368744177664 * x0^4 * x1^6
  + 4539385334011019/281474976710656 * x0^3 * x1^7
  + 2840480459072087/70368744177664 * x0^2 * x1^8
  + -6720788190772507/140737488355328 * x0 * x1^9
  + 6008758624759963/140737488355328 * x1^10.
  
Let ind0_sigma0 x0 x1 :=
  1026730013349603/70368744177664 + -1127238949909931/17592186044416 * 
  x0 + 8273184856228649/140737488355328 * x1
  + 7452946951477767/70368744177664 * x0^2
  + -7292265154558215/35184372088832 * x0 * x1
  + 6497198843372087/70368744177664 * x1^2
  + -3125335714882623/35184372088832 * x0^3
  + 1975102280599673/8796093022208 * x0^2 * x1
  + -3674256981068897/17592186044416 * x0 * x1^2
  + 6733983095236971/70368744177664 * x1^3
  + 416889410935015/4398046511104 * x0^4
  + -7090965765038087/70368744177664 * x0^3 * x1
  + 553719995631469/8796093022208 * x0^2 * x1^2
  + -4136680119115367/35184372088832 * x0 * x1^3
  + 7934492213437529/70368744177664 * x1^4
  + -6955685888335853/70368744177664 * x0^5
  + 8517682031072239/70368744177664 * x0^4 * x1
  + 6361782423555239/281474976710656 * x0^3 * x1^2
  + -8691445042903409/562949953421312 * x0^2 * x1^3
  + -5181086732549493/35184372088832 * x0 * x1^4
  + 604164489812813/8796093022208 * x1^5
  + 4614571817450455/140737488355328 * x0^6
  + -5124538033517547/35184372088832 * x0^5 * x1
  + 7889221259596073/140737488355328 * x0^4 * x1^2
  + -563798028530319/35184372088832 * x0^3 * x1^3
  + 967078252104117/17592186044416 * x0^2 * x1^4
  + -5010167615103017/35184372088832 * x0 * x1^5
  + 2968129032113347/140737488355328 * x1^6
  + -3554359358562555/70368744177664 * x0^7
  + 3156519036312545/35184372088832 * x0^6 * x1
  + 8111894326228221/140737488355328 * x0^5 * x1^2
  + 5258197893201151/70368744177664 * x0^4 * x1^3
  + -284745254869251/4398046511104 * x0^3 * x1^4
  + -7081008281891057/140737488355328 * x0^2 * x1^5
  + -8407972417539517/70368744177664 * x0 * x1^6
  + 212091601392485/2199023255552 * x1^7
  + 6089841331875857/70368744177664 * x0^8
  + -1758898769455081/17592186044416 * x0^7 * x1
  + -2986409074321211/281474976710656 * x0^6 * x1^2
  + -4728637392518327/281474976710656 * x0^5 * x1^3
  + 1169164081206325/35184372088832 * x0^4 * x1^4
  + -8055632698832345/281474976710656 * x0^3 * x1^5
  + 766389920389395/4503599627370496 * x0^2 * x1^6
  + -6858228644566215/70368744177664 * x0 * x1^7
  + 7557350627030155/70368744177664 * x1^8
  + -1834191630918017/35184372088832 * x0^9
  + 6495555618392071/70368744177664 * x0^8 * x1
  + -5504405734284399/140737488355328 * x0^7 * x1^2
  + 5483624146651045/140737488355328 * x0^6 * x1^3
  + -2675468548449707/70368744177664 * x0^5 * x1^4
  + 4690391166967267/140737488355328 * x0^4 * x1^5
  + -4853509099998181/140737488355328 * x0^3 * x1^6
  + 84278528671439/2199023255552 * x0^2 * x1^7
  + -6595357621194435/140737488355328 * x0 * x1^8
  + 1663045446834505/17592186044416 * x1^9
  + 501060795797581/4398046511104 * x0^10
  + -1167107535395343/17592186044416 * x0^9 * x1
  + -3767495329191685/70368744177664 * x0^8 * x1^2
  + -5256928365510315/281474976710656 * x0^7 * x1^3
  + 135877226788469/2199023255552 * x0^6 * x1^4
  + 7987650760152203/140737488355328 * x0^5 * x1^5
  + 1044269831813451/17592186044416 * x0^4 * x1^6
  + -417735216518639/17592186044416 * x0^3 * x1^7
  + -2726705288006013/281474976710656 * x0^2 * x1^8
  + -4607163526634519/70368744177664 * x0 * x1^9
  + 150751021986505/1099511627776 * x1^10
  + -2373380315485835/17592186044416 * x0^11
  + 8508108821440147/140737488355328 * x0^10 * x1
  + -5385469943887433/140737488355328 * x0^9 * x1^2
  + 1323182283017657/35184372088832 * x0^8 * x1^3
  + -6668593871647447/140737488355328 * x0^7 * x1^4
  + 163259675303857/8796093022208 * x0^6 * x1^5
  + -5358532080744323/140737488355328 * x0^5 * x1^6
  + 7184868917978455/281474976710656 * x0^4 * x1^7
  + -1572764862879841/70368744177664 * x0^3 * x1^8
  + 4699887978967895/70368744177664 * x0^2 * x1^9
  + -6449267980793695/140737488355328 * x0 * x1^10
  + 5639624895851439/70368744177664 * x1^11
  + 3150260524762489/35184372088832 * x0^12
  + -2023561675865709/35184372088832 * x0^11 * x1
  + 5909821699765187/1125899906842624 * x0^10 * x1^2
  + -8088175583241349/140737488355328 * x0^9 * x1^3
  + 8091898129879263/140737488355328 * x0^8 * x1^4
  + 467591980658879/8796093022208 * x0^7 * x1^5
  + 7009797663708175/70368744177664 * x0^6 * x1^6
  + 7771370849613177/562949953421312 * x0^5 * x1^7
  + 3589947031125453/70368744177664 * x0^4 * x1^8
  + -4714936225080235/2251799813685248 * x0^3 * x1^9
  + 8210058713412003/1125899906842624 * x0^2 * x1^10
  + -5187280229196935/70368744177664 * x0 * x1^11
  + 83637917962729/1099511627776 * x1^12
  + -4979083298931757/35184372088832 * x0^13
  + 8820345199820483/140737488355328 * x0^12 * x1
  + 4522791616581985/281474976710656 * x0^11 * x1^2
  + 320957248516333/8796093022208 * x0^10 * x1^3
  + 1490011142801741/70368744177664 * x0^9 * x1^4
  + 3200198360897917/140737488355328 * x0^8 * x1^5
  + -3691799390641629/70368744177664 * x0^7 * x1^6
  + -8993967261649985/281474976710656 * x0^6 * x1^7
  + -2666836854246457/281474976710656 * x0^5 * x1^8
  + 6020102047781877/140737488355328 * x0^4 * x1^9
  + -6885104265231751/140737488355328 * x0^3 * x1^10
  + -5221420474957127/562949953421312 * x0^2 * x1^11
  + -4294322506715207/35184372088832 * x0 * x1^12
  + 6955583791200897/70368744177664 * x1^13
  + 8930375709827637/140737488355328 * x0^14
  + -50170819873753/549755813888 * x0^13 * x1
  + 4924589928942363/70368744177664 * x0^12 * x1^2
  + -2143233281762153/35184372088832 * x0^11 * x1^3
  + 7233376871344415/140737488355328 * x0^10 * x1^4
  + -2808175002092421/70368744177664 * x0^9 * x1^5
  + 5335206805556007/140737488355328 * x0^8 * x1^6
  + -7956916232234563/281474976710656 * x0^7 * x1^7
  + 263479494082611/4398046511104 * x0^6 * x1^8
  + -66947384675235/2199023255552 * x0^5 * x1^9
  + 1893687010816467/70368744177664 * x0^4 * x1^10
  + -7913053014458985/140737488355328 * x0^3 * x1^11
  + 5030626264852499/140737488355328 * x0^2 * x1^12
  + -3837839161860479/35184372088832 * x0 * x1^13
  + 1908092153494719/281474976710656 * x1^14
  + 5303448563759787/140737488355328 * x0^15
  + 5700107104639139/35184372088832 * x0^14 * x1
  + 2738890748742087/70368744177664 * x0^13 * x1^2
  + 6159254660648993/140737488355328 * x0^12 * x1^3
  + -971310604115903/140737488355328 * x0^11 * x1^4
  + 2130472941616745/70368744177664 * x0^10 * x1^5
  + -6929661151036201/281474976710656 * x0^9 * x1^6
  + -4510025156445891/281474976710656 * x0^8 * x1^7
  + -1567593183771543/35184372088832 * x0^7 * x1^8
  + 6830037085367811/281474976710656 * x0^6 * x1^9
  + 2518153668639143/140737488355328 * x0^5 * x1^10
  + 5334376874439/137438953472 * x0^4 * x1^11
  + -371647325332821/8796093022208 * x0^3 * x1^12
  + -4880575656771395/70368744177664 * x0^2 * x1^13
  + -7536144790892095/35184372088832 * x0 * x1^14
  + 3720525323047347/70368744177664 * x1^15
  + 449996267395857/4398046511104 * x0^16
  + -4175738718382933/17592186044416 * x0^15 * x1
  + -4596081312225291/70368744177664 * x0^14 * x1^2
  + -8778972200379477/140737488355328 * x0^13 * x1^3
  + 1589730663699099/70368744177664 * x0^12 * x1^4
  + -780064316853575/17592186044416 * x0^11 * x1^5
  + -2684510821076279/70368744177664 * x0^10 * x1^6
  + -4166059702248109/35184372088832 * x0^9 * x1^7
  + -7765568761399619/281474976710656 * x0^8 * x1^8
  + -2456573480422863/35184372088832 * x0^7 * x1^9
  + 1172092034057303/562949953421312 * x0^6 * x1^10
  + -641441088798025/8796093022208 * x0^5 * x1^11
  + 4450825789144521/281474976710656 * x0^4 * x1^12
  + -5258437542406891/35184372088832 * x0^3 * x1^13
  + -3842969488014051/70368744177664 * x0^2 * x1^14
  + -4374172561218597/17592186044416 * x0 * x1^15
  + 6952219477244297/35184372088832 * x1^16
  + -2980288884119529/17592186044416 * x0^17
  + 3523790514343593/17592186044416 * x0^16 * x1
  + -8331915555357545/140737488355328 * x0^15 * x1^2
  + 5511219789433879/70368744177664 * x0^14 * x1^3
  + -5701617827276597/35184372088832 * x0^13 * x1^4
  + -1466113542808965/140737488355328 * x0^12 * x1^5
  + -4297060038106637/35184372088832 * x0^11 * x1^6
  + 3384575945834045/70368744177664 * x0^10 * x1^7
  + -7986615217520231/140737488355328 * x0^9 * x1^8
  + 7102379164117443/70368744177664 * x0^8 * x1^9
  + -8999965506467893/281474976710656 * x0^7 * x1^10
  + 2616065348257091/17592186044416 * x0^6 * x1^11
  + -189751324366737/35184372088832 * x0^5 * x1^12
  + 6322325011250593/70368744177664 * x0^4 * x1^13
  + -8002491534891627/70368744177664 * x0^3 * x1^14
  + 3547551558428257/70368744177664 * x0^2 * x1^15
  + -3613067443507937/35184372088832 * x0 * x1^16
  + 2822527518445421/17592186044416 * x1^17
  + 4169482524465321/70368744177664 * x0^18
  + -4658334784314973/70368744177664 * x0^17 * x1
  + 1792102407052243/35184372088832 * x0^16 * x1^2
  + -4375036678240581/140737488355328 * x0^15 * x1^3
  + 2768412478848427/35184372088832 * x0^14 * x1^4
  + 3315377386898747/140737488355328 * x0^13 * x1^5
  + 4753672973324683/35184372088832 * x0^12 * x1^6
  + 1981749722383569/70368744177664 * x0^11 * x1^7
  + 5137894188189193/281474976710656 * x0^10 * x1^8
  + -5962602559089187/140737488355328 * x0^9 * x1^9
  + 3641716427458545/70368744177664 * x0^8 * x1^10
  + -5114767303899687/562949953421312 * x0^7 * x1^11
  + 6614877611842447/70368744177664 * x0^6 * x1^12
  + 7642371341518551/140737488355328 * x0^5 * x1^13
  + 5346031059186007/70368744177664 * x0^4 * x1^14
  + -7081114475957505/562949953421312 * x0^3 * x1^15
  + 2413280343205631/70368744177664 * x0^2 * x1^16
  + -1333050698745329/140737488355328 * x0 * x1^17
  + 5783258592887901/140737488355328 * x1^18.
  
Let ind1_sigma x0 x1 :=
  4327161810841519/9007199254740992 + 1634815923710825/562949953421312 * 
  x0 + -5489045920169869/2251799813685248 * x1
  + 1411382397495389/140737488355328 * x0^2
  + -3900621361119289/281474976710656 * x0 * x1
  + 689149204784601/140737488355328 * x1^2
  + 2889924374449753/562949953421312 * x0^3
  + -7438839261863955/281474976710656 * x0^2 * x1
  + 11936575569873/549755813888 * x0 * x1^2
  + -1255747731661593/562949953421312 * x1^3
  + -5625280885771263/562949953421312 * x0^4
  + -7686517241654961/562949953421312 * x0^3 * x1
  + 5991345633976443/281474976710656 * x0^2 * x1^2
  + -4050061212202777/140737488355328 * x0 * x1^3
  + 432879819206597/35184372088832 * x1^4
  + 559760157147361/35184372088832 * x0^5
  + -890852755788513/281474976710656 * x0^4 * x1
  + 4653402828608661/281474976710656 * x0^3 * x1^2
  + -312812089649865/8796093022208 * x0^2 * x1^3
  + 7398196706918743/281474976710656 * x0 * x1^4
  + -3415206004441345/140737488355328 * x1^5
  + 5409160052614801/140737488355328 * x0^6
  + -3990371446945725/140737488355328 * x0^5 * x1
  + 5617165445104061/140737488355328 * x0^4 * x1^2
  + -8168710621114801/562949953421312 * x0^3 * x1^3
  + 5833732186833887/140737488355328 * x0^2 * x1^4
  + 3088284985304233/562949953421312 * x0 * x1^5
  + 3499110162900825/2251799813685248 * x1^6
  + -8457430476623417/1125899906842624 * x0^7
  + -341192032585625/8796093022208 * x0^6 * x1
  + 5364602419894287/140737488355328 * x0^5 * x1^2
  + -5399992179886199/1125899906842624 * x0^4 * x1^3
  + 76639500426119/8796093022208 * x0^3 * x1^4
  + 5877484104289075/4503599627370496 * x0^2 * x1^5
  + 5577918403539359/281474976710656 * x0 * x1^6
  + 6710273030187253/2251799813685248 * x1^7
  + -3035369920960881/281474976710656 * x0^8
  + -2508815426009573/70368744177664 * x0^7 * x1
  + 5782487435959223/281474976710656 * x0^6 * x1^2
  + -1582231682220263/70368744177664 * x0^5 * x1^3
  + -6219340723551535/562949953421312 * x0^4 * x1^4
  + -4847461265396727/140737488355328 * x0^3 * x1^5
  + 4142616121275837/562949953421312 * x0^2 * x1^6
  + -5572944733094125/70368744177664 * x0 * x1^7
  + 151620505710769/4398046511104 * x1^8
  + 1196283772770579/35184372088832 * x0^9
  + -7011919383053893/140737488355328 * x0^8 * x1
  + 4484266219739333/140737488355328 * x0^7 * x1^2
  + -5421378626063523/281474976710656 * x0^6 * x1^3
  + 4737545246156137/281474976710656 * x0^5 * x1^4
  + -5995423726964229/140737488355328 * x0^4 * x1^5
  + 2222758720378491/70368744177664 * x0^3 * x1^6
  + -342289729455715/8796093022208 * x0^2 * x1^7
  + 129628377203241/2199023255552 * x0 * x1^8
  + -5476175839473235/140737488355328 * x1^9
  + 6438536267795501/281474976710656 * x0^10
  + -8096089173730189/281474976710656 * x0^9 * x1
  + 5476636767766857/281474976710656 * x0^8 * x1^2
  + -5629568447087615/2251799813685248 * x0^7 * x1^3
  + 5666024776692139/281474976710656 * x0^6 * x1^4
  + -3809762805327039/562949953421312 * x0^5 * x1^5
  + 8440549922686409/281474976710656 * x0^4 * x1^6
  + -1314337424373081/281474976710656 * x0^3 * x1^7
  + 2660935944223395/140737488355328 * x0^2 * x1^8
  + -1774524451735821/140737488355328 * x0 * x1^9
  + 1632325859733799/140737488355328 * x1^10.
  
Let ind1_sigma1 x0 x1 :=
  2897569416150377/281474976710656 + 2925521033707087/70368744177664 * 
  x0 + -5048349132713703/140737488355328 * x1
  + 4665573941375175/70368744177664 * x0^2
  + -7889515105482215/70368744177664 * x0 * x1
  + 3935300288789153/70368744177664 * x1^2
  + 204121277475901/4398046511104 * x0^3
  + -3957622811524619/35184372088832 * x0^2 * x1
  + 1784960758437247/17592186044416 * x0 * x1^2
  + -1053495927925111/17592186044416 * x1^3
  + 1949475219205361/70368744177664 * x0^4
  + -3880804071793401/70368744177664 * x0^3 * x1
  + 5347012475016095/281474976710656 * x0^2 * x1^2
  + -8405223667363449/140737488355328 * x0 * x1^3
  + 1019483557283373/17592186044416 * x1^4
  + 4977554115651957/140737488355328 * x0^5
  + -4760347101111023/70368744177664 * x0^4 * x1
  + 1143084579299697/140737488355328 * x0^3 * x1^2
  + 8090223721147943/562949953421312 * x0^2 * x1^3
  + 4661892159741335/70368744177664 * x0 * x1^4
  + -6031349242436401/140737488355328 * x1^5
  + 8731393841709491/281474976710656 * x0^6
  + -3008632002390129/35184372088832 * x0^5 * x1
  + 1891158651137993/70368744177664 * x0^4 * x1^2
  + -1813696413050777/140737488355328 * x0^3 * x1^3
  + 1365459014884023/70368744177664 * x0^2 * x1^4
  + -2361143314272939/35184372088832 * x0 * x1^5
  + 2289658908379027/70368744177664 * x1^6
  + 6637995381816871/140737488355328 * x0^7
  + -6455237858344385/140737488355328 * x0^6 * x1
  + -2542998460887951/70368744177664 * x0^5 * x1^2
  + -1595433968150243/70368744177664 * x0^4 * x1^3
  + 6654204569866733/140737488355328 * x0^3 * x1^4
  + 5406745923499555/281474976710656 * x0^2 * x1^5
  + 7332965063027277/140737488355328 * x0 * x1^6
  + -6547390503550589/140737488355328 * x1^7
  + 2259114998164635/35184372088832 * x0^8
  + -8431802620003135/281474976710656 * x0^7 * x1
  + 7576951280497919/562949953421312 * x0^6 * x1^2
  + -7630966826536981/562949953421312 * x0^5 * x1^3
  + 574967554593687/35184372088832 * x0^4 * x1^4
  + -5427532666982651/281474976710656 * x0^3 * x1^5
  + -190121380665243/35184372088832 * x0^2 * x1^6
  + -5496104189499377/140737488355328 * x0 * x1^7
  + 2211212956036445/35184372088832 * x1^8
  + 6757735678270255/140737488355328 * x0^9
  + -6009652884362045/140737488355328 * x0^8 * x1
  + 4969400449910261/281474976710656 * x0^7 * x1^2
  + -852446593441477/35184372088832 * x0^6 * x1^3
  + 1711207826256317/70368744177664 * x0^5 * x1^4
  + -7800963550236235/2251799813685248 * x0^4 * x1^5
  + 5335102142598053/281474976710656 * x0^3 * x1^6
  + -5445528300119691/281474976710656 * x0^2 * x1^7
  + 8705381540999917/281474976710656 * x0 * x1^8
  + -7619666876296293/140737488355328 * x1^9
  + 4343996367364537/70368744177664 * x0^10
  + -2459304872960493/140737488355328 * x0^9 * x1
  + -1189173616073779/140737488355328 * x0^8 * x1^2
  + -7425938912543041/9007199254740992 * x0^7 * x1^3
  + 6263808247524701/281474976710656 * x0^6 * x1^4
  + 2967422931028863/140737488355328 * x0^5 * x1^5
  + 1806083405604475/70368744177664 * x0^4 * x1^6
  + -4305576187725167/140737488355328 * x0^3 * x1^7
  + 8921240703219151/1125899906842624 * x0^2 * x1^8
  + -3145316339521085/140737488355328 * x0 * x1^9
  + 1336922996033425/35184372088832 * x1^10
  + 7645986520077963/140737488355328 * x0^11
  + -8067056279038387/281474976710656 * x0^10 * x1
  + 136039639387755/4398046511104 * x0^9 * x1^2
  + -2822804468593909/140737488355328 * x0^8 * x1^3
  + 2086276995468193/140737488355328 * x0^7 * x1^4
  + -4983683760648195/281474976710656 * x0^6 * x1^5
  + 4543199940896925/140737488355328 * x0^5 * x1^6
  + -3598068749453595/281474976710656 * x0^4 * x1^7
  + -3579410792611237/281474976710656 * x0^3 * x1^8
  + -3127679828882215/140737488355328 * x0^2 * x1^9
  + 334067186908459/8796093022208 * x0 * x1^10
  + -6917820478916661/140737488355328 * x1^11
  + 407860260922597/17592186044416 * x0^12
  + -7489472062805193/140737488355328 * x0^11 * x1
  + -3369501167883595/1125899906842624 * x0^10 * x1^2
  + -1023407572918261/70368744177664 * x0^9 * x1^3
  + 1196823414463963/35184372088832 * x0^8 * x1^4
  + 1241207914504337/140737488355328 * x0^7 * x1^5
  + 3996220649818983/140737488355328 * x0^6 * x1^6
  + 2846021669595175/140737488355328 * x0^5 * x1^7
  + 8563477241941519/281474976710656 * x0^4 * x1^8
  + -5624793901892165/281474976710656 * x0^3 * x1^9
  + 3039947143694841/562949953421312 * x0^2 * x1^10
  + -7598532218477015/140737488355328 * x0 * x1^11
  + 5711624435867479/140737488355328 * x1^12
  + 3455414750591195/70368744177664 * x0^13
  + -2864492593458749/70368744177664 * x0^12 * x1
  + -8783088621225501/1125899906842624 * x0^11 * x1^2
  + -4377334030967447/281474976710656 * x0^10 * x1^3
  + -4807703158898031/562949953421312 * x0^9 * x1^4
  + -3460835615315823/281474976710656 * x0^8 * x1^5
  + 7976405635411601/1125899906842624 * x0^7 * x1^6
  + -3591427558823205/281474976710656 * x0^6 * x1^7
  + 3849068822180371/281474976710656 * x0^5 * x1^8
  + -1274824735914413/70368744177664 * x0^4 * x1^9
  + 4353669005519315/140737488355328 * x0^3 * x1^10
  + -594331074584957/281474976710656 * x0^2 * x1^11
  + 6556864866492975/140737488355328 * x0 * x1^12
  + -4697592290950953/1125899906842624 * x1^13
  + 6460987367366755/281474976710656 * x0^14
  + -5447169764254047/70368744177664 * x0^13 * x1
  + 161376582679677/17592186044416 * x0^12 * x1^2
  + -1276483306361955/35184372088832 * x0^11 * x1^3
  + 307659753256799/8796093022208 * x0^10 * x1^4
  + -4769940672960193/281474976710656 * x0^9 * x1^5
  + 5915854210870951/281474976710656 * x0^8 * x1^6
  + -3385017558148737/140737488355328 * x0^7 * x1^7
  + 2633532428035743/140737488355328 * x0^6 * x1^8
  + -5320343931808695/562949953421312 * x0^5 * x1^9
  + 2338057307488645/140737488355328 * x0^4 * x1^10
  + -5181833744396495/2251799813685248 * x0^3 * x1^11
  + -6227374652627665/9007199254740992 * x0^2 * x1^12
  + -6322736188844491/70368744177664 * x0 * x1^13
  + 8567389335308119/281474976710656 * x1^14
  + -7545645399820303/1125899906842624 * x0^15
  + -1547416184081853/17592186044416 * x0^14 * x1
  + -4933342356261159/140737488355328 * x0^13 * x1^2
  + -8374990114104945/281474976710656 * x0^12 * x1^3
  + 7807784419295151/9007199254740992 * x0^11 * x1^4
  + -1425315734319621/140737488355328 * x0^10 * x1^5
  + 8887521792881745/1125899906842624 * x0^9 * x1^6
  + -5966502525792673/2251799813685248 * x0^8 * x1^7
  + 5446744926513245/2251799813685248 * x0^7 * x1^8
  + -2582129525554127/140737488355328 * x0^6 * x1^9
  + -5282406259187943/1125899906842624 * x0^5 * x1^10
  + -5568838362905851/281474976710656 * x0^4 * x1^11
  + 614107538951347/8796093022208 * x0^3 * x1^12
  + 8028953094398407/281474976710656 * x0^2 * x1^13
  + 567231563567641/4398046511104 * x0 * x1^14
  + -200864562183983/2199023255552 * x1^15
  + 1443637528270359/17592186044416 * x0^16
  + -2864015215698495/35184372088832 * x0^15 * x1
  + -4249663066329721/140737488355328 * x0^14 * x1^2
  + -6548703115132873/140737488355328 * x0^13 * x1^3
  + 5205302824137871/1125899906842624 * x0^12 * x1^4
  + -2842864201221787/281474976710656 * x0^11 * x1^5
  + -4807586391055945/562949953421312 * x0^10 * x1^6
  + -3696942926776301/70368744177664 * x0^9 * x1^7
  + -7162710363845589/562949953421312 * x0^8 * x1^8
  + -7434900557979757/140737488355328 * x0^7 * x1^9
  + 16569273797771/1099511627776 * x0^6 * x1^10
  + -1561938156324691/35184372088832 * x0^5 * x1^11
  + 4611741471799823/281474976710656 * x0^4 * x1^12
  + -5622159709147003/70368744177664 * x0^3 * x1^13
  + -6613441217045127/1125899906842624 * x0^2 * x1^14
  + -2738676143769501/35184372088832 * x0 * x1^15
  + 6029929589375655/70368744177664 * x1^16
  + 7903002711235039/70368744177664 * x0^17
  + -3208284247582969/35184372088832 * x0^16 * x1
  + 4177547328911745/140737488355328 * x0^15 * x1^2
  + -735875889492049/17592186044416 * x0^14 * x1^3
  + 5028424844914209/70368744177664 * x0^13 * x1^4
  + -7156106648605627/2251799813685248 * x0^12 * x1^5
  + 665540457656905/8796093022208 * x0^11 * x1^6
  + -6063535238521521/281474976710656 * x0^10 * x1^7
  + 5574982618460765/140737488355328 * x0^9 * x1^8
  + -5880659716421149/140737488355328 * x0^8 * x1^9
  + 5976499537950799/281474976710656 * x0^7 * x1^10
  + -8226460094227423/140737488355328 * x0^6 * x1^11
  + 5140455420885349/4503599627370496 * x0^5 * x1^12
  + -5010480446763139/140737488355328 * x0^4 * x1^13
  + 3236452249478767/281474976710656 * x0^3 * x1^14
  + -2811208242733191/140737488355328 * x0^2 * x1^15
  + 2270238672756669/140737488355328 * x0 * x1^16
  + -618298656102721/17592186044416 * x1^17
  + 2698174894050569/70368744177664 * x0^18
  + -5741847365058001/140737488355328 * x0^17 * x1
  + 117350701394713/4398046511104 * x0^16 * x1^2
  + -6298126846978747/562949953421312 * x0^15 * x1^3
  + 8431370951136869/281474976710656 * x0^14 * x1^4
  + -2505696115354715/1125899906842624 * x0^13 * x1^5
  + 2525835485654547/35184372088832 * x0^12 * x1^6
  + 8256000672178759/562949953421312 * x0^11 * x1^7
  + 1585815258427791/140737488355328 * x0^10 * x1^8
  + -1551051772375519/70368744177664 * x0^9 * x1^9
  + 8588863868936821/281474976710656 * x0^8 * x1^10
  + 2891714455882431/140737488355328 * x0^7 * x1^11
  + 5647530918647127/140737488355328 * x0^6 * x1^12
  + 5123181980727821/281474976710656 * x0^5 * x1^13
  + 5346106536588071/281474976710656 * x0^4 * x1^14
  + 7590001375384527/1125899906842624 * x0^3 * x1^15
  + 4873747239100867/562949953421312 * x0^2 * x1^16
  + 1600888910380451/9007199254740992 * x0 * x1^17
  + 193080597425253/35184372088832 * x1^18.
  
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