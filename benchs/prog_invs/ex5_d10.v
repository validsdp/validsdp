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
  1421026946512084771/1152921504606846976
  + -6630000031628851/73786976294838206464 * x0
  + -3933208116550259/36893488147419103232 * x1
  + -5585009827394751/73786976294838206464 * x2
  + -8898596240520743/1125899906842624 * x0^2
  + 177668756661025/35184372088832 * x0 * x1
  + -1702230871884183/281474976710656 * x1^2
  + 2924250017231247/562949953421312 * x0 * x2
  + -6474799127721193/36028797018963968 * x1 * x2
  + -2692472168557187/281474976710656 * x2^2
  + 2875248242849863/281474976710656 * x0^3
  + -6658411399750421/2251799813685248 * x0^2 * x1
  + 6308717576875335/1125899906842624 * x0 * x1^2
  + 7332585746798555/1125899906842624 * x1^3
  + -6017751271834935/2251799813685248 * x0^2 * x2
  + -4286603585986633/144115188075855872 * x0 * x1 * x2
  + 6862846018898171/36028797018963968 * x1^2 * x2
  + 402454587338777/70368744177664 * x0 * x2^2
  + 2094813521515229/2251799813685248 * x1 * x2^2
  + 8030528812630073/4503599627370496 * x2^3
  + -1574224770585775/2251799813685248 * x0^4
  + -7480187434905181/2251799813685248 * x0^3 * x1
  + -3117029437514067/281474976710656 * x0^2 * x1^2
  + -2568557728255995/9007199254740992 * x0 * x1^3
  + -6916727908384501/562949953421312 * x1^4
  + -3157052443349103/1125899906842624 * x0^3 * x2
  + -4832348723198539/9007199254740992 * x0^2 * x1 * x2
  + -4614753068861651/144115188075855872 * x0 * x1^2 * x2
  + -744397633079693/9007199254740992 * x1^3 * x2
  + -4159522943719075/562949953421312 * x0^2 * x2^2
  + -8047022185300387/288230376151711744 * x0 * x1 * x2^2
  + -3074803090114507/281474976710656 * x1^2 * x2^2
  + 6170399569250841/18014398509481984 * x0 * x2^3
  + 3354705647994193/18014398509481984 * x1 * x2^3
  + -3517060783595587/281474976710656 * x2^4
  + 6213629868088913/562949953421312 * x0^5
  + 2876248890839323/18014398509481984 * x0^4 * x1
  + 1507023037084721/1125899906842624 * x0^3 * x1^2
  + -2126929448847769/2251799813685248 * x0^2 * x1^3
  + 6024826517703191/4503599627370496 * x0 * x1^4
  + -1371277133266739/4503599627370496 * x1^5
  + 7863239443690473/18014398509481984 * x0^4 * x2
  + -6559964211227871/36028797018963968 * x0^3 * x1 * x2
  + 8783727125756387/9007199254740992 * x0^2 * x1^2 * x2
  + 5704942806051159/36028797018963968 * x0 * x1^3 * x2
  + 8756361016785361/36028797018963968 * x1^4 * x2
  + 7482338296705419/2251799813685248 * x0^3 * x2^2
  + 6693768358890725/9007199254740992 * x0^2 * x1 * x2^2
  + 6245191320850279/4503599627370496 * x0 * x1^2 * x2^2
  + -4841196120274125/9007199254740992 * x1^3 * x2^2
  + 734541080070727/562949953421312 * x0^2 * x2^3
  + 1774848052560857/9007199254740992 * x0 * x1 * x2^3
  + 687208093538261/2251799813685248 * x1^2 * x2^3
  + 8336869203808775/4503599627370496 * x0 * x2^4
  + 5986165847343767/36028797018963968 * x1 * x2^4
  + 4344795492009295/18014398509481984 * x2^5
  + -4401142903317425/281474976710656 * x0^6
  + 4738395188855137/2251799813685248 * x0^5 * x1
  + -8439059469645557/2251799813685248 * x0^4 * x1^2
  + 8956106457629543/36028797018963968 * x0^3 * x1^3
  + -3582082708917791/562949953421312 * x0^2 * x1^4
  + 4234821242268779/36028797018963968 * x0 * x1^5
  + -5226379126186429/562949953421312 * x1^6
  + 6627409576904819/9007199254740992 * x0^5 * x2
  + 7563501447123455/72057594037927936 * x0^4 * x1 * x2
  + 6548119777464153/9007199254740992 * x0^3 * x1^2 * x2
  + 6395853893731711/18014398509481984 * x0^2 * x1^3 * x2
  + 5948327084989577/36028797018963968 * x0 * x1^4 * x2
  + 3344913527375621/18014398509481984 * x1^5 * x2
  + -3436185454341835/1125899906842624 * x0^4 * x2^2
  + 1913332712679723/2251799813685248 * x0^3 * x1 * x2^2
  + -8333334818205889/2251799813685248 * x0^2 * x1^2 * x2^2
  + 3005670298969891/9007199254740992 * x0 * x1^3 * x2^2
  + -950868142675523/140737488355328 * x1^4 * x2^2
  + 1264575684583999/1125899906842624 * x0^3 * x2^3
  + 5803243540657515/18014398509481984 * x0^2 * x1 * x2^3
  + 5505287636199235/18014398509481984 * x0 * x1^2 * x2^3
  + 4383956019669469/36028797018963968 * x1^3 * x2^3
  + -5958995627852181/1125899906842624 * x0^2 * x2^4
  + 857350393720643/2251799813685248 * x0 * x1 * x2^4
  + -7345870082877231/1125899906842624 * x1^2 * x2^4
  + 5412034442180925/144115188075855872 * x0 * x2^5
  + 6056584436010805/36028797018963968 * x1 * x2^5
  + -8809076779680525/1125899906842624 * x2^6
  + -5284249806636947/562949953421312 * x0^7
  + -4313792352008753/9007199254740992 * x0^6 * x1
  + 4731724183163125/562949953421312 * x0^5 * x1^2
  + 2647205262372479/2251799813685248 * x0^4 * x1^3
  + 6951723323622667/2251799813685248 * x0^3 * x1^4
  + 4395079758567021/4503599627370496 * x0^2 * x1^5
  + 3299763331237833/1125899906842624 * x0 * x1^6
  + 7926515704283251/144115188075855872 * x1^7
  + -4267875980600205/4503599627370496 * x0^6 * x2
  + -6304366013163957/72057594037927936 * x0^5 * x1 * x2
  + 1895910498103197/2251799813685248 * x0^4 * x1^2 * x2
  + 7601317384868421/18014398509481984 * x0^3 * x1^3 * x2
  + 5294300163547925/9007199254740992 * x0^2 * x1^4 * x2
  + 3486627368896469/18014398509481984 * x0 * x1^5 * x2
  + 4746831213966693/18014398509481984 * x1^6 * x2
  + 7849804546973259/1125899906842624 * x0^5 * x2^2
  + 736294367354619/1125899906842624 * x0^4 * x1 * x2^2
  + 2214134939046379/1125899906842624 * x0^3 * x1^2 * x2^2
  + 822857220580879/1125899906842624 * x0^2 * x1^3 * x2^2
  + 3753098538775855/4503599627370496 * x0 * x1^4 * x2^2
  + -2369304851382011/18014398509481984 * x1^5 * x2^2
  + 3703964761688841/2251799813685248 * x0^4 * x2^3
  + 6446444579347021/18014398509481984 * x0^3 * x1 * x2^3
  + 6810826751893781/9007199254740992 * x0^2 * x1^2 * x2^3
  + 5068563179262521/36028797018963968 * x0 * x1^3 * x2^3
  + 5584902369147235/36028797018963968 * x1^4 * x2^3
  + 235718028498807/70368744177664 * x0^3 * x2^4
  + 5304394675129065/9007199254740992 * x0^2 * x1 * x2^4
  + 8039382245999711/9007199254740992 * x0 * x1^2 * x2^4
  + 6373511546383547/576460752303423488 * x1^3 * x2^4
  + 5241661784057397/4503599627370496 * x0^2 * x2^5
  + 6104979320654185/36028797018963968 * x0 * x1 * x2^5
  + 1597877057764461/9007199254740992 * x1^2 * x2^5
  + 6888804150965525/2251799813685248 * x0 * x2^6
  + 8992475181789331/36028797018963968 * x1 * x2^6
  + 5550989417755549/9007199254740992 * x2^7
  + -1240544598245425/140737488355328 * x0^8
  + -655853527177199/281474976710656 * x0^7 * x1
  + 3735727442648207/562949953421312 * x0^6 * x1^2
  + 2939198805715787/1125899906842624 * x0^5 * x1^3
  + -3266451546386095/2251799813685248 * x0^4 * x1^4
  + 5066884213410729/2251799813685248 * x0^3 * x1^5
  + -4228272075831457/1125899906842624 * x0^2 * x1^6
  + 5913448001618955/4503599627370496 * x0 * x1^7
  + -1909131541425477/281474976710656 * x1^8
  + -2656698109852843/1125899906842624 * x0^7 * x2
  + -4541022158200599/9007199254740992 * x0^6 * x1 * x2
  + 951474413639795/1125899906842624 * x0^5 * x1^2 * x2
  + 4604320986893165/9007199254740992 * x0^4 * x1^3 * x2
  + 3027696849837/4398046511104 * x0^3 * x1^4 * x2
  + 6584475051610251/18014398509481984 * x0^2 * x1^5 * x2
  + 3287793976110571/18014398509481984 * x0 * x1^6 * x2
  + 1787647529516119/9007199254740992 * x1^7 * x2
  + 1593018391225583/281474976710656 * x0^6 * x2^2
  + 209115920172965/281474976710656 * x0^5 * x1 * x2^2
  + -6197781411289005/2251799813685248 * x0^4 * x1^2 * x2^2
  + 4398164619427345/4503599627370496 * x0^3 * x1^3 * x2^2
  + -1144011942926683/281474976710656 * x0^2 * x1^4 * x2^2
  + 4735547818984465/18014398509481984 * x0 * x1^5 * x2^2
  + -6121819502578687/1125899906842624 * x1^6 * x2^2
  + 8817825493448053/4503599627370496 * x0^5 * x2^3
  + 6936296752245487/18014398509481984 * x0^4 * x1 * x2^3
  + 7162423813112049/9007199254740992 * x0^3 * x1^2 * x2^3
  + 1024380040839259/4503599627370496 * x0^2 * x1^3 * x2^3
  + 2298861900387581/36028797018963968 * x0 * x1^4 * x2^3
  + 4801234342003679/72057594037927936 * x1^5 * x2^3
  + -2390063499625245/2251799813685248 * x0^4 * x2^4
  + 6807048109269117/9007199254740992 * x0^3 * x1 * x2^4
  + -2269132249523453/562949953421312 * x0^2 * x1^2 * x2^4
  + 1436364652474651/9007199254740992 * x0 * x1^3 * x2^4
  + -6012490809863527/1125899906842624 * x1^4 * x2^4
  + 482454351753117/281474976710656 * x0^3 * x2^5
  + 4616646334543689/18014398509481984 * x0^2 * x1 * x2^5
  + 8146774062563221/72057594037927936 * x0 * x1^2 * x2^5
  + 3106392529242145/72057594037927936 * x1^3 * x2^5
  + -7586459042137521/2251799813685248 * x0^2 * x2^6
  + 2617084778747517/9007199254740992 * x0 * x1 * x2^6
  + -5872253385696507/1125899906842624 * x1^2 * x2^6
  + 883160650541419/1125899906842624 * x0 * x2^7
  + 5735242027326321/72057594037927936 * x1 * x2^7
  + -6622866566695563/1125899906842624 * x2^8
  + 2781898779601979/70368744177664 * x0^9
  + -2625858454487963/4503599627370496 * x0^8 * x1
  + 3103585828828421/140737488355328 * x0^7 * x1^2
  + 8129926480885395/2251799813685248 * x0^6 * x1^3
  + 306594114640495/35184372088832 * x0^5 * x1^4
  + 3072432805639617/1125899906842624 * x0^4 * x1^5
  + 1340649994610823/281474976710656 * x0^3 * x1^6
  + 7623680531230523/9007199254740992 * x0^2 * x1^7
  + 2877668497980841/562949953421312 * x0 * x1^8
  + 4244979350010825/4503599627370496 * x1^9
  + -7326305472797825/36028797018963968 * x0^8 * x2
  + -1965762849216605/4503599627370496 * x0^7 * x1 * x2
  + 6995081291888263/4503599627370496 * x0^6 * x1^2 * x2
  + 4795693565456567/9007199254740992 * x0^5 * x1^3 * x2
  + 5149314836251367/4503599627370496 * x0^4 * x1^4 * x2
  + 5895410455284407/18014398509481984 * x0^3 * x1^5 * x2
  + 4738149055994569/9007199254740992 * x0^2 * x1^6 * x2
  + -4728404742810947/144115188075855872 * x0 * x1^7 * x2
  + 5310921057756627/9007199254740992 * x1^8 * x2
  + 6061257881428395/281474976710656 * x0^7 * x2^2
  + 6605565067257321/4503599627370496 * x0^6 * x1 * x2^2
  + 5870696712011233/2251799813685248 * x0^5 * x1^2 * x2^2
  + 1200915536656133/1125899906842624 * x0^4 * x1^3 * x2^2
  + 1052621795500041/1125899906842624 * x0^3 * x1^4 * x2^2
  + 6321988371423043/36028797018963968 * x0^2 * x1^5 * x2^2
  + 898953771529553/562949953421312 * x0 * x1^6 * x2^2
  + 6578435334820505/18014398509481984 * x1^7 * x2^2
  + 7547344035254005/2251799813685248 * x0^6 * x2^3
  + 8168486367941385/18014398509481984 * x0^5 * x1 * x2^3
  + 4692002313557901/4503599627370496 * x0^4 * x1^2 * x2^3
  + 7938802119819973/36028797018963968 * x0^3 * x1^3 * x2^3
  + 3724457296276585/18014398509481984 * x0^2 * x1^4 * x2^3
  + -4346893438180435/144115188075855872 * x0 * x1^5 * x2^3
  + 724132903901127/2251799813685248 * x1^6 * x2^3
  + 4782805372760247/562949953421312 * x0^5 * x2^4
  + 2498421396414849/2251799813685248 * x0^4 * x1 * x2^4
  + 7819281897695503/9007199254740992 * x0^3 * x1^2 * x2^4
  + 1556988559862645/9007199254740992 * x0^2 * x1^3 * x2^4
  + 5098650818774279/4503599627370496 * x0 * x1^4 * x2^4
  + 604427587576671/2251799813685248 * x1^5 * x2^4
  + 5753945167866865/2251799813685248 * x0^4 * x2^5
  + 3028868545152071/9007199254740992 * x0^3 * x1 * x2^5
  + 7231283370925269/36028797018963968 * x0^2 * x1^2 * x2^5
  + -5868663323004335/288230376151711744 * x0 * x1^3 * x2^5
  + 2972594499405517/9007199254740992 * x1^4 * x2^5
  + 4981626195780829/1125899906842624 * x0^3 * x2^6
  + 7770626159172459/18014398509481984 * x0^2 * x1 * x2^6
  + 1773133161976887/1125899906842624 * x0 * x1^2 * x2^6
  + 5333362379068457/18014398509481984 * x1^3 * x2^6
  + 5480592836288981/4503599627370496 * x0^2 * x2^7
  + 5008967191466593/72057594037927936 * x0 * x1 * x2^7
  + 8149543919926933/18014398509481984 * x1^2 * x2^7
  + 1300014902180359/281474976710656 * x0 * x2^8
  + 8211086663789469/18014398509481984 * x1 * x2^8
  + 7475546721060563/4503599627370496 * x2^9
  + -5456859217210719/281474976710656 * x0^10
  + 2730101472572061/1125899906842624 * x0^9 * x1
  + -1832584090563045/70368744177664 * x0^8 * x1^2
  + 408602071863107/140737488355328 * x0^7 * x1^3
  + -4018333817431521/140737488355328 * x0^6 * x1^4
  + 8108278408554731/18014398509481984 * x0^5 * x1^5
  + -1067872601537871/35184372088832 * x0^4 * x1^6
  + -5688648052170827/2251799813685248 * x0^3 * x1^7
  + -4679568942805655/140737488355328 * x0^2 * x1^8
  + -1184046851197677/281474976710656 * x0 * x1^9
  + -7444359530433441/140737488355328 * x1^10
  + 6109038453335873/2251799813685248 * x0^9 * x2
  + 5089919582146021/72057594037927936 * x0^8 * x1 * x2
  + 7133458624087051/4503599627370496 * x0^7 * x1^2 * x2
  + 4656244882010497/18014398509481984 * x0^6 * x1^3 * x2
  + 2975009190637295/2251799813685248 * x0^5 * x1^4 * x2
  + -3327092703024799/18014398509481984 * x0^4 * x1^5 * x2
  + 4073999089893927/4503599627370496 * x0^3 * x1^6 * x2
  + -1948649567679991/2251799813685248 * x0^2 * x1^7 * x2
  + 5540822632971649/4503599627370496 * x0 * x1^8 * x2
  + -5082359026371995/4503599627370496 * x1^9 * x2
  + -7274359329157011/281474976710656 * x0^8 * x2^2
  + 7056016588012825/4503599627370496 * x0^7 * x1 * x2^2
  + -6009611991385207/281474976710656 * x0^6 * x1^2 * x2^2
  + 3277067929100483/4503599627370496 * x0^5 * x1^3 * x2^2
  + -5317879172505231/281474976710656 * x0^4 * x1^4 * x2^2
  + -4267799583237355/18014398509481984 * x0^3 * x1^5 * x2^2
  + -1385144607967867/70368744177664 * x0^2 * x1^6 * x2^2
  + -5854282472230995/36028797018963968 * x0 * x1^7 * x2^2
  + -624490148508225/17592186044416 * x1^8 * x2^2
  + 6833929567670217/2251799813685248 * x0^7 * x2^3
  + 4114726674609919/9007199254740992 * x0^6 * x1 * x2^3
  + 5901918489243619/9007199254740992 * x0^5 * x1^2 * x2^3
  + 4498443412438843/36028797018963968 * x0^4 * x1^3 * x2^3
  + -8479303578775411/1152921504606846976 * x0^3 * x1^4 * x2^3
  + -6194399827203285/36028797018963968 * x0^2 * x1^5 * x2^3
  + 3013833287375483/18014398509481984 * x0 * x1^6 * x2^3
  + -714578627201829/4503599627370496 * x1^7 * x2^3
  + -8252243645738211/281474976710656 * x0^6 * x2^4
  + 7940718767691855/9007199254740992 * x0^5 * x1 * x2^4
  + -5327661117630607/281474976710656 * x0^4 * x1^2 * x2^4
  + -564302963992311/9007199254740992 * x0^3 * x1^3 * x2^4
  + -4917262858057537/281474976710656 * x0^2 * x1^4 * x2^4
  + 8881092184928009/288230376151711744 * x0 * x1^5 * x2^4
  + -131819823557445/4398046511104 * x1^6 * x2^4
  + 2031881634253183/1125899906842624 * x0^5 * x2^5
  + 5720496976784915/18014398509481984 * x0^4 * x1 * x2^5
  + -221346747431175/1125899906842624 * x0^3 * x1^2 * x2^5
  + -6347496427104465/72057594037927936 * x0^2 * x1^3 * x2^5
  + 2868261747652683/72057594037927936 * x0 * x1^4 * x2^5
  + -5162167273644551/144115188075855872 * x1^5 * x2^5
  + -2285253539065321/70368744177664 * x0^4 * x2^6
  + 3898022033636779/18014398509481984 * x0^3 * x1 * x2^6
  + -2778985273237255/140737488355328 * x0^2 * x1^2 * x2^6
  + 2707516830488295/18014398509481984 * x0 * x1^3 * x2^6
  + -8442212943779235/281474976710656 * x1^4 * x2^6
  + 5964923220002527/18014398509481984 * x0^3 * x2^7
  + 1443595627422237/36028797018963968 * x0^2 * x1 * x2^7
  + -2688956634519957/72057594037927936 * x0 * x1^2 * x2^7
  + 5046421232567319/144115188075855872 * x1^3 * x2^7
  + -5184297117273173/140737488355328 * x0^2 * x2^8
  + 148155066047099/1125899906842624 * x0 * x1 * x2^8
  + -4978655289931691/140737488355328 * x1^2 * x2^8
  + 1715801697921923/4503599627370496 * x0 * x2^9
  + 5200863573310467/144115188075855872 * x1 * x2^9
  + -3978994938377675/70368744177664 * x2^10.
  
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
