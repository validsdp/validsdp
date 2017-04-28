Require Import Reals.
From ValidSDP Require Import validsdp.
Local Open Scope R_scope.

Let sigma x0 x1 x2 : R := 6444365281246187/9007199254740992
         + 6312265263179769/576460752303423488 * x0
         + 6621776382116655/144115188075855872 * x1
         + -185496562805861/4503599627370496 * x2
         + 2416248187670441/4503599627370496 * x0^2
         + 5492430780988505/2305843009213693952 * x0 * x1
         + 5399350334336355/9007199254740992 * x1^2
         + 2775867384476511/72057594037927936 * x0 * x2
         + 6483681914198991/576460752303423488 * x1 * x2
         + 2659792549913679/4503599627370496 * x2^2
         + 2117156699109693/18014398509481984 * x0^3
         + 7324243373258689/72057594037927936 * x0^2 * x1
         + 5102009265014683/36028797018963968 * x0 * x1^2
         + 3559734688910025/36028797018963968 * x1^3
         + -5679254056549573/72057594037927936 * x0^2 * x2
         + -1770164427185237/36028797018963968 * x0 * x1 * x2
         + -2562963200769027/72057594037927936 * x1^2 * x2
         + 5769433788981365/36028797018963968 * x0 * x2^2
         + 7548762259869971/72057594037927936 * x1 * x2^2
         + -3538613895383109/72057594037927936 * x2^3
         + 1328789540631521/1125899906842624 * x0^4
         + -1855173755015043/9007199254740992 * x0^3 * x1
         + 2557767583672237/2251799813685248 * x0^2 * x1^2
         + -3462699602642395/9007199254740992 * x0 * x1^3
         + 7284044249240483/4503599627370496 * x1^4
         + 5263524722980771/36028797018963968 * x0^3 * x2
         + 144788199285567/18014398509481984 * x0^2 * x1 * x2
         + 1831673356681769/18014398509481984 * x0 * x1^2 * x2
         + 3484693834948841/36028797018963968 * x1^3 * x2
         + 4245018932645721/4503599627370496 * x0^2 * x2^2
         + -353526205012855/2251799813685248 * x0 * x1 * x2^2
         + 2324174681675653/2251799813685248 * x1^2 * x2^2
         + 3833151841760419/18014398509481984 * x0 * x2^3
         + 2941798320053223/72057594037927936 * x1 * x2^3
         + 1944708727800615/1125899906842624 * x2^4.

Let sigma1 x0 x1 x2 : R := 2238448784199197/4503599627370496
         + -7081956584605647/72057594037927936 * x0
         + -8095256989233253/288230376151711744 * x1
         + -5081574377800643/576460752303423488 * x2
         + 6018099001714223/18014398509481984 * x0^2
         + -30139342649847/1125899906842624 * x0 * x1
         + 8383324917719011/18014398509481984 * x1^2
         + -5487532759550775/288230376151711744 * x0 * x2
         + 5995950258377873/2305843009213693952 * x1 * x2
         + 8282785251080307/18014398509481984 * x2^2
         + -541778131690975/9007199254740992 * x0^3
         + -7290596405711811/576460752303423488 * x0^2 * x1
         + 3678758018224447/288230376151711744 * x0 * x1^2
         + 2513546562261607/288230376151711744 * x1^3
         + -717353212593637/36028797018963968 * x0^2 * x2
         + -6468496630616151/2305843009213693952 * x0 * x1 * x2
         + -4253168427456647/1152921504606846976 * x1^2 * x2
         + 2838432209735679/288230376151711744 * x0 * x2^2
         + 6398208700392841/576460752303423488 * x1 * x2^2
         + -3686553544012965/288230376151711744 * x2^3
         + 2832741523587629/4503599627370496 * x0^4
         + -820673162760289/18014398509481984 * x0^3 * x1
         + 36970644880265/70368744177664 * x0^2 * x1^2
         + -7091093352421131/144115188075855872 * x0 * x1^3
         + 222479320665527/281474976710656 * x1^4
         + -5920263192513033/288230376151711744 * x0^3 * x2
         + 86019135108721/4503599627370496 * x0^2 * x1 * x2
         + -3581037718886157/9223372036854775808 * x0 * x1^2 * x2
         + 541587445016049/36028797018963968 * x1^3 * x2
         + 2306452544747269/4503599627370496 * x0^2 * x2^2
         + -2885589273342991/72057594037927936 * x0 * x1 * x2^2
         + 4958911087255367/9007199254740992 * x1^2 * x2^2
         + 3714775807673741/576460752303423488 * x0 * x2^3
         + 4558527826146687/288230376151711744 * x1 * x2^3
         + 1751295812746853/2251799813685248 * x2^4
         + -8298022908743093/72057594037927936 * x0^5
         + -6995141011474289/72057594037927936 * x0^4 * x1
         + -906911613956325/9007199254740992 * x0^3 * x1^2
         + -4516111377899479/72057594037927936 * x0^2 * x1^3
         + -628700413433465/4503599627370496 * x0 * x1^4
         + -7914662856350805/144115188075855872 * x1^5
         + 2004387752491777/36028797018963968 * x0^4 * x2
         + 293684893385199/4503599627370496 * x0^3 * x1 * x2
         + 6643594431463215/288230376151711744 * x0^2 * x1^2 * x2
         + 5628209625281181/72057594037927936 * x0 * x1^3 * x2
         + 2038641075471393/144115188075855872 * x1^4 * x2
         + -311007039610149/2251799813685248 * x0^3 * x2^2
         + -8771543598063923/144115188075855872 * x0^2 * x1 * x2^2
         + -4640037065113525/36028797018963968 * x0 * x1^2 * x2^2
         + -4806722763336115/72057594037927936 * x1^3 * x2^2
         + 4375085894604395/144115188075855872 * x0^2 * x2^3
         + 4729553562804721/72057594037927936 * x0 * x1 * x2^3
         + 7939122053219573/576460752303423488 * x1^2 * x2^3
         + -7015044277992411/36028797018963968 * x0 * x2^4
         + -7613398074203915/72057594037927936 * x1 * x2^4
         + 1195520686271805/288230376151711744 * x2^5
         + 7154056313052153/144115188075855872 * x0^6
         + 4511872077787229/72057594037927936 * x0^5 * x1
         + 4655591819919163/72057594037927936 * x0^4 * x1^2
         + 4608448381322171/72057594037927936 * x0^3 * x1^3
         + 7553102807877403/144115188075855872 * x0^2 * x1^4
         + 1414408159002659/36028797018963968 * x0 * x1^5
         + 4147770253630557/288230376151711744 * x1^6
         + -4956636040779497/144115188075855872 * x0^5 * x2
         + -5861766429081453/144115188075855872 * x0^4 * x1 * x2
         + -5385581057667679/144115188075855872 * x0^3 * x1^2 * x2
         + -7214734708951869/144115188075855872 * x0^2 * x1^3 * x2
         + -1133047824711617/36028797018963968 * x0 * x1^4 * x2
         + -8929442930261787/1152921504606846976 * x1^5 * x2
         + 4625068670240235/72057594037927936 * x0^4 * x2^2
         + 8498398020785319/144115188075855872 * x0^3 * x1 * x2^2
         + 7796742623941989/144115188075855872 * x0^2 * x1^2 * x2^2
         + 6805340246135981/144115188075855872 * x0 * x1^3 * x2^2
         + 2487188163897569/144115188075855872 * x1^4 * x2^2
         + -2282908947939141/72057594037927936 * x0^3 * x2^3
         + -6389150420567317/144115188075855872 * x0^2 * x1 * x2^3
         + -1849144206170525/72057594037927936 * x0 * x1^2 * x2^3
         + -3362503951811703/576460752303423488 * x1^3 * x2^3
         + 8177541134906045/144115188075855872 * x0^2 * x2^4
         + 8078528346835259/144115188075855872 * x0 * x1 * x2^4
         + 1195325563618785/72057594037927936 * x1^2 * x2^4
         + -111546168491751/18014398509481984 * x0 * x2^5
         + -5156218193544123/2305843009213693952 * x1 * x2^5
         + 2931994166378865/2305843009213693952 * x2^6.

Let p x0 x1 x2 : R :=
     376932522065681012931/295147905179352825856
    + 8509962722502765/295147905179352825856 * x0
    + 4810786678983139/147573952589676412928 * x1
    + 8195275705635465/1180591620717411303424 * x2
    + -5286590888873701/4503599627370496 * x0^2
    + 3142771579399875/36028797018963968 * x0 * x1
    + -591108560874675/281474976710656 * x1^2
    + 1261458973270647/2251799813685248 * x0 * x2
    + 5929053759940775/72057594037927936 * x1 * x2
    + -1259727915632095/562949953421312 * x2^2
    + 1149275400895391/4503599627370496 * x0^3
    + 7285847311712275/18014398509481984 * x0^2 * x1
    + 8440266932050133/18014398509481984 * x0 * x1^2
    + 4371217067606495/36028797018963968 * x1^3
    + -458360830646393/1125899906842624 * x0^2 * x2
    + -2813070140505775/4503599627370496 * x0 * x1 * x2
    + -8737122075031031/72057594037927936 * x1^2 * x2
    + 3341105181056463/4503599627370496 * x0 * x2^2
    + 7431847970290251/18014398509481984 * x1 * x2^2
    + -7134326653543871/288230376151711744 * x2^3
    + -4419035466710003/36028797018963968 * x0^4
    + -3191026702181451/18014398509481984 * x0^3 * x1
    + -8852489850214139/72057594037927936 * x0^2 * x1^2
    + -2762344079633701/36028797018963968 * x0 * x1^3
    + -974190988861453/36028797018963968 * x1^4
    + 4592531851313069/36028797018963968 * x0^3 * x2
    + 1897745899402969/9007199254740992 * x0^2 * x1 * x2
    + 3929173054132589/36028797018963968 * x0 * x1^2 * x2
    + 5952875244748005/288230376151711744 * x1^3 * x2
    + -5462054773810051/36028797018963968 * x0^2 * x2^2
    + -5346287477580991/36028797018963968 * x0 * x1 * x2^2
    + -92562462037723/2251799813685248 * x1^2 * x2^2
    + 8810307269401287/576460752303423488 * x0 * x2^3
    + 3135835432654057/576460752303423488 * x1 * x2^3
    + -569947876840979/288230376151711744 * x2^4.

Lemma sigma_pos (x0 x1 x2 : R) : sigma x0 x1 x2 >= 0.
unfold sigma.
Time validsdp.
Time Qed.

Lemma sigma1_pos (x0 x1 x2 : R) : sigma1 x0 x1 x2 >= 0.
unfold sigma1.
Time validsdp.
Time Qed.

Lemma p_ind (x0 x1 x2 : R) :
  (p (1/4 * (4/5 * x0 + 2/5 * x1^2))
     (1/4 * (-3/5 * (x1)^2 + 3/10 * x2^2))
     (1/4 * (1/2 * x2 + 2/5 * x0^2)))
  - (sigma x0 x1 x2) * (p x0 x1 x2)
  - (sigma1 x0 x1 x2) * (x0^2 + x1^2 + x2^2 - 1) >= 0.
unfold p, sigma, sigma1.
Time validsdp.
Time Qed.