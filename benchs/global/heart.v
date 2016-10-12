From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (0 - x0) * (x5)^3 + 3 * x0 * x5 * (x6)^2 - x2 * (x6)^3
  + 3 * x2 * x6 * (x5)^2 - x1 * (x4)^3 + 3 * x1 * x4 * (x7)^2 - x3 * (x7)^3
  + 3 * x3 * x7 * (x4)^2 - 9563453/10000000.

Let b1 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x0 + 1/10) * (4/10 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x1 - 4/10) * (1/1 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x2 + 7/10) * (-4/10 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x3 + 7/10) * (4/10 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x4 - 1/10) * (2/10 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x5 + 1/10) * (2/10 - x5).

Let b7 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x6 + 3/10) * (11/10 - x6).

Let b8 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x7 + 11/10) * (-3/10 - x7).

Let lb := -1744/1000.

Let ub := 1369/1000.

Let lb_sigma (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  859681690977733/17179869184.

Let lb_sigma1 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  844962993462023/34359738368 + -160587860682327/68719476736 * x0
  + -228146914180997/34359738368 * x1 + 616364505227097/68719476736 * 
  x2 + 617560226234933/34359738368 * x3 + -125707927640735/68719476736 * 
  x4 + -11940108195153/34359738368 * x5 + 88145903353641/17179869184 * 
  x6 + 1600362159866305/68719476736 * x7 + 268192187830423/8589934592 * 
  x0^2 + -107669618621999/68719476736 * x0 * x1
  + 2607056712558775/68719476736 * x1^2
  + 284299593795963/68719476736 * x0 * x2
  + 361358620332537/68719476736 * x1 * x2
  + 1610236767023659/68719476736 * x2^2
  + 39516019520299/17179869184 * x0 * x3
  + 566792775566839/68719476736 * x1 * x3
  + -130433435224043/17179869184 * x2 * x3
  + 2283125998992025/68719476736 * x3^2
  + -31380054334867/68719476736 * x0 * x4
  + -10147234245677/34359738368 * x1 * x4
  + 11707105638135/8589934592 * x2 * x4
  + 36858110708885/17179869184 * x3 * x4 + 705890579621661/17179869184 * 
  x4^2 + 165145167022903/68719476736 * x0 * x5
  + 14070462212121/34359738368 * x1 * x5
  + -38737236412251/68719476736 * x2 * x5
  + 74280220239029/68719476736 * x3 * x5
  + -746818670057/68719476736 * x4 * x5 + 302879411383081/8589934592 * 
  x5^2 + 50157744599407/8589934592 * x0 * x6
  + 79802568784247/17179869184 * x1 * x6
  + -208286622508489/34359738368 * x2 * x6
  + 178266667216755/68719476736 * x3 * x6
  + 3547155396269/4294967296 * x4 * x6
  + -786864456137809/68719476736 * x5 * x6
  + 445232850077805/17179869184 * x6^2 + 55818953850243/17179869184 * 
  x0 * x7 + 741851166540343/68719476736 * x1 * x7
  + -705649534951261/68719476736 * x2 * x7
  + -1273586251469905/68719476736 * x3 * x7
  + 205812294421653/68719476736 * x4 * x7
  + 40219946746667/34359738368 * x5 * x7
  + 53230216014977/68719476736 * x6 * x7
  + 1501935512176523/68719476736 * x7^2.

Let lb_sigma2 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  1959990073029381/68719476736 + -153585075228009/68719476736 * x0
  + -982233612590445/68719476736 * x1 + 588557397321559/68719476736 * 
  x2 + 882587673172427/68719476736 * x3 + 1025276288007/8589934592 * 
  x4 + -1829940091823/4294967296 * x5 + 3447978107131/8589934592 * x6
  + 521368796929225/34359738368 * x7 + 2094004546633635/68719476736 * 
  x0^2 + -35003491296645/17179869184 * x0 * x1
  + 2805552663301035/68719476736 * x1^2
  + 174907196344967/68719476736 * x0 * x2
  + 572948480243401/68719476736 * x1 * x2
  + 2156626089546029/68719476736 * x2^2
  + 140664245672661/68719476736 * x0 * x3
  + 193981724175009/17179869184 * x1 * x3
  + -567678253134071/68719476736 * x2 * x3
  + 580405739518945/17179869184 * x3^2
  + -22599622914815/68719476736 * x0 * x4
  + -10936628084985/8589934592 * x1 * x4
  + 16466186602983/17179869184 * x2 * x4
  + 18489711135101/17179869184 * x3 * x4
  + 2764316045540579/68719476736 * x4^2
  + 212431938920841/68719476736 * x0 * x5
  + -14091540531909/17179869184 * x1 * x5
  + 16589176895979/68719476736 * x2 * x5
  + 40896162120701/68719476736 * x3 * x5 + 956025193695/68719476736 * 
  x4 * x5 + 1232372447811355/34359738368 * x5^2
  + 220030160766495/68719476736 * x0 * x6
  + -108963981070035/34359738368 * x1 * x6
  + -275604027985571/68719476736 * x2 * x6
  + 24776791510163/34359738368 * x3 * x6
  + 22822436666397/68719476736 * x4 * x6
  + -25299580511975/17179869184 * x5 * x6
  + 959226804724875/34359738368 * x6^2 + 97968072325187/34359738368 * 
  x0 * x7 + 1281458286911913/68719476736 * x1 * x7
  + -774591605865551/68719476736 * x2 * x7
  + -866389074373287/68719476736 * x3 * x7
  + 15902694825031/17179869184 * x4 * x7
  + 23143723820009/34359738368 * x5 * x7
  + 17139796540807/68719476736 * x6 * x7 + 474669673856303/17179869184 * 
  x7^2.

Let lb_sigma3 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  1769419357084771/68719476736 + -5086838254265/2147483648 * x0
  + -371130956872799/68719476736 * x1 + 981291857302071/68719476736 * 
  x2 + 1220242051988073/68719476736 * x3 + -87695035868607/68719476736 * 
  x4 + -26047655841605/34359738368 * x5 + 26972566646739/4294967296 * 
  x6 + 186247734403037/8589934592 * x7 + 897278748892643/34359738368 * 
  x0^2 + -81705341826199/68719476736 * x0 * x1
  + 725698795906993/17179869184 * x1^2 + 89296045692037/17179869184 * 
  x0 * x2 + 140672853168301/17179869184 * x1 * x2
  + 371052423915295/8589934592 * x2^2 + 75063757334531/34359738368 * 
  x0 * x3 + 308466173851845/34359738368 * x1 * x3
  + -439266186285507/34359738368 * x2 * x3
  + 2349574317459399/68719476736 * x3^2
  + -26736391012123/68719476736 * x0 * x4
  + -16544659166715/34359738368 * x1 * x4
  + 63752610473539/34359738368 * x2 * x4
  + 18649202811343/8589934592 * x3 * x4 + 1368241734257249/34359738368 * 
  x4^2 + 11830788213525/2147483648 * x0 * x5
  + -25876853161985/68719476736 * x1 * x5
  + 1838299012215/34359738368 * x2 * x5
  + 13064213971009/17179869184 * x3 * x5
  + -607650374463/17179869184 * x4 * x5 + 2616160132960685/68719476736 * 
  x5^2 + 788197639685429/68719476736 * x0 * x6
  + 430119850332105/68719476736 * x1 * x6
  + -249500783407089/68719476736 * x2 * x6
  + 23136619210141/34359738368 * x3 * x6
  + 32369974355059/34359738368 * x4 * x6
  + -382652484573795/34359738368 * x5 * x6
  + 1260326174867921/34359738368 * x6^2
  + 92698399997005/34359738368 * x0 * x7
  + 364820817132757/34359738368 * x1 * x7
  + -161748725681107/8589934592 * x2 * x7
  + -71735203258779/4294967296 * x3 * x7
  + 46744602064585/17179869184 * x4 * x7
  + 17633369267709/17179869184 * x5 * x7
  + -32301695343895/17179869184 * x6 * x7
  + 398285472686021/17179869184 * x7^2.

Let lb_sigma4 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  884550246210383/34359738368 + -215039927183453/68719476736 * x0
  + -876000809326151/68719476736 * x1 + 810378757397499/68719476736 * 
  x2 + 134201639615943/34359738368 * x3 + -56053375532967/34359738368 * 
  x4 + -33990756311691/68719476736 * x5 + -171979379935977/68719476736 * 
  x6 + 21915907657347/2147483648 * x7 + 1947882030972857/68719476736 * 
  x0^2 + -57559616499215/34359738368 * x0 * x1
  + 466163281792863/17179869184 * x1^2 + 44573193750567/17179869184 * 
  x0 * x2 + 105148461151821/17179869184 * x1 * x2
  + 485105314975637/17179869184 * x2^2
  + 123834900082217/68719476736 * x0 * x3
  + 233037894555579/34359738368 * x1 * x3
  + -465199220698541/68719476736 * x2 * x3
  + 863819682462355/17179869184 * x3^2
  + -33188236806179/68719476736 * x0 * x4
  + -70725631045215/68719476736 * x1 * x4
  + 56177257673225/34359738368 * x2 * x4
  + 15033616549003/34359738368 * x3 * x4
  + 2780170279696395/68719476736 * x4^2 + 39042273607957/8589934592 * 
  x0 * x5 + -43028314334087/68719476736 * x1 * x5
  + 6122998479797/17179869184 * x2 * x5
  + -4689553223781/34359738368 * x3 * x5
  + -3772886220683/68719476736 * x4 * x5
  + 2223842918781463/68719476736 * x5^2
  + 147430569139537/68719476736 * x0 * x6
  + -12340483822473/4294967296 * x1 * x6
  + -303711955154615/68719476736 * x2 * x6
  + -53741279755289/68719476736 * x3 * x6
  + -20403213255947/68719476736 * x4 * x6
  + -7093113122169/17179869184 * x5 * x6 + 726974451705987/34359738368 * 
  x6^2 + 95810744509779/34359738368 * x0 * x7
  + 90302642839845/8589934592 * x1 * x7
  + -182655303433405/17179869184 * x2 * x7
  + -180625445817153/68719476736 * x3 * x7
  + 73603425638745/68719476736 * x4 * x7
  + 6484083354979/68719476736 * x5 * x7
  + 43724973943025/68719476736 * x6 * x7
  + 2119441832905985/68719476736 * x7^2.

Let lb_sigma5 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  680816451703169/4294967296 + 104778233248719/8589934592 * x0
  + 2166034187503507/68719476736 * x1 + -185956183561749/4294967296 * 
  x2 + -1820179545895769/34359738368 * x3 + 504406075905337/68719476736 * 
  x4 + 1426219060667/68719476736 * x5 + -305010314818109/68719476736 * 
  x6 + -777563150150791/4294967296 * x7 + 1556589872149761/34359738368 * 
  x0^2 + 290381587159491/68719476736 * x0 * x1
  + 1833552613202817/34359738368 * x1^2 + -3376246344341/536870912 * 
  x0 * x2 + -884728965400971/68719476736 * x1 * x2
  + 4142591619048199/68719476736 * x2^2
  + -494936750625573/68719476736 * x0 * x3
  + -269443988624515/17179869184 * x1 * x3
  + 191002216120169/8589934592 * x2 * x3
  + 4870479571861329/68719476736 * x3^2 + 3632122749307/4294967296 * 
  x0 * x4 + 251522244676309/34359738368 * x1 * x4
  + -161676007199869/68719476736 * x2 * x4
  + -57526706094473/17179869184 * x3 * x4
  + 4140222833125231/68719476736 * x4^2
  + -36836057436217/68719476736 * x0 * x5
  + 1572225155365/34359738368 * x1 * x5
  + 17649866152903/68719476736 * x2 * x5
  + 2494178001441/17179869184 * x3 * x5
  + -2705948060859/68719476736 * x4 * x5
  + 1429720139371057/34359738368 * x5^2
  + -149396824010561/68719476736 * x0 * x6
  + -96201169068861/68719476736 * x1 * x6
  + 132773296674329/34359738368 * x2 * x6
  + 17321949319187/4294967296 * x3 * x6
  + -9154229326125/17179869184 * x4 * x6
  + 41139363857791/68719476736 * x5 * x6
  + 3196060828189475/68719476736 * x6^2 + -7080270976327/536870912 * 
  x0 * x7 + -2101285242774297/68719476736 * x1 * x7
  + 3269623326309333/68719476736 * x2 * x7
  + 222926771693567/4294967296 * x3 * x7
  + -394859371342065/68719476736 * x4 * x7 + 158938679337/536870912 * 
  x5 * x7 + 522976463178163/68719476736 * x6 * x7
  + 3829868641195551/17179869184 * x7^2.

Let lb_sigma6 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  1833733504232903/68719476736 + -21073331669433/17179869184 * x0
  + -300055070756733/68719476736 * x1 + 625678345736517/68719476736 * 
  x2 + 627867504649413/34359738368 * x3 + -96102907426259/68719476736 * 
  x4 + 92517050940223/68719476736 * x5 + 49445043689551/2147483648 * 
  x6 + 46299340873157/2147483648 * x7 + 1463723025281007/68719476736 * 
  x0^2 + -54782929799221/68719476736 * x0 * x1
  + 1454834039097253/34359738368 * x1^2
  + 182006096314285/34359738368 * x0 * x2
  + 181980613035299/34359738368 * x1 * x2
  + 2170496812267541/68719476736 * x2^2
  + 115568761915779/68719476736 * x0 * x3
  + 161881341528387/17179869184 * x1 * x3
  + -175833998141595/17179869184 * x2 * x3
  + 602552548800901/17179869184 * x3^2
  + -11959642681597/34359738368 * x0 * x4
  + -13037468592769/68719476736 * x1 * x4
  + 2613615148075/2147483648 * x2 * x4
  + 156653993755367/68719476736 * x3 * x4
  + 2817523887329701/68719476736 * x4^2
  + 376854231811099/34359738368 * x0 * x5
  + 67256574404757/68719476736 * x1 * x5
  + -134926926551555/34359738368 * x2 * x5
  + 3091074085047/8589934592 * x3 * x5 + 12212842408607/68719476736 * 
  x4 * x5 + 1174223089779435/17179869184 * x5^2
  + 199581107233157/34359738368 * x0 * x6
  + 18570315602009/1073741824 * x1 * x6
  + -1567188804390001/68719476736 * x2 * x6
  + -173000545766749/68719476736 * x3 * x6
  + 170334554527097/68719476736 * x4 * x6
  + 11403946061367/68719476736 * x5 * x6
  + 1622900191912131/17179869184 * x6^2
  + 66217631507253/34359738368 * x0 * x7
  + 752141159138179/68719476736 * x1 * x7
  + -447238909475649/34359738368 * x2 * x7
  + -73933179619271/4294967296 * x3 * x7
  + 192037979210547/68719476736 * x4 * x7
  + -52031046253/68719476736 * x5 * x7
  + -733350586571281/68719476736 * x6 * x7
  + 1597341190566345/68719476736 * x7^2.

Let lb_sigma7 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  41831346828981/2147483648 + -1339313653173/17179869184 * x0
  + -268637102128609/34359738368 * x1 + 101042004757015/34359738368 * 
  x2 + 672390054636221/68719476736 * x3 + -130199986508673/34359738368 * 
  x4 + -96692698862667/68719476736 * x5 + -586339153759703/68719476736 * 
  x6 + 1538551254254713/68719476736 * x7 + 235503753399725/68719476736 * 
  x0^2 + 7638611865623/34359738368 * x0 * x1
  + 1045998227355259/68719476736 * x1^2 + -1970408347943/8589934592 * 
  x0 * x2 + -19359003727317/68719476736 * x1 * x2
  + 251546786261611/34359738368 * x2^2 + 14476184767873/68719476736 * 
  x0 * x3 + 421004592971/34359738368 * x1 * x3
  + -2342673769569/2147483648 * x2 * x3 + 1469653375458211/68719476736 * 
  x3^2 + -4063427309793/17179869184 * x0 * x4
  + 37311784290911/34359738368 * x1 * x4
  + 103066441093303/68719476736 * x2 * x4
  + 7827766292449/17179869184 * x3 * x4 + 2758343200184857/68719476736 * 
  x4^2 + 22817613575837/68719476736 * x0 * x5
  + -83606298087701/68719476736 * x1 * x5
  + 111533277704817/34359738368 * x2 * x5
  + -40347111819003/68719476736 * x3 * x5
  + -14077829561997/68719476736 * x4 * x5
  + 495847602590711/68719476736 * x5^2
  + -41587573477817/34359738368 * x0 * x6
  + -759826340242551/68719476736 * x1 * x6
  + 98406661618719/17179869184 * x2 * x6
  + -348298066509213/68719476736 * x3 * x6
  + -58722227078949/68719476736 * x4 * x6
  + 94303325875955/17179869184 * x5 * x6
  + 1455563785264905/68719476736 * x6^2
  + 21392434608161/68719476736 * x0 * x7
  + 34199076863347/17179869184 * x1 * x7
  + -20555118623429/8589934592 * x2 * x7
  + -645058167832609/34359738368 * x3 * x7
  + 89895902048467/34359738368 * x4 * x7
  + -8260296193071/34359738368 * x5 * x7
  + -72865387800651/34359738368 * x6 * x7
  + 1171008722592057/68719476736 * x7^2.

Let lb_sigma8 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  2669240354805637/68719476736 + -53616320149413/17179869184 * x0
  + -393322811201667/34359738368 * x1 + 693853931597263/68719476736 * 
  x2 + -880323311863967/68719476736 * x3 + 14948620544961/34359738368 * 
  x4 + 204116182427/2147483648 * x5 + -96860872648371/68719476736 * x6
  + -14348449537997/17179869184 * x7 + 2195614627369651/68719476736 * 
  x0^2 + -117709887226691/68719476736 * x0 * x1
  + 519690799377967/17179869184 * x1^2
  + 213670709707911/68719476736 * x0 * x2
  + 105955726823593/17179869184 * x1 * x2 + 128995978173347/4294967296 * 
  x2^2 + 83942901494957/68719476736 * x0 * x3
  + 249058100549185/68719476736 * x1 * x3
  + -234273800170999/68719476736 * x2 * x3
  + 200952917053791/4294967296 * x3^2 + -6656704157623/17179869184 * 
  x0 * x4 + -115689954205505/34359738368 * x1 * x4
  + 40866737899455/34359738368 * x2 * x4
  + -124219557491183/68719476736 * x3 * x4
  + 1352124642703473/34359738368 * x4^2 + 1882503336293/536870912 * x0 * x5
  + -37750545401123/68719476736 * x1 * x5
  + 4890280455113/34359738368 * x2 * x5
  + -42438949724395/68719476736 * x3 * x5
  + 854121845621/68719476736 * x4 * x5 + 2424267491628831/68719476736 * 
  x5^2 + 151642154404699/68719476736 * x0 * x6
  + -11430586560745/4294967296 * x1 * x6
  + -293447432404437/68719476736 * x2 * x6
  + -35585345370719/17179869184 * x3 * x6
  + -3829516371993/34359738368 * x4 * x6
  + -32000613571199/68719476736 * x5 * x6
  + 1795172349059897/68719476736 * x6^2
  + 285585844766677/68719476736 * x0 * x7
  + 260094389099975/17179869184 * x1 * x7
  + -480599024502911/34359738368 * x2 * x7
  + 128056119742215/8589934592 * x3 * x7
  + -15677821655347/34359738368 * x4 * x7
  + -803788363869/68719476736 * x5 * x7
  + 172857803058353/68719476736 * x6 * x7
  + 3919038346990619/68719476736 * x7^2.

Let ub_sigma (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  3232176750028611/68719476736.

Let ub_sigma1 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  1669627377453055/34359738368 + -146538712578349/34359738368 * x0
  + -438774172074497/34359738368 * x1 + 115696991633335/17179869184 * 
  x2 + -203214817510109/17179869184 * x3 + -66925392159883/34359738368 * 
  x4 + -34852724777825/17179869184 * x5 + -506466931553193/34359738368 * 
  x6 + 496661768063517/34359738368 * x7 + 2769155448217871/34359738368 * 
  x0^2 + -7921866180413/1073741824 * x0 * x1
  + 3005355896958021/68719476736 * x1^2
  + 157373690528077/34359738368 * x0 * x2
  + 392238241238153/34359738368 * x1 * x2
  + 1773865373780175/34359738368 * x2^2
  + -61917591452379/17179869184 * x0 * x3
  + -321753252621989/34359738368 * x1 * x3
  + 123232861415537/17179869184 * x2 * x3 + 30322640297659/536870912 * 
  x3^2 + -43541141405183/34359738368 * x0 * x4
  + -59954177409885/17179869184 * x1 * x4
  + 17617990035439/8589934592 * x2 * x4
  + -73165184860475/34359738368 * x3 * x4
  + 971350832920087/17179869184 * x4^2
  + -13917266351295/34359738368 * x0 * x5
  + -99365942651131/34359738368 * x1 * x5
  + 31418332230973/17179869184 * x2 * x5
  + -56356898058531/34359738368 * x3 * x5
  + -4482220720877/8589934592 * x4 * x5 + 2037721753211579/34359738368 * 
  x5^2 + -224529019337337/34359738368 * x0 * x6
  + -161134524403011/8589934592 * x1 * x6
  + 26423146998663/2147483648 * x2 * x6
  + -175250991746015/17179869184 * x3 * x6
  + -118642978264907/34359738368 * x4 * x6
  + -86523084090693/34359738368 * x5 * x6
  + 3071519994318849/68719476736 * x6^2 + 32734010376415/4294967296 * 
  x0 * x7 + 163053566265159/8589934592 * x1 * x7
  + -427840136111929/34359738368 * x2 * x7
  + 177931755708677/17179869184 * x3 * x7
  + 8037455028023/2147483648 * x4 * x7 + 12892856930803/4294967296 * 
  x5 * x7 + 347723522879785/17179869184 * x6 * x7
  + 1420892537565883/34359738368 * x7^2.

Let ub_sigma2 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  3108693047219917/68719476736 + -119044747029921/17179869184 * x0
  + -497235267399447/34359738368 * x1 + 145706973908933/17179869184 * 
  x2 + -293857511056667/34359738368 * x3 + -32921746748121/17179869184 * 
  x4 + -131139711008401/34359738368 * x5 + -647935522771759/34359738368 * 
  x6 + 225156246699981/17179869184 * x7 + 1815071987861985/34359738368 * 
  x0^2 + -286967840974217/34359738368 * x0 * x1
  + 993314794433073/17179869184 * x1^2 + 82327091016265/17179869184 * 
  x0 * x2 + 242137079469677/17179869184 * x1 * x2
  + 3432137571197317/68719476736 * x2^2
  + -104918887256539/34359738368 * x0 * x3
  + -61585999055393/8589934592 * x1 * x3
  + 172753450337747/34359738368 * x2 * x3
  + 913395668010783/17179869184 * x3^2
  + -24490124724155/17179869184 * x0 * x4
  + -3918898282961/1073741824 * x1 * x4
  + 70592521526633/34359738368 * x2 * x4
  + -52693566601419/34359738368 * x3 * x4
  + 1921157600461991/34359738368 * x4^2
  + -47132353460889/17179869184 * x0 * x5
  + -145600916443445/34359738368 * x1 * x5
  + 10562337840237/4294967296 * x2 * x5
  + -52516018811075/34359738368 * x3 * x5
  + -26176480276019/34359738368 * x4 * x5
  + 1916233353639195/34359738368 * x5^2
  + -130101130006397/17179869184 * x0 * x6
  + -754613444238201/34359738368 * x1 * x6
  + 467960852256421/34359738368 * x2 * x6
  + -120451703400117/17179869184 * x3 * x6
  + -124271302737869/34359738368 * x4 * x6
  + -66867699335243/17179869184 * x5 * x6
  + 1403308775437491/34359738368 * x6^2
  + 128149033346757/17179869184 * x0 * x7
  + 719029068389331/34359738368 * x1 * x7
  + -194756938649309/17179869184 * x2 * x7
  + 77115050887977/8589934592 * x3 * x7 + 306517482019/67108864 * x4 * x7
  + 134342349973383/34359738368 * x5 * x7
  + 338392787862541/17179869184 * x6 * x7
  + 733761785273757/17179869184 * x7^2.

Let ub_sigma3 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  251518525064325/4294967296 + -125531798878311/34359738368 * x0
  + -25837347428807/8589934592 * x1 + 98087400467809/34359738368 * x2
  + -9123079986007/1073741824 * x3 + 21071313139551/34359738368 * x4
  + -34527774738461/17179869184 * x5 + -179295561467693/34359738368 * 
  x6 + 32679823407295/8589934592 * x7 + 1950529935805265/34359738368 * 
  x0^2 + -164177076468389/34359738368 * x0 * x1
  + 3485870509960465/68719476736 * x1^2
  + 147516203015383/34359738368 * x0 * x2
  + 164801954390961/17179869184 * x1 * x2
  + 4934619120009613/68719476736 * x2^2
  + -86812977762949/34359738368 * x0 * x3
  + -232394201902067/34359738368 * x1 * x3
  + 81464982719551/17179869184 * x2 * x3
  + 3972534473815879/68719476736 * x3^2 + -472805047459/536870912 * x0 * x4
  + -47365004401111/34359738368 * x1 * x4
  + 54690917412299/34359738368 * x2 * x4
  + -51022804267763/34359738368 * x3 * x4
  + 3901767224017949/68719476736 * x4^2 + -1875808318871/2147483648 * 
  x0 * x5 + -83706432473353/34359738368 * x1 * x5
  + 36098077706359/17179869184 * x2 * x5
  + -42476135590685/34359738368 * x3 * x5
  + -15583700869145/34359738368 * x4 * x5
  + 4091850431643529/68719476736 * x5^2
  + -93100356491411/17179869184 * x0 * x6
  + -347877851064961/34359738368 * x1 * x6
  + 284708859649989/34359738368 * x2 * x6
  + -239527776365875/34359738368 * x3 * x6
  + -25952379304735/17179869184 * x4 * x6
  + -89512928726745/34359738368 * x5 * x6 + 437243488035161/8589934592 * 
  x6^2 + 89746153217533/17179869184 * x0 * x7
  + 352835968995407/34359738368 * x1 * x7
  + -351315114627823/34359738368 * x2 * x7
  + 248247426657057/34359738368 * x3 * x7
  + 26934107622605/17179869184 * x4 * x7
  + 45601135498225/17179869184 * x5 * x7
  + 379706772567949/34359738368 * x6 * x7
  + 845158201100073/17179869184 * x7^2.

Let ub_sigma4 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  1363562887936921/34359738368 + -189456746375981/34359738368 * x0
  + -275068063861937/17179869184 * x1 + 54956189694331/4294967296 * x2
  + 50029318959913/34359738368 * x3 + -68290595096329/17179869184 * x4
  + -99490022373643/34359738368 * x5 + -575764865632487/34359738368 * 
  x6 + 504409637993593/34359738368 * x7 + 3204243373357653/68719476736 * 
  x0^2 + -11522681813783/2147483648 * x0 * x1
  + 2613507589717101/68719476736 * x1^2
  + 131256253770231/34359738368 * x0 * x2
  + 403526039290981/34359738368 * x1 * x2 + 381895168979801/8589934592 * 
  x2^2 + -38842504667579/17179869184 * x0 * x3
  + -3373738012457/4294967296 * x1 * x3
  + -11206746184047/17179869184 * x2 * x3
  + 4688139569109295/68719476736 * x3^2
  + -41517410065487/34359738368 * x0 * x4
  + -37531829607387/8589934592 * x1 * x4
  + 51295905461481/17179869184 * x2 * x4
  + 24434198880685/34359738368 * x3 * x4
  + 3816538105413979/68719476736 * x4^2
  + -156396053318851/34359738368 * x0 * x5
  + -46590346602809/17179869184 * x1 * x5
  + 31069450987263/17179869184 * x2 * x5
  + -1456420433421/1073741824 * x3 * x5
  + -20896542843063/34359738368 * x4 * x5
  + 876098166957335/17179869184 * x5^2
  + -219877684525241/34359738368 * x0 * x6
  + -498180869677917/34359738368 * x1 * x6
  + 28843775468817/2147483648 * x2 * x6
  + -12642924406797/4294967296 * x3 * x6
  + -54575779780795/17179869184 * x4 * x6
  + -28924266490671/8589934592 * x5 * x6 + 287073495031719/8589934592 * 
  x6^2 + 200057460897/33554432 * x0 * x7
  + 295779178874407/17179869184 * x1 * x7
  + -201954796332159/17179869184 * x2 * x7
  + 50938288860585/34359738368 * x3 * x7
  + 141570795837471/34359738368 * x4 * x7
  + 106224387871623/34359738368 * x5 * x7
  + 131010810914447/8589934592 * x6 * x7
  + 1386416942570921/34359738368 * x7^2.

Let ub_sigma5 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  8772888436616443/68719476736 + 311574985102483/17179869184 * x0
  + 4418174359778605/68719476736 * x1 + -2655435766091763/68719476736 * 
  x2 + 498820129512323/34359738368 * x3 + 5236059512877/536870912 * x4
  + 146631940024033/17179869184 * x5 + 17556496926417/268435456 * x6
  + -2699219711455999/34359738368 * x7 + 2183912859698423/34359738368 * 
  x0^2 + 145977962147725/8589934592 * x0 * x1
  + 8114620398727413/68719476736 * x1^2
  + -378062807780683/34359738368 * x0 * x2
  + -288813385164039/8589934592 * x1 * x2
  + 2740582402334613/34359738368 * x2^2
  + 101809206851529/17179869184 * x0 * x3
  + 577526857864371/34359738368 * x1 * x3
  + -182398668741483/17179869184 * x2 * x3
  + 563894777320395/8589934592 * x3^2 + 26949659910181/8589934592 * x0 * x4
  + 69287478408355/17179869184 * x1 * x4
  + -193023518314697/34359738368 * x2 * x4 + 919218284503/268435456 * 
  x3 * x4 + 713703226320051/8589934592 * x4^2
  + 45089113766011/17179869184 * x0 * x5
  + 140275092021381/17179869184 * x1 * x5
  + -183460324401279/34359738368 * x2 * x5
  + 100478273933959/34359738368 * x3 * x5
  + 53556144690929/34359738368 * x4 * x5
  + 4076732660174747/68719476736 * x5^2
  + 634642835719409/34359738368 * x0 * x6
  + 2127333150412191/34359738368 * x1 * x6
  + -2441165120123115/68719476736 * x2 * x6
  + 665321679767119/34359738368 * x3 * x6
  + 337560601880137/34359738368 * x4 * x6
  + 152481389390815/17179869184 * x5 * x6
  + 8994495963114813/68719476736 * x6^2
  + -668946908857863/34359738368 * x0 * x7
  + -4651559981874199/68719476736 * x1 * x7
  + 2704503920049361/68719476736 * x2 * x7
  + -26733699955701/2147483648 * x3 * x7
  + -169229663562351/17179869184 * x4 * x7
  + -159741830497543/17179869184 * x5 * x7
  + -2579252423977243/34359738368 * x6 * x7
  + 1233379637585013/8589934592 * x7^2.

Let ub_sigma6 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  3555858634108463/68719476736 + -154217880683593/34359738368 * x0
  + -312449384834849/34359738368 * x1 + 240074874087763/34359738368 * 
  x2 + -378850684257519/34359738368 * x3 + -586785765159/536870912 * 
  x4 + -95225851451223/34359738368 * x5 + -683128942188017/34359738368 * 
  x6 + 368199375315499/34359738368 * x7 + 4025819314674717/68719476736 * 
  x0^2 + -50770070750271/8589934592 * x0 * x1
  + 1607391816462107/34359738368 * x1^2
  + 135880376305105/34359738368 * x0 * x2
  + 176480984547623/17179869184 * x1 * x2 + 28743232126793/536870912 * 
  x2^2 + -109976650212223/34359738368 * x0 * x3
  + -310651355163661/34359738368 * x1 * x3
  + 52363133646283/8589934592 * x2 * x3 + 3992300553657957/68719476736 * 
  x3^2 + -595094136099/536870912 * x0 * x4
  + -91921719098645/34359738368 * x1 * x4
  + 67121390457687/34359738368 * x2 * x4
  + -67885948347023/34359738368 * x3 * x4
  + 1972094153509405/34359738368 * x4^2
  + -96191407214775/17179869184 * x0 * x5
  + -64400740493665/17179869184 * x1 * x5
  + 92908745747237/34359738368 * x2 * x5
  + -29319207710805/17179869184 * x3 * x5
  + -23242221080669/34359738368 * x4 * x5
  + 3001098202060505/34359738368 * x5^2
  + -210474226893589/34359738368 * x0 * x6
  + -694334481780181/34359738368 * x1 * x6
  + 702814084360611/34359738368 * x2 * x6
  + -135114395330971/17179869184 * x3 * x6
  + -142725778540619/34359738368 * x4 * x6
  + -14551444786025/4294967296 * x5 * x6
  + 3170342042514915/68719476736 * x6^2
  + 218765745268247/34359738368 * x0 * x7
  + 559481194450909/34359738368 * x1 * x7
  + -97553001517045/8589934592 * x2 * x7
  + 325393446096941/34359738368 * x3 * x7
  + 99953939392285/34359738368 * x4 * x7
  + 68014834319981/17179869184 * x5 * x7
  + 750922051894635/34359738368 * x6 * x7 + 382020947378031/8589934592 * 
  x7^2.

Let ub_sigma7 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  167486942993919/4294967296 + -20407661358429/8589934592 * x0
  + -641311143914031/34359738368 * x1 + 285935704952497/34359738368 * 
  x2 + -94851811441677/34359738368 * x3 + -76142624763245/17179869184 * 
  x4 + 4531192555759/34359738368 * x5 + -210487614935233/34359738368 * 
  x6 + 684662447411211/34359738368 * x7 + 1657458943481709/34359738368 * 
  x0^2 + -101476973196615/34359738368 * x0 * x1
  + 1197807770870521/34359738368 * x1^2
  + 31192543310627/34359738368 * x0 * x2
  + 355525440968755/34359738368 * x1 * x2
  + 3210315644341841/68719476736 * x2^2
  + -34794132449755/34359738368 * x0 * x3
  + -46671342869575/17179869184 * x1 * x3
  + 62935806472727/34359738368 * x2 * x3
  + 2775436992994927/68719476736 * x3^2
  + -22792738293335/34359738368 * x0 * x4
  + -172474256830283/34359738368 * x1 * x4
  + 86054471670207/34359738368 * x2 * x4
  + -8454803880291/34359738368 * x3 * x4 + 442622033379565/8589934592 * 
  x4^2 + 63452864969591/8589934592 * x0 * x5
  + -32622554337315/34359738368 * x1 * x5
  + -14441690910325/34359738368 * x2 * x5
  + -25143380920701/34359738368 * x3 * x5
  + -4679169777391/34359738368 * x4 * x5
  + 1698025237842217/34359738368 * x5^2
  + -9633596777617/34359738368 * x0 * x6
  + -448990417542179/34359738368 * x1 * x6
  + -62625770580191/34359738368 * x2 * x6
  + -10490941628927/2147483648 * x3 * x6
  + -76508885262765/34359738368 * x4 * x6
  + -146389791243/2147483648 * x5 * x6 + 4473490526241407/68719476736 * 
  x6^2 + 51849541036763/17179869184 * x0 * x7
  + 621048893967147/34359738368 * x1 * x7
  + -185493736263333/17179869184 * x2 * x7
  + 69560998623103/8589934592 * x3 * x7 + 44738265461347/8589934592 * 
  x4 * x7 + 33620792615847/34359738368 * x5 * x7
  + 226323746011033/17179869184 * x6 * x7
  + 1135210868454305/34359738368 * x7^2.

Let ub_sigma8 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  3275795803196633/68719476736 + -166257453529157/34359738368 * x0
  + -186841968533861/34359738368 * x1 + 251658714617039/34359738368 * 
  x2 + 323161076321007/34359738368 * x3 + -936058885937/4294967296 * 
  x4 + -23112199222205/8589934592 * x5 + -257357193729807/17179869184 * 
  x6 + 315571668522095/34359738368 * x7 + 3490786322634505/68719476736 * 
  x0^2 + -146611277773739/34359738368 * x0 * x1
  + 3383567513832519/68719476736 * x1^2
  + 57971739395091/17179869184 * x0 * x2
  + 229280427267767/34359738368 * x1 * x2
  + 3370776997632615/68719476736 * x2^2
  + -20634347700493/34359738368 * x0 * x3
  + 55157368996395/8589934592 * x1 * x3
  + -143446801081063/34359738368 * x2 * x3
  + 3605377851171477/68719476736 * x3^2
  + -17846268756805/17179869184 * x0 * x4
  + 67504457326669/34359738368 * x1 * x4 + 7174425106217/4294967296 * 
  x2 * x4 + 40195033696141/17179869184 * x3 * x4
  + 1889558258065927/34359738368 * x4^2
  + -109304506198931/34359738368 * x0 * x5
  + -39571740743659/17179869184 * x1 * x5
  + 57531109941671/34359738368 * x2 * x5
  + -9610691488175/17179869184 * x3 * x5
  + -1205136976383/2147483648 * x4 * x5 + 3711106640327949/68719476736 * 
  x5^2 + -49385031592619/8589934592 * x0 * x6
  + -106066309617147/8589934592 * x1 * x6
  + 100164846303709/8589934592 * x2 * x6
  + 19537174670131/17179869184 * x3 * x6
  + -107383090457357/34359738368 * x4 * x6
  + -104919301098417/34359738368 * x5 * x6
  + 2732688751902751/68719476736 * x6^2
  + 107156700482741/17179869184 * x0 * x7 + 3122020781659/268435456 * 
  x1 * x7 + -99126528404557/8589934592 * x2 * x7
  + -416634153848361/34359738368 * x3 * x7
  + 36568132024921/8589934592 * x4 * x7
  + 54336941499545/17179869184 * x5 * x7
  + 598004036290343/34359738368 * x6 * x7
  + 4519807539622121/68719476736 * x7^2.

Lemma lb_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) :
  lb_sigma x0 x1 x2 x3 x4 x5 x6 x7 * (p x0 x1 x2 x3 x4 x5 x6 x7 - lb)
  - lb_sigma1 x0 x1 x2 x3 x4 x5 x6 x7 * b1 x0 x1 x2 x3 x4 x5 x6 x7
  - lb_sigma2 x0 x1 x2 x3 x4 x5 x6 x7 * b2 x0 x1 x2 x3 x4 x5 x6 x7
  - lb_sigma3 x0 x1 x2 x3 x4 x5 x6 x7 * b3 x0 x1 x2 x3 x4 x5 x6 x7
  - lb_sigma4 x0 x1 x2 x3 x4 x5 x6 x7 * b4 x0 x1 x2 x3 x4 x5 x6 x7
  - lb_sigma5 x0 x1 x2 x3 x4 x5 x6 x7 * b5 x0 x1 x2 x3 x4 x5 x6 x7
  - lb_sigma6 x0 x1 x2 x3 x4 x5 x6 x7 * b6 x0 x1 x2 x3 x4 x5 x6 x7
  - lb_sigma7 x0 x1 x2 x3 x4 x5 x6 x7 * b7 x0 x1 x2 x3 x4 x5 x6 x7
  - lb_sigma8 x0 x1 x2 x3 x4 x5 x6 x7 * b8 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof.
rewrite /p /lb /lb_sigma /lb_sigma1 /b1 /lb_sigma2 /b2 /lb_sigma3 /b3
        /lb_sigma4 /b4 /lb_sigma5 /b5 /lb_sigma6 /b6 /lb_sigma7 /b7 /lb_sigma8 /b8.
do_sdp.
Qed.

Lemma lb_sigma_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma x0 x1 x2 x3 x4 x5 x6 x7 > 0.
Proof. rewrite /lb_sigma. interval. Qed.

Lemma lb_sigma1_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma1 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /lb_sigma1. do_sdp. Qed.

Lemma lb_sigma2_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma2 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /lb_sigma2. do_sdp. Qed.

Lemma lb_sigma3_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma3 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /lb_sigma3. do_sdp. Qed.

Lemma lb_sigma4_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma4 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /lb_sigma4. do_sdp. Qed.

Lemma lb_sigma5_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma5 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /lb_sigma5. do_sdp. Qed.

Lemma lb_sigma6_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma6 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /lb_sigma6. do_sdp. Qed.

Lemma lb_sigma7_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma7 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /lb_sigma7. do_sdp. Qed.

Lemma lb_sigma8_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : lb_sigma8 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /lb_sigma8. do_sdp. Qed.

Lemma ub_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) :
  ub_sigma x0 x1 x2 x3 x4 x5 x6 x7 * (ub - p x0 x1 x2 x3 x4 x5 x6 x7)
  - ub_sigma1 x0 x1 x2 x3 x4 x5 x6 x7 * b1 x0 x1 x2 x3 x4 x5 x6 x7
  - ub_sigma2 x0 x1 x2 x3 x4 x5 x6 x7 * b2 x0 x1 x2 x3 x4 x5 x6 x7
  - ub_sigma3 x0 x1 x2 x3 x4 x5 x6 x7 * b3 x0 x1 x2 x3 x4 x5 x6 x7
  - ub_sigma4 x0 x1 x2 x3 x4 x5 x6 x7 * b4 x0 x1 x2 x3 x4 x5 x6 x7
  - ub_sigma5 x0 x1 x2 x3 x4 x5 x6 x7 * b5 x0 x1 x2 x3 x4 x5 x6 x7
  - ub_sigma6 x0 x1 x2 x3 x4 x5 x6 x7 * b6 x0 x1 x2 x3 x4 x5 x6 x7
  - ub_sigma7 x0 x1 x2 x3 x4 x5 x6 x7 * b7 x0 x1 x2 x3 x4 x5 x6 x7
  - ub_sigma8 x0 x1 x2 x3 x4 x5 x6 x7 * b8 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof.
rewrite /p /ub /ub_sigma /ub_sigma1 /b1 /ub_sigma2 /b2 /ub_sigma3 /b3
        /ub_sigma4 /b4 /ub_sigma5 /b5 /ub_sigma6 /b6 /ub_sigma7 /b7 /ub_sigma8 /b8.
do_sdp.
Qed.

Lemma ub_sigma_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma x0 x1 x2 x3 x4 x5 x6 x7 > 0.
Proof. rewrite /ub_sigma. interval. Qed.

Lemma ub_sigma1_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma1 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /ub_sigma1. do_sdp. Qed.

Lemma ub_sigma2_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma2 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /ub_sigma2. do_sdp. Qed.

Lemma ub_sigma3_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma3 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /ub_sigma3. do_sdp. Qed.

Lemma ub_sigma4_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma4 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /ub_sigma4. do_sdp. Qed.

Lemma ub_sigma5_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma5 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /ub_sigma5. do_sdp. Qed.

Lemma ub_sigma6_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma6 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /ub_sigma6. do_sdp. Qed.

Lemma ub_sigma7_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma7 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /ub_sigma7. do_sdp. Qed.

Lemma ub_sigma8_pos (x0 x1 x2 x3 x4 x5 x6 x7 : R) : ub_sigma8 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
Proof. rewrite /ub_sigma8. do_sdp. Qed.

Lemma var_bounds (x l u : R) : l <= x <= u -> (x - l) * (u - x) >= 0.
Proof.
move=> [Hl Hu].
apply Rle_ge.
by apply Interval_missing.Rmult_le_pos_pos; apply Fcore_Raux.Rle_0_minus.
Qed.

Lemma relax (x y z : R) : x >= 0 -> y >= 0 -> z - x * y >= 0 -> z >= 0.
Proof.
move=> HX Hy.
apply Rge_trans, Rle_ge.
rewrite -{2}(Rminus_0_r z).
apply Rplus_le_compat_l, Ropp_le_contravar.
by apply Interval_missing.Rmult_le_pos_pos; apply Rge_le.
Qed.
  
Theorem p_ge_lb (x0 x1 x2 x3 x4 x5 x6 x7 : R) :
  -1/10 <= x0 <= 4/10 -> 4/10 <= x1 <= 1 -> -7/10 <= x2 <= -4/10 -> -7/10 <= x3 <= 4/10 -> 1/10 <= x4 <= 2/10 -> -1/10 <= x5 <= 2/10 -> -3/10 <= x6 <= 11/10 -> -11/10 <= x7 <= -3/10 ->
  lb <= p x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
move=> H0 H1 H2 H3 H4 H5 H6 H7.
have Hb0 : b1 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b1 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb1 : b2 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ by rewrite /b2; apply var_bounds; rewrite Rcomplements.Rdiv_1. }
have Hb2 : b3 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b3 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb3 : b4 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b4 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb4 : b5 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ by rewrite /b5; apply var_bounds. }
have Hb5 : b6 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b6 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb6 : b7 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b7 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb7 : b8 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b8 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (lb_sigma x0 x1 x2 x3 x4 x5 x6 x7)); [by apply lb_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (lb_sigma1_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb0).
apply (relax _ _ _ (lb_sigma2_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb1).
apply (relax _ _ _ (lb_sigma3_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb2).
apply (relax _ _ _ (lb_sigma4_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb3).
apply (relax _ _ _ (lb_sigma5_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb4).
apply (relax _ _ _ (lb_sigma6_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb5).
apply (relax _ _ _ (lb_sigma7_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb6).
apply (relax _ _ _ (lb_sigma8_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb7).
apply lb_pos.
Qed.

Theorem p_le_ub (x0 x1 x2 x3 x4 x5 x6 x7 : R) :
  -1/10 <= x0 <= 4/10 -> 4/10 <= x1 <= 1 -> -7/10 <= x2 <= -4/10 -> -7/10 <= x3 <= 4/10 -> 1/10 <= x4 <= 2/10 -> -1/10 <= x5 <= 2/10 -> -3/10 <= x6 <= 11/10 -> -11/10 <= x7 <= -3/10 ->
  p x0 x1 x2 x3 x4 x5 x6 x7 <= ub.
Proof.
move=> H0 H1 H2 H3 H4 H5 H6 H7.
have Hb0 : b1 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b1 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb1 : b2 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ by rewrite /b2; apply var_bounds; rewrite Rcomplements.Rdiv_1. }
have Hb2 : b3 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b3 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb3 : b4 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b4 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb4 : b5 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ by rewrite /b5; apply var_bounds. }
have Hb5 : b6 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b6 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb6 : b7 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b7 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb7 : b8 x0 x1 x2 x3 x4 x5 x6 x7 >= 0.
{ rewrite /b8 -(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (ub_sigma x0 x1 x2 x3 x4 x5 x6 x7)); [by apply ub_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (ub_sigma1_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb0).
apply (relax _ _ _ (ub_sigma2_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb1).
apply (relax _ _ _ (ub_sigma3_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb2).
apply (relax _ _ _ (ub_sigma4_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb3).
apply (relax _ _ _ (ub_sigma5_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb4).
apply (relax _ _ _ (ub_sigma6_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb5).
apply (relax _ _ _ (ub_sigma7_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb6).
apply (relax _ _ _ (ub_sigma8_pos x0 x1 x2 x3 x4 x5 x6 x7) Hb7).
apply ub_pos.
Qed.