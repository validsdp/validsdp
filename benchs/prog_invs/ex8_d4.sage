load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x0','x1'])

rhs = polynomial_ring('360137561854871/1125899906842624 + -4648532753362095/1152921504606846976 * x0^2 + -522343598561959/576460752303423488 * x0 * x1 + -7354102629772791/2305843009213693952 * x1^2 + 5916113786527169/576460752303423488 * x0^3 + -574397345683745/36028797018963968 * x0^2 * x1 + -1432498279428087/576460752303423488 * x0 * x1^2 + 4968500152983215/288230376151711744 * x1^3 + -8454232510940359/72057594037927936 * x0^4 + 8778941830946171/288230376151711744 * x0^3 * x1 + -3420954828653527/36028797018963968 * x0^2 * x1^2 + -8812954633677685/144115188075855872 * x0 * x1^3 + -4295668762430125/72057594037927936 * x1^4')
lhs = [polynomial_ring('(1 + -x0) * (1 + x0)'), polynomial_ring('(1 + -x1) * (1 + x1)')]

check_init = test_MC11(polynomial_ring, lhs, rhs)

rhs = polynomial_ring('360137561854871/1125899906842624 + -459583005578436358899/230584300921369395200000 * x0^2 + -1144309636064083560477/576460752303423488000000 * x0 * x1 + -8190279309669672821823/2305843009213693952000000 * x1^2 + 2853512453178208139018111/576460752303423488000000000 * x0^3 + 2859978588227701049626699/288230376151711744000000000 * x0^2 * x1 + -6242902009634782267883233/576460752303423488000000000 * x0 * x1^2 + 732017933552986412822291/144115188075855872000000000 * x1^3 + -580551721655989523027132233/18014398509481984000000000000 * x0^4 + -21083919770514196620764679589/288230376151711744000000000000 * x0^3 * x1 + -12966227195352294033823139967/144115188075855872000000000000 * x0^2 * x1^2 + -3025487866049480775996441787/72057594037927936000000000000 * x0 * x1^3 + -2233610777023506321280504397/36028797018963968000000000000 * x1^4 + 12564134845787273030833693/720575940379279360000000000000 * x0^4 * x1 + 92274172599398814371298181/2882303761517117440000000000000 * x0^3 * x1^2 + 9130672651470597042156497/360287970189639680000000000000 * x0^2 * x1^3 + 21776916212930209963177703/1441151880758558720000000000000 * x0 * x1^4 + -5169000140809606939789/1441151880758558720000000000000 * x0^4 * x1^2 + -26702741164478516495683/5764607523034234880000000000000 * x0^3 * x1^3 + -34084618546115257032073/14411518807585587200000000000000 * x0^2 * x1^4 + 4774618738744635403/14411518807585587200000000000000 * x0^4 * x1^3 + 68693265822354134969/288230376151711744000000000000000 * x0^3 * x1^4 + -8454232510940359/720575940379279360000000000000000 * x0^4 * x1^4')
lhs = [polynomial_ring('360137561854871/1125899906842624 + -4648532753362095/1152921504606846976 * x0^2 + -522343598561959/576460752303423488 * x0 * x1 + -7354102629772791/2305843009213693952 * x1^2 + 5916113786527169/576460752303423488 * x0^3 + -574397345683745/36028797018963968 * x0^2 * x1 + -1432498279428087/576460752303423488 * x0 * x1^2 + 4968500152983215/288230376151711744 * x1^3 + -8454232510940359/72057594037927936 * x0^4 + 8778941830946171/288230376151711744 * x0^3 * x1 + -3420954828653527/36028797018963968 * x0^2 * x1^2 + -8812954633677685/144115188075855872 * x0 * x1^3 + -4295668762430125/72057594037927936 * x1^4'),polynomial_ring('x0 + -x1')]

check_then = test_MC11(polynomial_ring, lhs, rhs)

rhs = polynomial_ring('360137561854871/1125899906842624 + -1214818634564524365381/230584300921369395200000 * x0^2 + -1118734648512051841/28823037615171174400000 * x0 * x1 + -3588221758965771489/2882303761517117440000 * x1^2 + -19320759693933782782384679/576460752303423488000000000 * x0^3 + 2604902039151466196933241/144115188075855872000000000 * x0^2 * x1 + 275219833370677396757187/36028797018963968000000000 * x0 * x1^2 + 9138250123663583544353/9007199254740992000000000 * x1^3 + -4821887152997222908830630167/36028797018963968000000000000 * x0^4 + 633867576303433867029855343/18014398509481984000000000000 * x0^3 * x1 + -13918506967323627035159766007/144115188075855872000000000000 * x0^2 * x1^2 + -46904638145446224495958391/2251799813685248000000000000 * x0 * x1^3 + -5237320021120043264759573/562949953421312000000000000 * x1^4 + 1955786051890680894347939/720575940379279360000000000000 * x0^5 + -5216040873488090950992063/576460752303423488000000000000 * x0^4 * x1 + 46039771534373063455628123/1441151880758558720000000000000 * x0^3 * x1^2 + -1498429982214579571022337/360287970189639680000000000000 * x0^2 * x1^3 + 16577899133690495233513/45035996273704960000000000000 * x0 * x1^4 + -5256941796975752100951/1801439850948198400000000000000 * x0^6 + -118347561920223024668423/28823037615171174400000000000000 * x0^5 * x1 + -52897955731115225568671/14411518807585587200000000000000 * x0^4 * x1^2 + 13441750728887151029149/7205759403792793600000000000000 * x0^3 * x1^3 + -196968684727788097931/450359962737049600000000000000 * x0^2 * x1^4 + 30531522434946758353/144115188075855872000000000000000 * x0^7 + -8323136611686284649/288230376151711744000000000000000 * x0^6 * x1 + -6800044361428606671/36028797018963968000000000000000 * x0^5 * x1^2 + -22659766947589626723/144115188075855872000000000000000 * x0^4 * x1^3 + 440616693852472421/7205759403792793600000000000000 * x0^3 * x1^4 + -8454232510940359/720575940379279360000000000000000 * x0^8 + 8778941830946171/2882303761517117440000000000000000 * x0^7 * x1 + -3420954828653527/360287970189639680000000000000000 * x0^6 * x1^2 + -1762590926735537/288230376151711744000000000000000 * x0^5 * x1^3 + -34365350099441/5764607523034234880000000000000 * x0^4 * x1^4')
lhs = [polynomial_ring('360137561854871/1125899906842624 + -4648532753362095/1152921504606846976 * x0^2 + -522343598561959/576460752303423488 * x0 * x1 + -7354102629772791/2305843009213693952 * x1^2 + 5916113786527169/576460752303423488 * x0^3 + -574397345683745/36028797018963968 * x0^2 * x1 + -1432498279428087/576460752303423488 * x0 * x1^2 + 4968500152983215/288230376151711744 * x1^3 + -8454232510940359/72057594037927936 * x0^4 + 8778941830946171/288230376151711744 * x0^3 * x1 + -3420954828653527/36028797018963968 * x0^2 * x1^2 + -8812954633677685/144115188075855872 * x0 * x1^3 + -4295668762430125/72057594037927936 * x1^4'),polynomial_ring('-x0 + x1')]

check_else = test_MC11(polynomial_ring, lhs, rhs)

if check_init and check_then and check_else:
  print 'proved: true'
else:
  print 'proved: false'
