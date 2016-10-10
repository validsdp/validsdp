load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4','x5','x6','x7'])

rhs = polynomial_ring('2501/10000 + x1^2+2/1*x2^2+2/1*x3^2+2/1*x4^2+2/1*x5^2+2/1*x6^2+2/1*x7^2-x1')
lhs = [polynomial_ring('(x1 + 1/1) * (1/1 - x1)'), polynomial_ring('(x2 + 1/1) * (1/1 - x2)'), polynomial_ring('(x3 + 1/1) * (1/1 - x3)'), polynomial_ring('(x4 + 1/1) * (1/1 - x4)'), polynomial_ring('(x5 + 1/1) * (1/1 - x5)'), polynomial_ring('(x6 + 1/1) * (1/1 - x6)'), polynomial_ring('(x7 + 1/1) * (1/1 - x7)')]

check_lb = test_MC11(polynomial_ring, lhs, rhs)

rhs = polynomial_ring('140001/10000 - (x1^2+2/1*x2^2+2/1*x3^2+2/1*x4^2+2/1*x5^2+2/1*x6^2+2/1*x7^2-x1)')

check_ub = test_MC11(polynomial_ring, lhs, rhs)

if check_lb and check_ub:
  print 'proved: true'
else:
  print 'proved: false'
