load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4'])

rhs = polynomial_ring('20802/1000 + x1*x2^2+x1*x3^2+x1*x4^2-11/10*x1+1/1')
lhs = [polynomial_ring('(x1 + 2) * (2 - x1)'), polynomial_ring('(x2 + 2) * (2 - x2)'), polynomial_ring('(x3 + 2) * (2 - x3)'), polynomial_ring('(x4 + 2) * (2 - x4)')]

check_lb = test_MC11(polynomial_ring, lhs, rhs)

rhs = polynomial_ring('22802/1000 - (x1*x2^2+x1*x3^2+x1*x4^2-11/10*x1+1/1)')

check_ub = test_MC11(polynomial_ring, lhs, rhs)

if check_lb and check_ub:
  print 'proved: true'
else:
  print 'proved: false'
