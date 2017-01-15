load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4'])

rhs = polynomial_ring('3181/1000 -x1*x3^3+4/1*x2*x3^2*x4+4/1*x1*x3*x4^2+2/1*x2*x4^3+4/1*x1*x3+4/1*x3^2-10/1*x2*x4-10/1*x4^2+2/1')
lhs = [polynomial_ring('(x1 + 1/2) * (1/2 - x1)'), polynomial_ring('(x2 + 1/2) * (1/2 - x2)'), polynomial_ring('(x3 + 1/2) * (1/2 - x3)'), polynomial_ring('(x4 + 1/2) * (1/2 - x4)')]

check_lb = test_MC11(polynomial_ring, lhs, rhs)

if check_lb:
  print 'proved: true'
else:
  print 'proved: false'
