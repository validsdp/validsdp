load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3'])

rhs = polynomial_ring('36713/1000 -x1 + 2 / 1 * x2 - x3 - 835634534 / 1000000000 * x2 * (1 / 1 + x2)')
lhs = [polynomial_ring('(x1 + 5) * (5 - x1)'), polynomial_ring('(x2 + 5) * (5 - x2)'), polynomial_ring('(x3 + 5) * (5 - x3)')]

check_lb = test_MC11(polynomial_ring, lhs, rhs)

if check_lb:
  print 'proved: true'
else:
  print 'proved: false'
