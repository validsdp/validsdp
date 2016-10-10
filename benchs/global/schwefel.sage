load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3'])

rhs = polynomial_ring('1/10000 + (x1-x2)^2+(x2-1/1)^2+(x1-x3^2)^2+(x3-1/1)^2')
lhs = [polynomial_ring('(x1 + 10/1) * (10/1 - x1)'), polynomial_ring('(x2 + 10/1) * (10/1 - x2)'), polynomial_ring('(x3 + 10/1) * (10/1 - x3)')]

check_lb = test_MC11(polynomial_ring, lhs, rhs)

if check_lb:
  print 'proved: true'
else:
  print 'proved: false'
