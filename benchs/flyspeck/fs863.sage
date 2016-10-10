load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4','x5','x6'])

rhs = polynomial_ring('-1/100000000 - ((- x2) * x3 - x1 * x4  + x2 * x5 + x3 * x6 - x5 * x6 + x1 * ((- x1) + x2 + x3 - x4 + x5 + x6))')

lhs = [polynomial_ring('(x1 - 4) * (63504 / 10000 - x1)'), polynomial_ring('(x2 - 4) * (63504 / 10000 - x2)'), polynomial_ring('(x3 - 4) * (4 - x3)'), polynomial_ring('(x4 - 90601 / 10000) * (90601 / 10000 - x4)'), polynomial_ring('(x5 - 4) * (63504 / 10000 - x5)'), polynomial_ring('(x6 - 4) * (4 - x6)')]

check = test_MC11(polynomial_ring, lhs, rhs)

if check:
  print 'proved: true'
else:
  print 'proved: false'
