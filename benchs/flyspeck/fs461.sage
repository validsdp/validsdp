load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4','x5','x6'])

rhs = polynomial_ring('-1/100000000 + x1 * x4 * ((- x1) + x2 + x3 - x4 + x5 + x6) + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) - x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6')
lhs = [polynomial_ring('(x1 - 606887582536 / 100000000000) * (702674064 / 100000000 - x1)'), polynomial_ring('(x2 - 4) * (8 - x2)'), polynomial_ring('(x3 - 4) * (8 - x3)'), polynomial_ring('(x4 - 4) * (8 - x4)'), polynomial_ring('(x5 - 4) * (8 - x5)'), polynomial_ring('(x6 - 4) * (8 - x6)')]

check = test_MC11(polynomial_ring, lhs, rhs)

if check:
  print 'proved: true'
else:
  print 'proved: false'
