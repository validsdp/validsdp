load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4','x5','x6'])

rhs = polynomial_ring('-1/100000000 + (- 4/1)   * (x4 * x4 * x1      + 8/1 * (x5 - x6) * (x2 - x3)        - x4 * (16/1 * x1 + (x5 - 8/1) * x2 + (x6 - 8/1) * x3))')

lhs = [polynomial_ring('(x1 - 1) * (117547965573 / 100000000000 - x1)'), polynomial_ring('(x2 - 1) * (117547965573 / 100000000000 - x2)'), polynomial_ring('(x3 - 1) * (117547965573 / 100000000000 - x3)'), polynomial_ring('(x4 - 251952632905 / 100000000000) * (63504 / 10000 - x4)'), polynomial_ring('(x5 - 251952632905 / 100000000000) * (90601 / 10000 - x5)'), polynomial_ring('(x6 - 56644 / 10000) * (16 / 1 - x6)')]

check = test_MC11(polynomial_ring, lhs, rhs)

if check:
  print 'proved: true'
else:
  print 'proved: false'
