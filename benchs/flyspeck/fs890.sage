load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4','x5','x6'])

rhs = polynomial_ring('-1/100000000 -(  x1 * x4 * ((- x1) + x2 + x3 - x4 + x5 + x6)   + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)     + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) - x2 * x3 * x4 - x1 * x3 * x5       - x1 * x2 * x6 - x4 * x5 * x6)')

lhs = [polynomial_ring('x1      * (x1 * x4 * ((- x1) + x2 + x3 - x4 + x5 + x6)         + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)           + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) - x2 * x3 * x4             - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6)      * (4/1)      + ((- x2) * x3 - x1 * x4         + x2 * x5           + x3 * x6 - x5 * x6 + x1 * ((- x1) + x2 + x3 - x4 + x5 + x6))        * ((- x2) * x3 - x1 * x4           + x2 * x5             + x3 * x6 - x5 * x6 + x1 * ((- x1) + x2 + x3 - x4 + x5 + x6))        * (- 243621/100000)'), polynomial_ring('(x1 - 4) * (63504 / 10000 - x1)'), polynomial_ring('(x2 - 4) * (63504 / 10000 - x2)'), polynomial_ring('(x3 - 4) * (63504 / 10000 - x3)'), polynomial_ring('(x4 - 4) * (4 - x4)'), polynomial_ring('(x5 - 4) * (4 - x5)'), polynomial_ring('(x6 - 90601 / 10000) * (104721490449 / 10000000000 - x6)')]

check = test_MC11(polynomial_ring, lhs, rhs)

if check:
  print 'proved: true'
else:
  print 'proved: false'
