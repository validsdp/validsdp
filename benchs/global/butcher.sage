load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4','x5','x6'])

rhs = polynomial_ring('14394/10000 + x6*x2^2+x5*x3^2-x1*x4^2+x4^3+x4^2-1/3*x1+4/3*x4')
lhs = [polynomial_ring('(x1 + 1) * (0 - x1)'), polynomial_ring('(x2 + 1) * (9/10 - x2)'), polynomial_ring('(x3 + 1) * (5/10 - x3)'), polynomial_ring('(x4 + 1) * (-1/10 - x4)'), polynomial_ring('(x5 + 1/10) * (-5/100 - x5)'), polynomial_ring('(x6 + 1/10) * (-3/100 - x6)')]

check_lb = test_MC11(polynomial_ring, lhs, rhs)

if check_lb:
  print 'proved: true'
else:
  print 'proved: false'
