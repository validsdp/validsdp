load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4','x5','x6','x7','x8'])

rhs = polynomial_ring('1744/1000 -x1*x6**3+3/1*x1*x6*x7**2-x3*x7**3+3/1*x3*x7*x6**2-x2*x5**3+3/1*x2*x5*x8**2-x4*x8**3+3/1*x4*x8*x5**2-9563453/10000000')
lhs = [polynomial_ring('(x1 + 1/10) * (4/10 - x1)'), polynomial_ring('(x2 - 4/10) * (1/1 - x2)'), polynomial_ring('(x3 + 7/10) * (-4/10 - x3)'), polynomial_ring('(x4 + 7/10) * (4/10 - x4)'), polynomial_ring('(x5 - 1/10) * (2/10 - x5)'), polynomial_ring('(x6 + 1/10) * (2/10 - x6)'), polynomial_ring('(x7 + 3/10) * (11/10 - x7)'), polynomial_ring('(x8 + 11/10) * (-3/10 - x8)')]

check_lb = test_MC11(polynomial_ring, lhs, rhs)

if check_lb:
  print 'proved: true'
else:
  print 'proved: false'
