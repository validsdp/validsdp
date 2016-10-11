# This small script calls the implementation from:
#   David Monniaux and Pierre Corbineau
#   On the Generation of Positivstellensatz Witnesses in Degenerate Cases
#   ITP 2011
# 
# The implementation can be downloaded from the URL given in the above
# paper <http://bit.ly/fBNLhR>. Unzip it and place all *.sage files in
# the same directory as this file.
#
# The implementation can use SDP solvers DSDP, SDPA or CSDP. We tried
# thrice and got the best results with CSDP. To use CSDP, the csdp
# executable must be in the path and the line 170 of
# solve_sos_equation.sage must be replaced by
# solution = csdp_solve("sdp_problem", mf0b, fisb, [0 for b in fisb])
#
# To make it work with SageMath 6.9 (no further need for fpLLL, as
# indicated in the paper, since fpLLL is now included in Sage) I had
# to change the two following lines:
# * line 26 of linear_algebra.sage, replace "1, 2" by "nrows=1, ncols=2"
# * line 27 of quadratic_form.sage, replace "transpose(v)" by
#   "Matrix([v]).transpose()"

load 'solve_sos_equation.sage'
load 'prepare_polynomials.sage'

# polynomial_ring is obtained by PolynomialRing(QQ, ['x0',...,'x<n>'])
#
# rhs_polynomial is a polynomial of degree d over polynomial_ring
# (obtained by polynomial_ring('x0 + 3 * x1^3') for instance)
#
# lhs_polynomial is a list of m polynomials of degree at most d
#
# The function looks for SOS polynomials s_0,..., s_m such that
# s_m + \sum_{i=0}^{m-1} s_i * lhs_polynomials[i] = rhs_polynomial
#
# If such s_i are found, prints "SOLUTION" (and details of the s_i
# ("sos polynomial" under expanded form and "summands" under SOS form)
# if corresponding lines are uncommented). Otherwise, prints
# "NO SOLUTION".
#
def test_MC11(polynomial_ring, lhs_polynomials, rhs_polynomial):
  rhs_deg = rhs_polynomial.degree()
  lhs_polynomials_degs = [(p, (rhs_deg - p.degree() + 1) / 2) for p in lhs_polynomials]
  sum_polynomials = rhs_polynomial - sum([p * sum(monomial_basis(2 * d)) for (p, d) in lhs_polynomials_degs])
  sum_polytope = (sum_polynomials.newton_polytope())*(1/2)
  sum_monomials = [m for m in monomial_basis(rhs_deg) if sum_polytope.contains(m.exponents()[0])]

  lhs_polynomials = lhs_polynomials + [polynomial_ring(1)]
  lhs_monomial_lists = [monomial_basis(d) for (p, d) in lhs_polynomials_degs] + [sum_monomials]

  solution = solve_sos_equation_sos(polynomial_ring, lhs_polynomials, lhs_monomial_lists, [], [], rhs_polynomial)

  def apply_sos_solution(pblocks):
    assert(len(pblocks) == len(lhs_monomial_lists))
    assert(len(pblocks) == len(lhs_polynomials))

    total = polynomial_ring(0)
    for (sos, poly, monomials) in zip(pblocks, lhs_polynomials, lhs_monomial_lists):
      total += poly * apply_sos(sos, monomials)
    return total

  if solution == ():
    print 'NO SOLUTION'
    return False
  else:
    # (pblocks, eblocks) = solution
    # assert(apply_sos_solution(pblocks)==rhs_polynomial)
    # print 'SOLUTION'
    # print 'RHS'
    # print rhs_polynomial
    # for i in xrange(len(lhs_polynomials)):
    #   print 'LHS POLYNOMIAL', i
    #   print lhs_polynomials[i]
    #   print 'sos polynomial'
    #   print apply_sos(pblocks[i], lhs_monomial_lists[i])
    #   print 'summands'
    #   for coeff, sos in pblocks[i]:
    #     print coeff, "*(", sum([a*b for a, b in zip(sos, lhs_monomial_lists[i])]), ")^2"
    print 'SOLUTION'
    return True
