import sys

load 'linear_algebra.sage'
load 'sdp_solver.sage'
load 'quadratic_forms.sage'

sparseflag=True
#sparseflag=False
test=False
reuse_solutions=False
numeric_sdp_test=False

def reduce_vector(v):
  l = lcm(map(denominator,v))
  v= vector(ZZ, vector(v)*l, sparse=sparseflag)
  v /= gcd(v)
  return v

def solve_sos_equation(polynomial_ring, positive_polynomials, positive_monomial_lists, equality_polynomials, equality_monomial_lists, rhs_polynomial):
  assert len(positive_polynomials) == len(positive_monomial_lists)
  assert len(equality_polynomials) == len(equality_monomial_lists)

  qcoeff_positions=[(block, i, j)\
               for block in xrange(len(positive_monomial_lists))\
               for i in xrange(len(positive_monomial_lists[block]))\
               for j in xrange(i+1)]
  qcoeff_positions_rev = dict([(qcoeff_positions[k], k) for k in xrange(len(qcoeff_positions))])

  lcoeff_positions=[(block, i)\
               for block in xrange(len(equality_monomial_lists))\
               for i in xrange(len(equality_monomial_lists[block]))]
  lcoeff_positions_rev = dict([(lcoeff_positions[k], k) for k in xrange(len(lcoeff_positions))])

  def get_qcoeff_position(block, i, j):
    if i < j:
      return qcoeff_positions_rev[(block, j, i)]
    else:
      return qcoeff_positions_rev[(block, i, j)]

  def get_lcoeff_position(block, i):
    return lcoeff_positions_rev[(block, i)] + len(qcoeff_positions)

  def vector_to_blocks(v):
    pblocks = [matrix(v.base_ring(), len(block), sparse=sparseflag) for block in positive_monomial_lists]
    eblocks = [vector(v.base_ring(), len(block), sparse=sparseflag) for block in equality_monomial_lists] 
    for k in v.nonzero_positions():
      if k < len(qcoeff_positions):
        (pblock, i, j)=qcoeff_positions[k]
        pblocks[pblock][i,j] = pblocks[pblock][j,i] = v[k]
      elif k < len(qcoeff_positions) + len(lcoeff_positions):
        (eblock, i) = lcoeff_positions[k - len(qcoeff_positions)]
        eblocks[eblock][i] = v[k]
    return (pblocks, eblocks)

  def apply_blocks(pblocks, eblocks):
    r = polynomial_ring(0)
    for k in xrange(len(positive_monomial_lists)):
      v = vector(polynomial_ring, positive_monomial_lists[k], sparse=sparseflag)
      r += positive_polynomials[k] * (v * pblocks[k] * v)
    for k in xrange(len(equality_monomial_lists)):
      v = vector(polynomial_ring, equality_monomial_lists[k], sparse=sparseflag)
      r += equality_polynomials[k] * (v * eblocks[k])
    return r

  constraint_space = VectorSpace(QQ, len(qcoeff_positions)+len(lcoeff_positions)+1, sparse=sparseflag)
  print "Dimension of search space: ", constraint_space.dimension()

  constraint_map = {}
  for (exponents_t, scalar) in rhs_polynomial.dict().iteritems():
    exponents = tuple(exponents_t)
    v=constraint_space(0)
    v[len(v)-1]=-scalar
    constraint_map[exponents]=v

  def add_constraint_coeff(k, exponents_t, coeff):
    exponents=tuple(exponents_t)
    if not constraint_map.has_key(exponents):
      constraint_map[exponents]=constraint_space(0)
    constraint_map[exponents][k] += coeff

  for block in xrange(len(positive_polynomials)):
    monomials = positive_monomial_lists[block]
    for i in xrange(len(monomials)):
      for j in xrange(len(monomials)):
        k=get_qcoeff_position(block, i, j)
        for (exponents_t, coeff) in (monomials[i]*monomials[j]*positive_polynomials[block]).dict().iteritems():
          add_constraint_coeff(k, exponents_t, coeff)

  for block in xrange(len(equality_polynomials)):
    monomials = equality_monomial_lists[block]
    for i in xrange(len(monomials)):
      k=get_lcoeff_position(block, i)
      for (exponents_t, coeff) in (monomials[i]*equality_polynomials[block]).dict().iteritems():
        add_constraint_coeff(k, exponents_t, coeff)

  generators=identity_matrix(constraint_space.dimension(),sparse=sparseflag)

  print "building constraint matrix"
  sys.stdout.flush()
  constraint_matrix=build_matrix_from_rows(constraint_map.values())

  print "echelonizing"
  sys.stdout.flush()
  constraint_matrix.echelonize()

  solution = ()
  while true:
    constraint_matrix = constraint_matrix * generators.transpose()
    print "constraint matrix is", constraint_matrix.nrows(), "per", constraint_matrix.ncols()
    print "echelonizing"
    sys.stdout.flush()
    constraint_matrix.echelonize();
    print "echelonizing done"

    print "nullspace2"
    # very slow; replaced by next line: solution_matrix=constraint_matrix.right_kernel().matrix()
    sys.stdout.flush()
    solution_matrix=right_kernel_matrix_from_echelon(constraint_matrix)
    print "nullspace2 end"

    if test:
      assert (constraint_matrix * solution_matrix.transpose()==0)

    if solution_matrix.nrows()==0:
      print "trivial kernel"
      return ()
    print "kernel has dimension", solution_matrix.nrows()

    last_pivot = solution_matrix[solution_matrix.nrows()-1, solution_matrix.ncols()-1]
    if last_pivot==0:
      print "kernel does not solve affine part"
      return ()
    solution_matrix.rescale_row(solution_matrix.nrows()-1, 1/last_pivot)
    generators = solution_matrix * generators

    if reuse_solutions and solution != ():
      a = solution_matrix[0:solution_matrix.nrows()-1,0:solution_matrix.ncols()-1].change_ring(RDF).dense_matrix()
      b = vector(RDF, solution) - vector(RDF, solution_matrix.row(solution_matrix.nrows()-1)[0:solution_matrix.ncols()-1])
      at = a.transpose()
      print "solving"
      import numpy
      from numpy import linalg
      solution_hint = vector(RDF, linalg.solve(a*at, a*b))
      solution_hint1 = vector(RDF, list(solution_hint) + [1])
      v_hint = solution_hint1 * generators
      print "delta:", n((previous_v - v_hint).norm())/n(previous_v.norm())
    else:
      solution_hint = ()

    (pblocks, eblocks) = vector_to_blocks(generators.row(generators.nrows()-1))
    if test:
      assert apply_blocks(pblocks, eblocks)==rhs_polynomial

    mf0b = [-pblock for pblock in pblocks]
    fisb=[]

    print "kernel vectors"
    sys.stdout.flush()
    for v in generators.rows()[0:generators.nrows()-1]:
      (pblocks, eblocks) = vector_to_blocks(v)
      if test:
        assert apply_blocks(pblocks, eblocks)==0
      fisb.append(pblocks)
    print "kernel vectors end"

    if len(fisb) == 0:
      (pblocks, eblocks) = vector_to_blocks(generators.row(0))
      (fpblocks, feblocks) = (pblocks, eblocks)
    else:
      #solution = dsdp_solve("sdp_problem", mf0b, fisb, [0 for b in fisb], solution_hint)
      solution = csdp_solve("sdp_problem", mf0b, fisb, [0 for b in fisb])
      #solution = sdpa_solve("sdp_problem", mf0b, fisb, [0 for b in fisb])
      if solution == ():
        print "no solution"
        return ()
      print "got solution"
      sys.stdout.flush()

      fv = vector(RDF,list(solution) + [1],sparse=sparseflag) * generators
      v = vector(QQ,list(solution) + [1],sparse=sparseflag) * generators
      previous_v = v

      print "solution vector reassembled"
      (fpblocks, feblocks) = vector_to_blocks(fv)
      (pblocks, eblocks) = vector_to_blocks(v)

    is_sdp = True
    constraint_matrix = matrix(QQ,sum([block.nrows()^2 for block in pblocks]),len(v),sparse=True)
    print "got space for ", constraint_matrix.nrows(), "x", constraint_matrix.ncols(), "constraints"
    constraints_nr = 0

    for block in xrange(len(pblocks)):
      print "block", block
      sys.stdout.flush()

      block_is_sdp=()

      block_is_sdp=None
      if numeric_sdp_test:
        try:
          if least_eigenvalue_is_positive(pblocks[block]):
            block_is_sdp=True
            print "looks not sdp"
          else:
            block_is_sdp=False
            print "looks sdp"
        except ValueError:
          block_is_sdp=None

      if block_is_sdp == None:
        if is_positive_semidefinite(pblocks[block]):
          block_is_sdp=True
          print "is sdp"
        else:
          block_is_sdp=False
          print "is not sdp"

      is_sdp = is_sdp and block_is_sdp

      if not block_is_sdp:
        # too slow img=build_matrix_from_rows(pblocks[block].rows(),sparse=False)
        print "stacking and echelonizing"
        img = stack_and_echelonize_matrices([mf0b[block]] + [fib[block] for fib in fisb])

        rank = len(img.pivots())
        print "echelonized with rank", rank
        if rank < img.nrows():
          img=img[0:rank,:]

        ker=left_near_kernel(img * fpblocks[block] * img.transpose())
        print "kernel size:", len(ker)

        for ker_v_rel in ker:
          ker_v = ker_v_rel * img
          print ker_v
          for i in xrange(pblocks[block].nrows()):
            for j in ker_v.nonzero_positions():
              constraint_matrix[constraints_nr,get_qcoeff_position(block, i, j)] += ker_v[j]
            constraints_nr = constraints_nr + 1
          print "number of constraints", constraints_nr
          print "echelonizing constraints"
          #constraint_matrix.echelonize()
          #constraints_nr = len(constraint_matrix.pivots())
          print "reduced constraints", constraints_nr, "filling:", len(constraint_matrix.dict().keys())

    if is_sdp:
      print "success"
      return (pblocks,eblocks)

    print "constraints:", constraints_nr
    if constraints_nr==0:
      print "with zero constraints, cannot progress"
      return ()

def solve_sos_equation_sos(polynomial_ring, positive_polynomials, positive_monomial_lists, equality_polynomials, equality_monomial_lists, rhs_polynomial):
  ret = solve_sos_equation(polynomial_ring, positive_polynomials, positive_monomial_lists, equality_polynomials, equality_monomial_lists, rhs_polynomial)
  if ret == ():
    return ()
  (pblocks, eblocks) = ret
  return (map(sdp_matrix_to_sos, pblocks), eblocks)
