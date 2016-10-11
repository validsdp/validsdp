def is_positive_definite_using_sylvester(m):
    assert m.is_symmetric()
    for i in xrange(1,m.nrows()+1):
        if m[0:i,0:i].determinant() <= 0:
            return False
    return True

def is_positive_semidefinite_using_sylvester(m):
    if m.is_zero():
        return True
    b = Matrix(VectorSpace(QQ,3).subspace(m.rows(copy=False)).basis())
    return is_positive_definite_using_sylvester(b * m * b.transpose())

class IsNotPositiveSemidefinite(ValueError):
    def __init__ (self, matrix):
        self.matrix = matrix
    def __str__(self):
        return 'Is not positive semidefinite:\n' + self.matrix.str()

class IsNotSymmetric(ValueError):
    def __init__ (self, matrix):
        self.matrix = matrix
    def __str__(self):
        return 'Is not symmetric:\n' + self.matrix.str()

def tvv_matrix(v):
    return Matrix([v]).transpose() * Matrix([v])
#    return transpose(v) * Matrix([v])

def sdp_matrix_to_sos(m0):
    ret = []
    m=copy(m0)
    if not m.is_symmetric():
        raise IsNotSymmetric(m)
    dim = m.nrows()
    for i in xrange(dim):
        coeff = m[i, i]
        if coeff < 0:
            raise IsNotPositiveSemidefinite(m0)
        if coeff == 0:
            if not m.row(i).is_zero():
                raise IsNotPositiveSemidefinite(m0)
        else:
            v = m.row(i) / coeff
            m -= tvv_matrix(v) * coeff
            ret.append((coeff, v))
    return ret

def sos_to_sdp_matrix(sos):
    if len(sos)==0:
        return 0
    (coeff, v) = sos[0]
    dim = len(v)
    ret = Matrix(dim)
    for (coeff, v) in sos:
        ret += coeff * tvv_matrix(v)
    return ret

def is_positive_semidefinite_using_sos(m):
    try:
        sdp_matrix_to_sos(m)
        return True
    except IsNotPositiveSemidefinite:
        return False

def apply_sos(sos, monomials):
    r= 0
    for (coeff, v) in sos:
        r += coeff * (v * vector(monomials))^2
    return r
  
def apply_qmatrix(q, v):
  return v*q*v

def matrix_to_gauss(m0):
  ret = []
  m=copy(m0)
  if not m.is_symmetric():
    raise IsNotSymmetric(m)
  dim = m.nrows()
  for i in xrange(dim):
    if m.row(i) == 0:
      continue
    for j in xrange(i, dim):
      coeff = m[j, j]
      if coeff != 0:
        break
    if coeff != 0:
      v = m.row(j) / coeff
      m -= tvv_matrix(v) * coeff
      ret.append((coeff, v))
    else:
      # Only zeroes on the diagonal
      rowi = m.row(i)
      for j in xrange(i, dim):
        coeff = rowi[j]
        if coeff != 0:
          break
      assert coeff != 0 # otherwise we'd have skipped the row
      rowi[i] /= coeff
      rowj = m.row(j) /coeff
      rowi[i] = 1
      rowi[j] = 0
      rowj[i] = 0
      rowj[j] = 1
      u = rowi + rowj
      v = rowi - rowj
      coeff /= 2
      m -= tvv_matrix(u) * coeff
      m += tvv_matrix(v) * coeff
      ret.append((coeff, u))
      ret.append((-coeff, v))
  return ret
    
def signature_using_sos(q):
  signs = [sgn(x) for (x,v) in matrix_to_gauss(q)]
  positive = signs.count(1)
  negative = signs.count(-1)
  # zeroes don't appear in the sum
  return (signs.count(1), q.nrows()-positive-negative, signs.count(-1))

def signature_using_evs(q):
  signs = map(sgn, q.eigenvalues())
  return (count(signs, 1), count(signs, 0), count(signs, -1))

def signature_using_charpoly(q):
  assert(q.is_symmetric())
  signs=map(sgn, q.dense_matrix().charpoly().coeffs())
  zeroes = 0
  for sign in signs:
    if sign != 0:
      break
    zeroes = zeroes+1
  if zeroes == len(signs):
    return (0, zeroes, 0)
  current = signs[zeroes]
  positives = 0    
  for sign in signs[zeroes+1:len(signs)]:
    if sign != current:
      positives = positives+1
    current = sign
  return (positives, zeroes, q.nrows()-positives-zeroes)

def signature(q):
  return signature_using_sos(q)

def is_positive_semidefinite_using_signature(q):
  print "is sdp?"
  (positives, zeroes, negatives) = signature(q)
  return negatives==0

def is_positive_definite_using_signature(q):
  print "is dp?"
  (positives, zeroes, negatives) = signature(q)
  return positives==q.nrows()

def is_positive_semidefinite(q):
  return is_positive_semidefinite_using_sos(q)

def least_eigenvalue_is_positive(q):
  assert(q.is_symmetric())
  v = vector(RDF, [(i * 111313214) % 117712117 for i in xrange(q.nrows())])
  v = v / v.norm()
  q_num = q.change_ring(RDF)
  i = 0
  is_sdp = True
  while i < 6:
    if v * q_num * v < 0:
      is_sdp = False
      break
    v = q_num.solve_right(v)
    v = v / v.norm()
    i = i+1
  return is_sdp
