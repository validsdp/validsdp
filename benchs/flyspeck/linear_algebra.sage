sparseflag = True

def right_kernel_matrix_from_echelon(m):
  nonpivots = m.nonpivots()
  pivots = m.pivots()
  kernel = Matrix(m.base_ring(), len(nonpivots), m.ncols(), sparse=sparseflag)
  for k in xrange(len(nonpivots)):
    j = nonpivots[k]
    kernel[k,j] = -1
    for i in m.nonzero_positions_in_column(j):
      kernel[k,pivots[i]] = m[i,j]
  return kernel

def round_matrix(m,sparse=sparseflag):
  r = matrix(ZZ, m.nrows(), m.ncols(), sparse=sparse)
  for (i, j) in m.nonzero_positions(copy=False):
    r[i, j] = ZZ(round(m[i, j]))
  return r

kernel_scaling = 1e18
relative_threshold1 = 3.
relative_threshold2 = 3.

def left_near_kernel(m):
  scaling = kernel_scaling / m.norm('frob')
  #zmat = block_matrix([round_matrix(m*scaling,sparse=false), identity_matrix(m.nrows())], 1, 2)
  zmat = block_matrix([round_matrix(m*scaling,sparse=false), identity_matrix(m.nrows())], nrows=1, ncols=2)
  reduced=zmat.LLL()
  thresh1 = vector(RDF,reduced.row(0)[m.ncols():reduced.ncols()]).norm()*relative_threshold1
  thresh2 = vector(RDF,reduced.row(0)).norm()*relative_threshold2
  return [row[m.ncols():reduced.ncols()] for row in reduced.rows()\
    if vector(RDF,row[m.ncols():reduced.ncols()]).norm() <= thresh1 \
    and vector(RDF,row).norm()<=thresh2]

def stack_matrices(l,sparse=sparseflag):
  rows=sum([m.nrows() for m in l])
  cols=l[0].ncols()
  for m in l[1:len(l)]:
    assert m.ncols()==cols
  r=matrix(l[0].base_ring(), rows, cols, sparse=sparse)
  row=0
  for m in l:
    r[row:row+m.nrows(),:] = m
    row += m.nrows()
  return r

def build_matrix_from_rows(l,sparse=sparseflag):
  assert len(l) > 0
  r=matrix(l[0].base_ring(), len(l), len(l[0]),sparse=sparse)
  for i in xrange(len(l)):
    r[i,:] = l[i]
  return r

def stack_and_echelonize_matrices_old(l,sparse=sparseflag):
  stacked = stack_matrices(l,sparse)
  stacked.echelonize()
  return stacked

def stack_and_echelonize_matrices(l,sparse=sparseflag):
  assert(len(l) > 0)
  dim = l[0].ncols()
  stacked = matrix(l[0].base_ring(), dim-1+max([m.nrows() for m in l]), dim, sparse=sparseflag)
  for m in l:
    if m==0:
      continue
    cdim = len(stacked.pivot_rows())
    print cdim, dim
    if cdim == dim:
      break
    stacked[dim-1:dim-1+m.nrows(),:] = m
    stacked.echelonize()
  return stacked
