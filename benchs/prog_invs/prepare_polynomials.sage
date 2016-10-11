def products01(polynomials):
  if len(polynomials)==0:
    return [polynomial_ring(1)]
  l2=products01(polynomials[1:len(polynomials)])
  p=polynomials[0]
  return l2 + [p*p2 for p2 in l2]

def monomial_basis_wrt(degree, gens):
  if degree==0:
    return [polynomial_ring(1)]
  if len(gens)==0:
    return [polynomial_ring(1)]
  x=gens[0]
  others=gens[1:len(gens)]
  return [(x^a)*b for a in xrange(degree+1) for b in monomial_basis_wrt(degree-a, others)]

def monomial_basis(degree):
  return monomial_basis_wrt(degree, polynomial_ring.gens())

def monomial_basis_wrt_homogeneous(degree, gens):
  if degree==0:
    return [polynomial_ring(1)]
  if len(gens)==0:
    return []
  x=gens[0]
  if len(gens)==1:
    return [x^degree]
  others=gens[1:len(gens)]
  return [(x^a)*b for a in xrange(degree+1) for b in monomial_basis_wrt_homogeneous(degree-a, others)]

def monomial_basis_homogeneous(degree):
  return monomial_basis_wrt_homogeneous(degree, polynomial_ring.gens())

def group_by(f, l):
  dico={}
  for item in l:
    key = f(item)
    if dico.has_key(key):
      dico[key].append(item)
    else:
      dico[key] = [item]
  return dico.values()

def monomial_grouping(monomial):
  l = list(monomial.exponents()[0])
  l.sort()
  return tuple(l)

def monomial_basis_wrt_symmetric(degree, gens):
  return [sum(l) for l in group_by(monomial_grouping, monomial_basis_wrt(degree, gens))]

def monomial_basis_symmetric(degree):
  return monomial_basis_wrt_symmetric(degree, polynomial_ring.gens())

def monomial_basis_wrt_homogeneous_symmetric(degree, gens):
  return [sum(l) for l in group_by(monomial_grouping, monomial_basis_wrt_homogeneous(degree, gens))]

def monomial_basis_homogeneous_symmetric(degree):
  return monomial_basis_wrt_homogeneous_symmetric(degree, polynomial_ring.gens())
