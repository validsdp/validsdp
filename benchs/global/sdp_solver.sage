fake_sdp=False

def write_sdpa_problem_q(file, f0b, fisb, costs):
  nblocks = len(f0b)
  for fib in fisb:
    assert len(fib) == nblocks
  print >> file, len(fisb)
  print >> file, nblocks
  sizes = [m.ncols() for m in f0b]
  for size in sizes:
    print >> file, size,
  print >> file
  assert len(costs) == len(fisb)
  for cost in costs:
    print >> file, cost,
  print >> file
    
  for block in xrange(nblocks):
    for i, j in f0b[block].nonzero_positions():
      if j>= i:
        print >> file, 0, block+1, i+1, j+1, (f0b[block][i, j])

  for matrix in xrange(len(fisb)):
    for block in xrange(nblocks):
      for i, j in fisb[matrix][block].nonzero_positions():
        if j>= i:
          print >> file, matrix+1, block+1, i+1, j+1, (fisb[matrix][block][i, j])

### numerical SDP
def write_sdpa_problem(file, f0b, fisb, costs):
  nblocks = len(f0b)
  for fib in fisb:
    assert len(fib) == nblocks
  print >> file, len(fisb)
  print >> file, nblocks
  sizes = [m.ncols() for m in f0b]
  for size in sizes:
    print >> file, size,
  print >> file
  assert len(costs) == len(fisb)
  for cost in costs:
    print >> file, cost,
  print >> file
    
  for block in xrange(nblocks):
    for i, j in f0b[block].nonzero_positions():
      if j>= i:
        print >> file, 0, block+1, i+1, j+1, n(f0b[block][i, j])

  for matrix in xrange(len(fisb)):
    for block in xrange(nblocks):
      for i, j in fisb[matrix][block].nonzero_positions():
        if j>= i:
          print >> file, matrix+1, block+1, i+1, j+1, n(fisb[matrix][block][i, j])

import sys

# def spawn_process(args):
#   import subprocess
#   return subprocess.call(args)

def spawn_process(args):
  import os
  return os.spawnvp(os.P_WAIT, args[0], args)
 
def dsdp_solve(filename, f0b, fisb, costs, y0=()):
  filename_qdat = filename+".dat-s"
  filename_res = filename+".result"
  
  with open(filename_qdat, "w") as file:
    write_sdpa_problem(file, f0b, fisb, costs)
    file.close()
  sys.stdout.flush()

  if y0==():
    if not fake_sdp:
      spawn_process(["dsdp5", filename_qdat, "-save", filename_res])
  else:
    assert (len(y0) == len(fisb))
    filename_y0 = filename+".y0"
    with open(filename_y0, "w") as file:
      for coeff in y0:
        print >> file, coeff,
      print >> file
      file.close()
    if not fake_sdp:
      spawn_process(["dsdp5", filename_qdat, "-save", filename_res, "-y0", filename_y0])

  print "dsdp5 finished, reading file"  
  with open(filename_res, "r") as file:
    solution = map(float, file.readline().split())
    file.close()
  return solution

def csdp_solve(filename, f0b, fisb, costs):
  import subprocess
  filename_qdat = filename+".dat-s"
  filename_res = filename+".result"
  
  with open(filename_qdat, "w") as file:
    write_sdpa_problem(file, f0b, fisb, costs)
    file.close()
  subprocess.call(["csdp", filename_qdat, filename_res])
  
  with open(filename_res, "r") as file:
    solution = map(float, file.readline().split())
    file.close()
  return solution

def sdpa_solve(filename, f0b, fisb, costs):
  import subprocess
  filename_qdat = filename+".dat-s"
  filename_res = filename+".result"
  
  with open(filename_qdat, "w") as file:
    write_sdpa_problem(file, f0b, fisb, costs)
    file.close()
  subprocess.call(["sdpa", "-p", "param.sdpa", "-o", filename_res, "-ds", filename_qdat])
  
  with open(filename_res, "r") as file:
    found=False
    while True:
      line=file.readline()
      if line=='xVec = \n':
        found=true
        break
    line=file.readline()
    solution=map(float, line[1:len(line)-2].split(','))
    file.close()
  return solution


def sdp_solve(filename, f0b, fisb, costs):
  if len(fisb) == 0:
    return [] # if the problem is trivial, return trivial answer
  else:
    import sys
    sys.stdout.flush()
    with open(filename + ".qdat-s", "w") as file:
      write_sdpa_problem_q(file, f0b, fisb, costs)
      file.close()
    return csdp_solve(filename, f0b, fisb, costs)

def read_sdp_solution_q(file):
  nblocks = int(file.readline())
  block_sizes = map(int, file.readline().split())
  matrices=[Matrix(QQ, size) for size in block_sizes]
  assert(len(block_sizes) == nblocks)
  for line in file:
    (dummy, block, i, j, coeff) = line.split()
    dummy=int(dummy)
    block = int(block)
    i = int(i)
    j = int(j)
    coeff = QQ(coeff)
    assert(dummy == 1)
    assert(block >= 1 and block <= nblocks)
    assert(i >= 1 and i <= block_sizes[block-1])
    assert(j >= i and j <= block_sizes[block-1])
    matrices[block-1][i-1,j-1] = coeff
    matrices[block-1][j-1,i-1] = coeff
  return matrices
  
def sdp_solve_q(filename, f0b, fisb, costs):
  if len(fisb) == 0:
    return [-block for block in f0b] # if the problem is trivial, return trivial answer
  else:
    filename_dat = filename+".dat-s"
    filename_qdat = filename+".qdat-s"
    filename_res = filename+".result"
    import sys
    sys.stdout.flush()
    with open(filename_dat, "w") as file:
      write_sdpa_problem(file, f0b, fisb, costs)
      file.close()
    with open(filename_qdat, "w") as file:
      write_sdpa_problem_q(file, f0b, fisb, costs)
      file.close()
    import subprocess
    if subprocess.call(["../cpp_trunk/sdp_solver", filename_qdat, filename_res])==0:
      with open(filename_res, "r") as file:
        v = read_sdp_solution_q(file)
        file.close()
      return v
    else:
      return ()
