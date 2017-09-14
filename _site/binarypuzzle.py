size = 10
game = '''
...00....1
........01
..0...1.0.
.1...1....
.0.0.11...
1.....1...
.0...1....
...1.1.11.
..........
..00......
'''

# setup variables and solver

import z3

vs = [(r,c) for r in range(size) for c in range(size)]
v  = [[z3.BitVec('v%d%d' % (r,c),8)  for c in range(size)] for r in range(size)]
s = z3.Solver()

# add game constraints

game = filter(lambda x:x in '01.', game)
assert size*size == len(game)

for ((r,c), val) in zip(vs, game):
    if val == '.':  s.add(0 <= v[r][c], v[r][c] <= 1)
    else:           s.add(v[r][c] == (int(val)))

# add board contraints

def row(n):   return [(n, i) for i in range(size)]
def col(n):   return [(i, n) for i in range(size)]

def row3(n,m):   return [(n, i) for i in range(m,m+3)]
def col3(n,m):   return [(i, n) for i in range(m,m+3)]

for i in xrange(size):
    s.add(z3.Sum([v[r][c] for r,c in row(i)]) == (size/2))
    s.add(z3.Sum([v[r][c] for r,c in col(i)]) == (size/2))

for i in xrange(size):
    for j in xrange(size-2):
        s.add(z3.Sum([v[r][c] for r,c in row3(i,j)]) <= 2)
        s.add(z3.Sum([v[r][c] for r,c in row3(i,j)]) >= 1)
        s.add(z3.Sum([v[r][c] for r,c in col3(i,j)]) <= 2)
        s.add(z3.Sum([v[r][c] for r,c in col3(i,j)]) >= 1)

s.add(z3.Distinct([z3.Concat([v[r][c] for r,c in row(i)]) for i in xrange(size)]))
s.add(z3.Distinct([z3.Concat([v[r][c] for r,c in col(i)]) for i in xrange(size)]))


# find solution
print s.check()
m   = s.model()
sol = [[m[v[r][c]] for c in range(size)] for r in range(size)]

# print solution

for r,c in vs:
    print str(sol[r][c]) + ("\n" if c==(size-1) else ""),
