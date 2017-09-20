---

layout: post
title: "Introduction to SAT solving using Z3"
description: "Little theory you should get (or maybe not)"
date: 2017-09-10
author: "Sudhakar Verma"
tags: [tech, code, tutorial]
comments: true
share: true

---

In Computer Science a SAT(satisfiability) problem is defined as follows
> Given a propositional formula comprising AND, OR, NOT and boolean variables(TRUE or FALSE), is there a combination of variables that evaluates the formula to true.

Its an NP complete problem. And its applications are vast lying not just in CS.

#### Satisfiability Modulo Theories (SMT)

Satisfiability modulo theories (SMT) generalizes boolean satisfiability (SAT) by adding equality reasoning, arithmetic, fixed-size bit-vectors, arrays, quantifiers and other useful first-order theories. This makes it much wider and useful.

In this post we won't go into details on how to write a solvers for such problems but instead learn on how such applications are used to solve complex puzzles by building up propositions.

### Enough theory? Get to code!
So what did the theory mean?
> Given any arbitrary set of assumptions and constraints an SMT solver would solve it for you if the constraints hold and if its not possible it would tell you so.

[Z3](https://github.com/Z3Prover/z3) is an SMT solver from Microsoft Research. It is one of the most widely used SMT solvers used out there. Its free(yeaaa) and bindings are available in about every popular language. I suggest you check the repository out. We'll try to solve a problem in Z3 using its python api.

So first lets install it. Using a virtualenv is a great idea as it'll not cause problems in your system wide python installation

```bash
$ pip install virtualenv
$ virtualenv z3
$ source ./z3/bin/activate
```

Then download its latest version from https://github.com/Z3Prover/z3/releases or directly git clone if you like to live rough(Arch Linux FTW!)

```bash
$ wget https://github.com/Z3Prover/z3/archive/z3-4.5.0.zip
$ unzip z3-4.5.0
$ python scripts/mk_make.py --python
$ cd build; make
$ make install
$ python
Python 2.7.12 (default, Nov 19 2016, 06:48:10)
[GCC 5.4.0 20160609] on linux2
Type "help", "copyright", "credits" or "license" for more information.
>>> from z3 import *
>>> z3.get_version_string()
'4.5.0'
```

And you're done.

Now to check the power of Z3 we'll try to make it solve a puzzle.
[Binary Puzzle](http://binarypuzzle.com/) is a puzzle with some constraints which are easy to implement in a program.

The puzzles look something like this.


![Puzzle](http://binarypuzzle.com/pic_daypuzzle.php?id=2324&grootte=4)

And the [rules](http://binarypuzzle.com/rules.php)
> Each binary puzzle should be solved according to the following rules:
1. Each box should contain a zero or a one.
2. No more than two similar numbers next to or below each other are allowed.
3. Each row and each column should contain an equal number of zeros and ones.
4. Each row is unique and each column is unique.
Each binary puzzle does only have one solution. You can always find this solution without guessing.

The puzzles is a square grid of even size. The rules are quite simple. You can try solving a couple of them by visiting the site. But where's the fun in that? So lets have a program which will solve this for us.

So start with the basics.
```python
>>> from z3 import *
>>> x = Int('x')
>>> y = Int('y')
>>> solve(x*x + y*y == 5)
[y = 2, x = -1]
```
Int is a basic data type you can declare in Z3. Here what we did is defined 2 Int variables x and y and we constrained their sum of squares to be 5. We can add more contraints as such.

```python
>>> solve(x >0, y > 0,x*x + y*y == 5)
[y = 1, x = 2]
>>> solve(x >0, y > 0,x*x + y*y == 25)
[y = 4, x = 3]
```
This will come in handy when you want to solve linear equations. Another data type is BitVec, a bit vector of a fixed length. These are like registers in your CPU. Fixed size and truncate on overflow. They can be referenced as integers too.
```python
>>> a = BitVec('a',32)
>>> b = BitVec('b',32)
>>> solve(a >0, b > 0,a*a + b*b == 5)
[b = 841045729, a = 1550054738]
```
Woah! What the heck is that. Seasoned computer scientists would consider that a solution. Here's why!
```python
>>> hex(841045729*841045729+1550054738*1550054738)
'0x2b2909a200000005'
```
Since we restricted our Bit Vectors to 32 bits any operation that overflows that limit will lead to unexpected results. For a 32 bit variable 0xffffffff is the max value it can attain.So this makes more sense.
```python
>>> hex((841045729*841045729+1550054738*1550054738)&0xffffffff)
'0x5'
```

So that's about it. Now you can add variables, set contraints and solve them. Here's a better way to do the same.

```python
>>> from z3 import *
>>> solver = Solver()
>>> a = Int('a',32)
>>> b = Int('b',32)
>>> solver.add(a > 0)
>>> solver.add(b > 0)
>>> solver.add(a*a + b*b == 25)
>>> solver.add(a + b < 10)
>>> solver.check()
sat
```
Its the same with an added constraint. If `solver.check()` returns `sat` that means the contraintsare true for at least one set of values. Now to fish out the solution.

```python
>>> solver.model()
[b = 3, a = 4]
>>> solver.model()[a]
4
>>> solver.model()[b]
3
```
Z3 has most of the native python operators overloaded for implementation in logic solving, so its not much different from plain english. I suggest you play around and find your way. Maybe even contribute to it on github!

Enough of that, lets get back to our puzzle. So first thing we need to represent the board in python. For some size

```python
vs = [(r,c) for r in range(size) for c in range(size)]
```

A 2D list to represent rows and columns in the game. next step is to define the game for Z3. I chose to consider every cell as a variable.

```python
v  = [[z3.BitVec('v%d%d' % (r,c),8)  for c in range(size)] for r in range(size)]
```

Here I have referenced BitVec of size 8 in a 2D list. The cell can have only 1 bit value {0 or 1}, but still I chose 8 (more on that later).
To represent our problem, I choose this representation
```python
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
```
A . means that position we need to solve. Iterate over the board and set them as variables having only {0, 1} Rule #1 in game rules.
```python
game = filter(lambda x:x in '01.', game)
assert size*size == len(game)
s = z3.Solver()
for ((r,c), val) in zip(vs, game):
    if val == '.':  s.add(0 <= v[r][c], v[r][c] <= 1)
    else:           s.add(v[r][c] == (int(val)))
```
Here I just cross checked all my characters, filtered out the waste and set up a solver. In the for loop I added constraints for '.'.
This sets up the game, but we still have not implemented the game logic.
According to Rule #3 Each row and each column should contain an equal number of zeros and ones.
```python
def row(n):   return [(n, i) for i in range(size)]
def col(n):   return [(i, n) for i in range(size)]

for i in xrange(size):
    s.add(z3.Sum([v[r][c] for r,c in row(i)]) == (size/2))
    s.add(z3.Sum([v[r][c] for r,c in col(i)]) == (size/2))
```
So there could be only size/2 1's and 0's both in a row and a column. I simplified that to a sum constraint.
According to Rule #2 No more than two similar numbers next to or below each other are allowed.
That means 000 and 111 is not allowed in the game. This means sum of 3 continuos cells can't be 0 or 3, 1 and 2 are okay.Adding that

```python
def row3(n,m):   return [(n, i) for i in range(m,m+3)]
def col3(n,m):   return [(i, n) for i in range(m,m+3)]

for i in xrange(size):
    for j in xrange(size-2):
        s.add(z3.Sum([v[r][c] for r,c in row3(i,j)]) <= 2)
        s.add(z3.Sum([v[r][c] for r,c in row3(i,j)]) >= 1)
        s.add(z3.Sum([v[r][c] for r,c in col3(i,j)]) <= 2)
        s.add(z3.Sum([v[r][c] for r,c in col3(i,j)]) >= 1)
```

That just leaves Rule #4 Each row is unique and each column is unique. Z3 has a Unique keyword.

```python
s.add(z3.Distinct([z3.Concat([v[r][c] for r,c in row(i)]) for i in xrange(size)]))
s.add(z3.Distinct([z3.Concat([v[r][c] for r,c in col(i)]) for i in xrange(size)]))
```

I turned each row and column to a bitvector and constrained then to be unique. This pretty much sums up the puzzle. Now if you issue a `s.check()` it returns a `sat` almost immediately. Print it out

```python
print s.check()
m   = s.model()
sol = [[m[v[r][c]] for c in range(size)] for r in range(size)]

# print solution

for r,c in vs:
    print str(sol[r][c]) + ("\n" if c==(size-1) else ""),
```

>sat
0 1 1 0 0 1 0 0 1 1
1 0 1 1 0 0 1 0 0 1
1 0 0 1 1 0 1 1 0 0
0 1 0 0 1 1 0 1 1 0
0 0 1 0 0 1 1 0 1 1
1 1 0 1 0 0 1 0 0 1
1 0 1 0 1 1 0 1 0 0
0 0 1 1 0 1 0 1 1 0
0 1 0 1 1 0 1 0 0 1
1 1 0 0 1 0 0 1 1 0

![Solved](http://i.imgur.com/W0WXGer.png)

For me Z3 has always been handy not just in CTFs but a couple of optimization projects. Give it a try!
