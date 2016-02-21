#!/usr/bin/env python

from __future__ import print_function
import z3

class LetterConnections:
  def __init__(self,data):
    data = [line for line in data.split("\n") if line != ""]
    self.xsize  = len(data[0])
    self.ysize  = len(data)

    self.letters = {}
    self.rletters = {}
    self.starts = {}
    self.ends = {}
    self.special_ends = {}
    self.special_starts = {}

    data = {(x,y): data[y][x] for x in range(self.xsize) for y in range(self.ysize)}

    for (x,y) in sorted(data):
      letter = data[x,y]
      if letter == ".":
        continue
      if letter in self.letters:
        if letter in self.ends:
          raise Exception("Letter %s occurs more than twice" % letter)
        self.ends[letter] = (x,y)
        self.special_ends[x,y] = letter
      else:
        i = len(self.letters)
        self.letters[letter] = i
        self.rletters[i] = letter
        self.starts[letter] = (x,y)
        self.special_starts[x,y] = letter
    for letter in self.letters:
      if letter not in self.ends:
        raise Exception("Letter %s occurs only once" % letter)

    self.solver = z3.Solver()

  def print_answer(self):
    for y in range(self.ysize):
      for x in range(self.ysize):
        li = int(str(self.model.evaluate(self.line[x,y])))
        l = self.rletters[li]
        d = int(str(self.model.evaluate(self.dir[x,y])))
        if (x,y) == self.starts[l]:
          print(u"\u2190\u2191\u2192\u2193"[d]+l+" ", end="")
        elif (x,y) == self.ends[l]:
          print("*"+l+" ", end="")
        else:
          print(u"\u2190\u2191\u2192\u2193"[d]+l.lower()+" ", end="")
      print("")

  def line_var(self, x, y):
    v = z3.Int("l%d,%d" % (x,y))
    self.solver.add(v >= 0)
    self.solver.add(v < len(self.letters))
    return v

  def dir_var(self, x, y):
    v = z3.Int("d%d,%d" % (x,y))
    self.solver.add(v >= 0)
    self.solver.add(v <= 3)
    return v

  def potential_incoming(self, x0, y0):
    result = []
    for (x,y,d) in [(x0+1,y0,0),(x0-1,y0,2),(x0,y0+1,1),(x0,y0-1,3)]:
      if (x,y) not in self.dir:
        continue
      if (x,y) in self.special_ends:
        continue
      result.append((x,y,d))
    return result

  # Surely Z3 must have a thing for it
  def condition_exactly_one(self, conds):
    self.solver.add(z3.Or(conds))
    for ci in range(len(conds)):
      for cj in range(len(conds)):
        if ci < cj:
          self.solver.add(z3.Or(z3.Not(conds[ci]), z3.Not(conds[cj])))

  def solve(self):
    self.line = {(x,y): self.line_var(x,y) for x in range(self.xsize) for y in range(self.ysize)}
    self.dir  = {(x,y): self.dir_var(x,y) for x in range(self.xsize) for y in range(self.ysize)}

    for letter in self.letters:
      i = self.letters[letter]
      self.solver.add(self.line[self.starts[letter]] == i)
      self.solver.add(self.line[self.ends[letter]] == i)

    for y in range(self.ysize):
      for x in range(self.ysize):
        if (x,y) in self.special_ends:
          continue
        # Direction Left
        if x == 0:
          self.solver.add(self.dir[x,y] != 0)
        else:
          self.solver.add(z3.Implies(self.dir[x,y] == 0, self.line[x,y] == self.line[x-1,y]))
          self.solver.add(z3.Implies(self.dir[x,y] == 0, self.dir[x-1,y] != 2))
        # Direction Up
        if y == 0:
          self.solver.add(self.dir[x,y] != 1)
        else:
          self.solver.add(z3.Implies(self.dir[x,y] == 1, self.line[x,y] == self.line[x,y-1]))
          self.solver.add(z3.Implies(self.dir[x,y] == 1, self.dir[x,y-1] != 3))
        # Direction Right
        if x == self.xsize - 1:
          self.solver.add(self.dir[x,y] != 2)
        else:
          self.solver.add(z3.Implies(self.dir[x,y] == 2, self.line[x,y] == self.line[x+1,y]))
          self.solver.add(z3.Implies(self.dir[x,y] == 2, self.dir[x+1,y] != 0))
        # Direction Down
        if y == self.ysize - 1:
          self.solver.add(self.dir[x,y] != 3)
        else:
          self.solver.add(z3.Implies(self.dir[x,y] == 3, self.line[x,y] == self.line[x,y+1]))
          self.solver.add(z3.Implies(self.dir[x,y] == 3, self.dir[x,y+1] != 1))

    # Everything except start node has one incoming arrow
    # End nodes not counted for this

    for y in range(self.ysize):
      for x in range(self.ysize):
        if (x,y) in self.special_starts:
          continue
        potential_incoming = self.potential_incoming(x,y)
        self.condition_exactly_one([(self.dir[i,j] == d) for (i,j,d) in potential_incoming])
    if self.solver.check() == z3.sat:
      self.model = self.solver.model()
      self.print_answer()
    else:
      print("failed to solve")

LetterConnections(
"""
..KJ....FE
.FJ.......
......G...
.K.I......
.......D..
IE......B.
...H...CD.
...A..C...
.A.H......
...B.G....
"""
).solve()
