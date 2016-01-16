#!/usr/bin/env python


from __future__ import print_function
import z3

class Bridges:
  def __init__(self, data):
    data = [line.split() for line in data.split("\n")]
    data = [line for line in data if line != []]
    data = [[None if c == "_" else int(c) for c in line] for line in data]
    self.xsize = len(data[0])
    self.ysize = len(data)
    self.data = {(x,y): data[y][x] for x in range(self.xsize) for y in range(self.ysize)}
    self.solver = z3.Solver()

  def print_answer(self):
    picture = [([" "] * (3*self.xsize))  for y in range(self.ysize*3)]

    for (x,y) in self.data:
      if self.data[x,y] == None:
        u = int(str(self.model.evaluate(self.vars[x,y,"u"])))
        l = int(str(self.model.evaluate(self.vars[x,y,"l"])))
        if u > 0:
          picture[y*3+1][x*3+1] = u" |\u2016"[u]
        elif l > 0:
          picture[y*3+1][x*3+1] = u" -="[l]
        else:
          picture[y*3+1][x*3+1] = " "
      else:
        picture[y*3+1][x*3+1] = str(self.data[x,y])

    for (x,y) in self.data:
      u = int(str(self.model.evaluate(self.vars[x,y,"u"])))
      d = int(str(self.model.evaluate(self.vars[x,y,"d"])))
      l = int(str(self.model.evaluate(self.vars[x,y,"l"])))
      r = int(str(self.model.evaluate(self.vars[x,y,"r"])))

      picture[y*3+1][x*3  ] = u" -="[l]
      picture[y*3+1][x*3+2] = u" -="[r]
      picture[y*3  ][x*3+1] = u" |\u2016"[u]
      picture[y*3+2][x*3+1] = u" |\u2016"[d]

    for row in picture:
      print("".join(row))

  def int012(self, x, y, d):
    v = z3.Int("%d,%d,%s" % (x,y,d))
    self.solver.add(v >= 0)
    self.solver.add(v <= 2)
    return v

  def solve(self):
    self.vars = {}
    for x in range(self.xsize):
      for y in range(self.ysize):
        u = self.int012(x,y,"u")
        d = self.int012(x,y,"d")
        r = self.int012(x,y,"r")
        l = self.int012(x,y,"l")
        self.vars[x,y,"u"] = u
        self.vars[x,y,"d"] = d
        self.vars[x,y,"r"] = r
        self.vars[x,y,"l"] = l
        if self.data[x,y] == None:
          self.solver.add(u==d)
          self.solver.add(l==r)
          self.solver.add(z3.Or(u==0, l==0))
        else:
          self.solver.add(u+d+r+l == self.data[x,y])
        # Nothing goes out of the map
        if x == 0:
          self.solver.add(l == 0)
        if x == self.xsize - 1:
          self.solver.add(r == 0)
        if y == 0:
          self.solver.add(u == 0)
        if y == self.ysize - 1:
          self.solver.add(d == 0)

    for x in range(self.xsize):
      for y in range(self.ysize):
        if x != self.xsize-1:
          self.solver.add(self.vars[x,y,"r"] == self.vars[x+1,y,"l"])
        if y != self.ysize-1:
          self.solver.add(self.vars[x,y,"d"] == self.vars[x,y+1,"u"])

    if self.solver.check() == z3.sat:
      self.model = self.solver.model()
      self.print_answer()
    else:
      print("failed to solve")


bridges = Bridges(
"""
3 _ _ 6 _ _ 4
_ 1 _ _ _ _ _
_ _ _ 4 _ 4 _
_ _ _ _ _ _ _
_ _ 1 _ 3 _ _
1 _ _ _ _ 2 _
_ 3 _ _ 5 _ 3
"""
)
bridges.solve()
