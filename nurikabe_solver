#!/usr/bin/env python

from __future__ import print_function
import z3

class Nurikabe:
  def __init__(self, data):
    data = [line for line in data.split("\n") if line != ""]
    data = [[(None if c == "." else int(c)) for c in line] for line in data]
    self.xsize = len(data[0])
    self.ysize = len(data)
    self.data = {(x,y):data[y][x] for x in range(self.xsize) for y in range(self.xsize)}
    self.solver = z3.Solver()

    self.islands = {}
    self.rislands = {}
    for y in range(self.ysize):
      for x in range(self.xsize):
        if self.data[x,y] != None:
          i = len(self.islands) + 1
          self.islands[x,y] = i
          self.rislands[i] = (x,y)

  def print_answer(self):
    for y in range(self.ysize):
      for x in range(self.xsize):
        i = int(str(self.model.evaluate(self.vars[x,y])))
        if self.data[x,y] != None:
          # self.data[x,y]
          print("x%02d " % i, end="")
        else:
          if i == 0:
            print("#   " , end="")
          else:
            print(".%02d " % i, end="")
      print("")

  def island_var(self, x, y):
    v = z3.Int("v%d,%d" % (x,y))
    self.solver.add(v >= 0)
    self.solver.add(v <= len(self.islands))
    return v

  def ivar(self, x, y, i):
    v = z3.Int("i%d,%d,%d" % (x,y,i))
    self.solver.add(v >= 0)
    self.solver.add(v <= 1)
    return v

  def solve(self):
    self.vars  = {(x,y):self.island_var(x,y) for x in range(self.xsize) for y in range(self.ysize)}
    self.ivars = {(x,y,i):self.ivar(x,y,i) for x in range(self.xsize) for y in range(self.ysize) for i in range(len(self.islands)+1) }

    # No black squares
    for x in range(self.xsize-1):
      for y in range(self.ysize-1):
        self.solver.add(z3.Or(
          self.vars[x,y] != 0,
          self.vars[x+1,y] != 0,
          self.vars[x,y+1] != 0,
          self.vars[x+1,y+1] != 0
        ))

    for x in range(self.xsize-1):
      for y in range(self.ysize-1):
        for i in range(len(self.islands)+1):
          self.solver.add(
            (self.ivars[x,y,i] == 1) == (self.vars[x,y] == i)
          )
    for i in range(len(self.islands)+1):
      if i != 0:
        island_size = self.data[self.rislands[i]]
        print(i,island_size)
        self.solver.add(
          z3.Sum([self.ivars[x,y,i] for x in range(self.xsize) for y in range(self.ysize)]) == island_size
        )

    # Every island gets own ID
    for (x,y) in self.islands:
      self.solver.add(self.vars[x,y] == self.islands[x,y])

    # Islands don't touch
    for x in range(self.xsize):
      for y in range(self.ysize):
        for (x1,y1) in [(x+1,y), (x,y+1)]:
          if (x1,y1) not in self.vars:
            continue
          a = self.vars[x,y]
          b = self.vars[x1,y1]
          self.solver.add(z3.Or(
            a == 0,
            b == 0,
            a == b
          ))

    if self.solver.check() == z3.sat:
      self.model = self.solver.model()
      self.print_answer()
    else:
      print("failed to solve")

Nurikabe("""
.3.3.5.1.2
..........
........1.
2.4.......
.......2..
.....4....
4........1
..........
2.5..1.2..
..........
""").solve()
