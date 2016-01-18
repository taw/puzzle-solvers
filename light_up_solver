#!/usr/bin/env python

from __future__ import print_function
import z3

class LightUp:
  def __init__(self, data):
    data = [line for line in data.split("\n") if line != ""]
    data = [[c for c in line] for line in data]
    self.xsize = len(data[0])
    self.ysize = len(data)
    self.data  = {(x,y): data[y][x] for x in range(self.xsize) for y in range(self.ysize)}
    self.solver = z3.Solver()

  def print_answer(self):
    for y in range(self.ysize):
      for x in range(self.xsize):
        if self.data[x,y] != ".":
          print(self.data[x,y], end="")
        elif str(self.model.evaluate(self.lamps[x,y])) == "1":
          print("*", end="")
        else:
          print(" ", end="")
      print("")

  def int01(self,x,y):
    v = z3.Int("l%d,%d" % (x,y))
    self.solver.add(v >= 0)
    self.solver.add(v <= 1)
    return v

  def lamps_next_to_cell(self,x,y):
    return [self.lamps[i,j] for (i,j) in (x-1,y),(x+1,y),(x,y-1),(x,y+1) if (i,j) in self.lamps]

  def raycast_cells(self,x0,y0):
    result = []
    for (dx,dy) in [(1,0),(-1,0),(0,1),(0,-1)]:
      x = x0+dx
      y = y0+dy
      while (x,y) in self.data and self.data[x,y] == ".":
        result.append(self.lamps[x,y])
        x += dx
        y += dy
    return result

  def solve(self):
    self.lamps = {(x,y): self.int01(x,y) for x in range(self.xsize) for y in range(self.ysize)}

    # No lamps on walls
    # Numbers count lamps next to node (diagonals don't count)

    for y in range(self.ysize):
      for x in range(self.xsize):
        if self.data[x,y] != ".":
          self.solver.add(self.lamps[x,y] == 0)
          if self.data[x,y] in "01234":
            self.solver.add(z3.Sum(self.lamps_next_to_cell(x,y)) == int(self.data[x,y]))

    # Every cell is in raycast of a lamp
    # No lamp is in raycast of another lamp
    for y in range(self.ysize):
      for x in range(self.xsize):
        raycast = z3.Sum(self.raycast_cells(x,y))
        self.solver.add(z3.Implies(self.lamps[x,y] == 0, raycast >= 1))
        self.solver.add(z3.Implies(self.lamps[x,y] == 1, raycast == 0))

    if self.solver.check() == z3.sat:
      self.model = self.solver.model()
      self.print_answer()
    else:
      print("failed to solve")

LightUp(
"""
....0..
.......
x.2.x..
...3...
..x.x.3
.......
..1....
"""
).solve()
