#!/usr/bin/env python

from __future__ import print_function
import z3

class Kakuro:
  def print_board(self):
    for y in range(self.ysize):
      for x in range(self.xsize):
        cell = self.data[x,y]
        if cell == None:
          if self.model and (x,y) in self.cells:
            a = str(self.model.evaluate(self.cells[x,y]))
            print(" [%s] " % a, end="")
          else:
            print("  _  ", end="")
        elif cell == (0,0):
          print("  x  ", end="")
        else:
          a,b = cell
          a = "  " if a == 0 else ("%2d" % a)
          b = "  " if b == 0 else ("%-2d" % b)
          print("%s/%s" % (a,b), end="")
        print(" ", end = "")
      print()

  def parse_cell(self, cell):
    if cell == "_":
      return None
    elif cell == "x":
      return (0,0)
    else:
      a,b = cell.split("/")
      a = 0 if a == "" else int(a)
      b = 0 if b == "" else int(b)
      return (a,b)

  def __init__(self, data):
    data = [[self.parse_cell(cell) for cell in line.split()] for line in data.split("\n") if line != ""]
    self.xsize = len(data[0])
    self.ysize = len(data)
    self.data = {(x,y): data[y][x] for x in range(self.xsize) for y in range(self.ysize)}
    self.solver = z3.Solver()

  def cell_var(self,x,y):
    v = z3.Int("c%d,%d" % (x,y))
    self.solver.add(v >= 1)
    self.solver.add(v <= 9)
    return v

  def setup_line(self, x0, y0, dx, dy, sum):
    if sum == 0:
      return
    vs = []
    x, y = x0+dx, y0+dy
    while (x,y) in self.cells:
      vs.append(self.cells[x,y])
      x += dx
      y += dy
    self.solver.add(z3.Distinct(vs))
    self.solver.add(z3.Sum(vs) == sum)

  def solve(self):
    self.cells = {(x,y): self.cell_var(x,y) for x in range(self.xsize) for y in range(self.ysize) if self.data[x,y] == None}
    for y in range(self.ysize):
      for x in range(self.xsize):
        cell = self.data[x,y]
        if cell == None:
          continue
        (a,b) = cell
        self.setup_line(x,y,0,1,a)
        self.setup_line(x,y,1,0,b)

    if self.solver.check() == z3.sat:
      self.model = self.solver.model()
      self.print_board()
    else:
      print("failed to solve")



Kakuro(
'''
  x     x     x   10/   24/   29/     x   11/   21/   10/
  x   11/   19/24   _     _     _     /6    _     _     _
  /31   _     _     _     _     _   10/20   _     _     _
  /4    _     _   22/18   _     _     _   23/13   _     _
  /18   _     _     _   24/26   _     _     _     _     _
  x   19/   30/16   _     _   10/11   _     _   11/   20/
  /34   _     _     _     _     _   23/23   _     _     _
  /7    _     _    9/16   _     _     _    3/4    _     _
  /24   _     _     _     /23   _     _     _     _     _
  /10   _     _     _     /11   _     _     _     x     x
'''
).solve()
