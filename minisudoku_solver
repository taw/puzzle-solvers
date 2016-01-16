#!/usr/bin/env python

from __future__ import print_function
import z3

class MiniSudoku:
  def __init__(self, data):
    self.data = data
    self.solver = z3.Solver()

  # private
  def cell_var(self, cell, i, j):
    v = z3.Int("cell[%d,%d]" % (i+1, j+1))
    self.solver.add(v >= 1)
    self.solver.add(v <= 6)
    if cell != None:
      self.solver.add(v == cell)
    return v

  def print_answer(self):
    for i in range(6):
      for j in range(6):
        print(self.model.evaluate(self.cells[i][j]), "", end="")
      print()

  def solve(self):
    self.cells = [
      [self.cell_var(self.data[j][i], i, j) for i in range(6)]
    for j in range(6)]

    for i in range(6):
      self.solver.add(z3.Distinct(self.cells[i]))
    for j in range(6):
      self.solver.add(z3.Distinct([row[j] for row in self.cells]))

    for i in [0,2,4]:
      for j in [0,3]:
         self.solver.add(z3.Distinct([c for row in self.cells[i:i+2] for c in row[j:j+3]]))

    if self.solver.check() == z3.sat:
      self.model = self.solver.model()
      self.print_answer()
    else:
      print("failed to solve")

_ = None
minisudoku = MiniSudoku([
  [_, _, _, 4, _, _],
  [_, _, 4, 1, 2, _],
  [_, _, 6, 5, 4, _],
  [_, 5, 2, 3, _, _],
  [_, 2, 3, 6, _, _],
  [_, _, 1, _, _, _],
])

minisudoku.solve()

