Unfortunately Z3 is not available for Ruby or even Python 3,
so I decided to do some exercises to learn how to use Z3 with Python 2.x.

In other words - use Python 2.x to run these.

To get z3 library, run this or equivalent:

    $ brew install z3

== Solver status ==

Unfortunately some solvers don't fully follow rules of puzzles they try to solve,
if rules were rather difficult to implement.

* bridges: complete
* clogic: incomplete (no three same rule missing, gets correct solution anyway)
* letter connections: incomplete (phantom loops possible; rarely problem in practice)
* light up: complete
* minisudoku: complete
* nonogram: complete (gets bad solution anyway, as example puzzle was ambiguous)
* slitherlink: incomplete (all connected rule missing)
* sudoku: complete
* trees: incomplete (1-1 tree-camp mapping missing)
* verbal arithmetic: complete
