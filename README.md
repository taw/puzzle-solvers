Unfortunately Z3 is not available for Ruby or even Python 3,
so I decided to do some exercises to learn how to use Z3 with Python 2.x.

In other words - use Python 2.x to run these.

To get z3 library, run this or equivalent:

    $ brew install z3

### Solver status

Unfortunately some solvers don't fully follow rules of puzzles they try to solve,
if rules were rather difficult to implement.

Complete:
* bridges
* light up
* minisudoku
* nonogram: gets bad solution anyway, as example puzzle was ambiguous
* selfref
* sudoku
* verbal arithmetic

Incomplete:
* clogic: no three same rule missing, gets correct solution anyway
* letter connections: phantom loops possible; rarely problem in practice
* slitherlink: all connected rule missing
* trees: 1-1 tree-camp mapping missing

Broken:
* nurikabe: my approach is probably not going to work

### Ruby version

Solvers in the repository have Ruby versions available at https://github.com/taw/z3/tree/master/examples
