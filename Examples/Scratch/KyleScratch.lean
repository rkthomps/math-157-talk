


import Examples.Imp.Eval
import Examples.Imp.Semantics

namespace Imp

theorem eval_bigstep_true (s : Stmt) (st st' : State) :
  BigStep st s st' ↔ ∃ fuel, s.eval st fuel = some st' := by
  sorry


def count_up := [imp|
  sum := 0;
  i := 0;
  while (i <= n) {
    sum := sum + i;
    i := i + 1
  }
]




def count_down := [imp|
  sum := 0;
  i := n;
  while (0 <= i) {
    sum := sum + i;
    i := i - 1
  }
]



#eval (count_up.eval (State.empty.update "n" 5)).get! "sum"


inductive EvaluatesTo : State → Stmt → State → Prop where


end Imp
