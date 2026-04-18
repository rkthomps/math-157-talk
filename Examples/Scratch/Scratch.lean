


import Examples.Imp.Eval
import Examples.Imp.Semantics

namespace Imp

theorem eval_bigstep_true (s : Stmt) (st st' : State) :
  BigStep st s st' ↔ ∃ fuel, s.eval st fuel = some st' := by
  sorry






end Imp
