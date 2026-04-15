import Examples.Imp.AST

namespace Imp

/-- Evaluate an arithmetic expression in a given state. -/
def aeval (a : AExp) (st : State) : Int :=
  match a with
  | .lit n => n
  | .var x => st x
  | .add a₁ a₂ => aeval a₁ st + aeval a₂ st
  | .mul a₁ a₂ => aeval a₁ st * aeval a₂ st
  | .sub a₁ a₂ => aeval a₁ st - aeval a₂ st

/-- Evaluate a boolean expression in a given state. -/
def beval (b : BExp) (st : State) : Bool :=
  match b with
  | .true => Bool.true
  | .false => Bool.false
  | .eq a₁ a₂ => aeval a₁ st == aeval a₂ st
  | .le a₁ a₂ => aeval a₁ st ≤ aeval a₂ st
  | .not b => !(beval b st)
  | .and b₁ b₂ => beval b₁ st && beval b₂ st

/-- Evaluate a statement with bounded fuel. Returns `none` if fuel runs out. -/
def Stmt.eval (s : Stmt) (st : State) (fuel : Nat := 1000) : Option State :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match s with
    | .skip => some st
    | .assign x a => some (st.update x (aeval a st))
    | .seq s₁ s₂ => do
        let st' ← s₁.eval st fuel
        s₂.eval st' fuel
    | .ifThenElse b s₁ s₂ =>
        if beval b st then s₁.eval st fuel else s₂.eval st fuel
    | .while b body =>
        if beval b st then do
          let st' ← body.eval st fuel
          Stmt.eval (.while b body) st' fuel
        else some st

end Imp
