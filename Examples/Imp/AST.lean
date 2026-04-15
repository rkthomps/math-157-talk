namespace Imp

/-- State maps variable names to integer values. -/
abbrev State := String → Int

def State.empty : State := fun _ => 0

def State.update (s : State) (x : String) (v : Int) : State :=
  fun y => if y == x then v else s y

/-- Arithmetic expressions. -/
inductive AExp where
  | lit (n : Int)
  | var (x : String)
  | add (a₁ a₂ : AExp)
  | mul (a₁ a₂ : AExp)
  | sub (a₁ a₂ : AExp)
  deriving Repr, BEq

/-- Boolean expressions. -/
inductive BExp where
  | true
  | false
  | eq (a₁ a₂ : AExp)
  | le (a₁ a₂ : AExp)
  | not (b : BExp)
  | and (b₁ b₂ : BExp)
  deriving Repr, BEq

/-- Statements. -/
inductive Stmt where
  | skip
  | assign (x : String) (a : AExp)
  | seq (s₁ s₂ : Stmt)
  | ifThenElse (b : BExp) (s₁ s₂ : Stmt)
  | while (b : BExp) (body : Stmt)
  deriving Repr, BEq

end Imp
