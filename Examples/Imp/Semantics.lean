
import Examples.Imp.AST
import Examples.Imp.Syntax
import Examples.Imp.Eval

namespace Imp

inductive BigStep : State → Stmt → State → Prop where
  | skip (st : State) :
      BigStep st .skip st

  | assign (x : String) (a : AExp) (st : State) :
      BigStep st (.assign x a) (st.update x (aeval a st))

  | seq (s₁ s₂ : Stmt) (st st' st'' : State) :
      BigStep st s₁ st' →
      BigStep st' s₂ st'' →
      BigStep st (.seq s₁ s₂) st''

  | ifTrue (b : BExp) (s₁ s₂ : Stmt) (st st' : State) :
      beval b st →
      BigStep st s₁ st' →
      BigStep st (.ifThenElse b s₁ s₂) st'

  | ifFalse (b : BExp) (s₁ s₂ : Stmt) (st st' : State) :
      ¬ beval b st →
      BigStep st s₂ st' →
      BigStep st (.ifThenElse b s₁ s₂) st'

  | whileFalse (b : BExp) (body : Stmt) (st : State) :
      ¬ beval b st →
      BigStep st (.while b body) st

  | whileTrue (b : BExp) (body : Stmt) (st st' st'' : State) :
      beval b st →
      BigStep st body st' →
      BigStep st' (.while b body) st'' →
      BigStep st (.while b body) st''


end Imp
