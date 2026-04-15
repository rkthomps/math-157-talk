import Examples.Imp.AST
import Examples.Imp.Eval
import Examples.Imp.Semantics

namespace Imp

/-- An assertion is a predicate on states. -/
def Assertion := State → Prop

/-- Assertion entailment. -/
def Assertion.entails (P Q : Assertion) : Prop := ∀ st, P st → Q st

/-- Substitution: `P [x := a]` is the assertion that holds when P holds
    after updating x to the value of a. -/
def Assertion.subst (P : Assertion) (x : String) (a : AExp) : Assertion :=
  fun st => P (st.update x (aeval a st))

/-- Floyd-Hoare logic. `FH P s Q` is the Hoare triple {P} s {Q}. -/
inductive FH : Assertion → Stmt → Assertion → Prop where
  | skip (P : Assertion) :
      FH P .skip P

  | assign (P : Assertion) (x : String) (a : AExp) :
      FH (P.subst x a) (.assign x a) P

  | seq (P Q R : Assertion) (s₁ s₂ : Stmt) :
      FH P s₁ Q →
      FH Q s₂ R →
      FH P (.seq s₁ s₂) R

  | ifThenElse (P Q : Assertion) (b : BExp) (s₁ s₂ : Stmt) :
      FH (fun st => P st ∧ beval b st) s₁ Q →
      FH (fun st => P st ∧ ¬beval b st) s₂ Q →
      FH P (.ifThenElse b s₁ s₂) Q

  | while (P : Assertion) (b : BExp) (body : Stmt) :
      FH (fun st => P st ∧ beval b st) body P →
      FH P (.while b body) (fun st => P st ∧ ¬beval b st)

  | consL (P' P : Assertion) (Q : Assertion) (s : Stmt) :
      FH P s Q →
      P'.entails P →
      FH P' s Q

  | consR (P Q Q' : Assertion) (s : Stmt) :
      FH P s Q →
      Q.entails Q' →
      FH P s Q'



/-- Annotated commands: `Stmt` extended with a loop invariant on `while`. -/
inductive AStmt where
  | skip
  | assign (x : String) (a : AExp)
  | seq    (s₁ s₂ : AStmt)
  | ifThenElse (b : BExp) (s₁ s₂ : AStmt)
  | while  (inv : Assertion) (b : BExp) (body : AStmt)

/-- Erase annotations, recovering the underlying `Stmt`. -/
def AStmt.toStmt : AStmt → Stmt
  | .skip                  => .skip
  | .assign x a            => .assign x a
  | .seq s₁ s₂             => .seq s₁.toStmt s₂.toStmt
  | .ifThenElse b s₁ s₂    => .ifThenElse b s₁.toStmt s₂.toStmt
  | .while _ b body        => .while b body.toStmt

/-- Weakest precondition of an annotated statement with respect to postcondition `q`.
    For `while`, the invariant is taken as the precondition. -/
@[simp]
def pre (q : Assertion) : AStmt → Assertion
  | .skip              => q
  | .assign x a        => q.subst x a
  | .seq s₁ s₂        => pre (pre q s₂) s₁
  | .ifThenElse b s₁ s₂ => fun st => if beval b st then pre q s₁ st else pre q s₂ st
  | .while inv _ _     => inv

end Imp
