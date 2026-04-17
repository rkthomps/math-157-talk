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



abbrev Valid (P : Assertion) (s : Stmt) (Q : Assertion) : Prop :=
    ∀ st st', P st → (BigStep st s st') → Q st'



theorem loop_inv (inv : Assertion) (st st' : State) (b : BExp) (body : Stmt) :
  Valid (fun st => inv st ∧ beval b st) body (fun st' => inv st') ->
  BigStep st (.while b body) st' →
  inv st →
  inv st' := by
  intros h1 h2 h3
  generalize foo : (Stmt.while b body) = s at h2
  induction h2 <;> grind


theorem loop_exit (st st' : State) (b : BExp) (body : Stmt) :
  BigStep st (.while b body) st' →
  ¬ beval b st' := by
  intros h
  generalize foo : (Stmt.while b body) = s at h
  induction h <;> grind


theorem fh_sound (P : Assertion) (s : Stmt) (Q : Assertion) :
  FH P s Q → Valid P s Q := by
  intros H
  induction H
  case «skip» => simp [Valid]; intros _ _ p b; cases b; assumption
  case assign => simp [Valid]; intros _ _ p b; cases b; assumption
  case seq =>
    simp [Valid]; intros _ _ p b; cases b
    grind
  case ifThenElse =>
    simp [Valid]; intros _ _ p b; cases b <;> grind
  case «while» wp wb wbo wfh ih =>
    simp [Valid]; intros _ _ p b; cases b
    case whileFalse => grind
    case whileTrue st st'' st' hbv hbs1 hbs2 =>
    --   have : BigStep
      constructor
      · have huge_step : BigStep st (.while wb wbo) st'' := by
          exact BigStep.whileTrue wb wbo st st' st'' hbv hbs1 hbs2
        have := loop_inv wp st st'' wb wbo ih huge_step p
        assumption
      · grind [loop_exit]


  case consL cp cp' cq cq' cs hfh hq =>
    simp [Valid] at *; intros st st' hcp hb
    have : cp' st := by simp [Assertion.entails] at hfh; exact hfh st hcp
    exact hq st st' this hb
  case consR cp cq cq' cs hfh hq hv =>
    simp [Valid] at *; intros st st' hcp hb
    have : cq st' := by exact hv st st' hcp hb
    simp [Assertion.entails] at hq; exact hq st' this


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

/-- Verification conditions for an annotated statement with postcondition `q`.
    `vc s q` holds iff the annotation is self-consistent and all side conditions
    needed to close the Hoare triple `{pre q s} s {q}` are discharged. -/
@[simp]
def vc : AStmt → Assertion → Prop
  | .skip,               _ => True
  | .assign _ _,         _ => True
  | .seq s₁ s₂,         q => vc s₁ (pre q s₂) ∧ vc s₂ q
  | .ifThenElse _ s₁ s₂, q => vc s₁ q ∧ vc s₂ q
  | .while inv b body,   q => (∀ st, inv st → beval b st  → pre inv body st) ∧
                               (∀ st, inv st → ¬beval b st → q st) ∧
                               vc body inv

theorem foo_true (b : BExp) (p1 p2 : Assertion) :
  Assertion.entails (fun st => (if beval b st then p1 st else p2 st) ∧ beval b st) p1 := by
  simp [Assertion.entails]; intros st h1 h2; simp_all

theorem foo_false (b : BExp) (p1 p2 : Assertion) :
  Assertion.entails (fun st => (if beval b st then p1 st else p2 st) ∧ ¬ beval b st) p2 := by
  simp [Assertion.entails]; intros st h1 h2; simp_all

--   | ifThenElse (P Q : Assertion) (b : BExp) (s₁ s₂ : Stmt) :
--       FH (fun st => P st ∧ beval b st) s₁ Q →
--       FH (fun st => P st ∧ ¬beval b st) s₂ Q →
--       FH P (.ifThenElse b s₁ s₂) Q

--   | while (P : Assertion) (b : BExp) (body : Stmt) :
--       FH (fun st => P st ∧ beval b st) body P →
--       FH P (.while b body) (fun st => P st ∧ ¬beval b st)

--   | consL (P' P : Assertion) (Q : Assertion) (s : Stmt) :
--       FH P s Q →
--       P'.entails P →
--       FH P' s Q

--   | consR (P Q Q' : Assertion) (s : Stmt) :
--       FH P s Q →
--       Q.entails Q' →
--       FH P s Q'


theorem vc_pre (s : AStmt) (q : Assertion) :
  vc s q → FH (pre q s) (s.toStmt) q := by
  induction s, q using vc.induct
  case case1 => simp [pre]; exact FH.skip _
  case case2 x ae p =>
    intros h; simp [pre];
    exact FH.assign _ x ae
  case case3 s₁ s₂ q ih₁ ih₂ =>
    simp [pre, vc] at *
    intros hpre hq
    have this1 := ih₁ hpre
    have this2 := ih₂ hq
    exact FH.seq _ _ _ s₁.toStmt s₂.toStmt this1 this2
  case case4 b s₁ s₂ q ih₁ ih₂ =>
    simp [pre, vc] at *
    intros hpre hq
    have this1 := ih₁ hpre
    have this2 := ih₂ hq
    have this_then := foo_true b (pre q s₁) (pre q s₂)
    have this_else := foo_false b (pre q s₁) (pre q s₂)
    have this_cons := FH.consL _ _ q s₁.toStmt this1 this_then
    have else_cons := FH.consL _ _ q s₂.toStmt this2 this_else
    exact FH.ifThenElse _ _ _ _ _ this_cons else_cons
  case case5 inv b body q ih =>
    intros h
    simp [vc] at *
    obtain ⟨h1, h2, h3⟩ := h
    have := ih h3
    have enter : Assertion.entails (fun st => inv st ∧ beval b st) (pre q body) := by
      sorry
    have exit : Assertion.entails (fun st => inv st ∧ ¬beval b st) q := by
      sorry
    sorry




theorem vc_sound (s : AStmt) (q : Assertion) :
  vc s q → Valid (pre q s) (s.toStmt) q := by
  intros h
  have : FH (pre q s) (s.toStmt) q := by apply vc_pre; assumption
  exact fh_sound (pre q s) (s.toStmt) q this


def vc' (p : Assertion) (s : AStmt) (q : Assertion) : Prop :=
  vc s q ∧ p.entails (pre q s)


theorem vc'_sound (p : Assertion) (s : AStmt) (q : Assertion) :
  vc' p s q → Valid p (s.toStmt) q := by
  intros h
  simp [vc'] at h
  have : Valid (pre q s) (s.toStmt) q := by apply vc_sound; simp_all
  simp [Valid] at *
  intros st st' hp hs
  have hp' : (pre q s) st := by simp [Assertion.entails] at h; simp_all
  apply this st st'; assumption
  assumption



end Imp
