
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


-- Single-step unfolding equations for `Stmt.eval`, proven by `rfl`.
-- These give fine-grained control and avoid the over-eager unfolding that
-- `simp only [Stmt.eval]` would do on a recursive definition.

private theorem eval_zero (s : Stmt) (st : State) : s.eval st 0 = none := rfl

private theorem eval_skip (st : State) (fuel : Nat) :
    (Stmt.skip).eval st (fuel + 1) = some st := rfl

private theorem eval_assign (x : String) (a : AExp) (st : State) (fuel : Nat) :
    (Stmt.assign x a).eval st (fuel + 1) = some (st.update x (aeval a st)) := rfl

private theorem eval_seq (s₁ s₂ : Stmt) (st : State) (fuel : Nat) :
    (Stmt.seq s₁ s₂).eval st (fuel + 1) =
      (s₁.eval st fuel).bind fun st' => s₂.eval st' fuel := rfl

private theorem eval_if (b : BExp) (s₁ s₂ : Stmt) (st : State) (fuel : Nat) :
    (Stmt.ifThenElse b s₁ s₂).eval st (fuel + 1) =
      if beval b st then s₁.eval st fuel else s₂.eval st fuel := rfl

private theorem eval_while (b : BExp) (body : Stmt) (st : State) (fuel : Nat) :
    (Stmt.while b body).eval st (fuel + 1) =
      if beval b st then
        (body.eval st fuel).bind fun st' => (Stmt.while b body).eval st' fuel
      else some st := rfl

/-- Adding one unit of fuel preserves a successful evaluation. -/
theorem Stmt.eval_mono_succ :
    ∀ (fuel : Nat) {s : Stmt} {st st' : State},
    s.eval st fuel = some st' → s.eval st (fuel + 1) = some st' := by
  intro fuel
  induction fuel with
  | zero =>
    intro s st st' h
    rw [eval_zero] at h
    nomatch h
  | succ n ih =>
    intro s st st' h
    cases s with
    | «skip» =>
      rw [eval_skip] at h ⊢; exact h
    | assign x a =>
      rw [eval_assign] at h ⊢; exact h
    | seq s₁ s₂ =>
      rw [eval_seq] at h ⊢
      cases h₁ : s₁.eval st n with
      | none => rw [h₁, Option.bind_none] at h; nomatch h
      | some st'' =>
        rw [h₁, Option.bind_some] at h
        rw [ih h₁, Option.bind_some]
        exact ih h
    | ifThenElse b s₁ s₂ =>
      rw [eval_if] at h ⊢
      by_cases hb : beval b st = Bool.true
      · rw [if_pos hb] at h ⊢; exact ih h
      · rw [if_neg hb] at h ⊢; exact ih h
    | «while» b body =>
      rw [eval_while] at h ⊢
      by_cases hb : beval b st = Bool.true
      · rw [if_pos hb] at h ⊢
        cases h₁ : body.eval st n with
        | none => rw [h₁, Option.bind_none] at h; nomatch h
        | some st'' =>
          rw [h₁, Option.bind_some] at h
          rw [ih h₁, Option.bind_some]
          exact ih h
      · rw [if_neg hb] at h ⊢; exact h

/-- Increasing fuel preserves a successful evaluation. -/
theorem Stmt.eval_mono {s : Stmt} {st st' : State} :
    ∀ {fuel fuel' : Nat}, fuel ≤ fuel' →
    s.eval st fuel = some st' → s.eval st fuel' = some st' := by
  intro fuel fuel' hle
  induction hle with
  | refl => intro h; exact h
  | step _ ih => intro h; exact Stmt.eval_mono_succ _ (ih h)

/-- Every big-step derivation is witnessed by some bounded evaluation. -/
theorem bigstep_to_eval {st : State} {s : Stmt} {st' : State} :
    BigStep st s st' → ∃ fuel, s.eval st fuel = some st' := by
  intro h
  induction h with
  | «skip» st => exact ⟨1, rfl⟩
  | assign x a st => exact ⟨1, rfl⟩
  | seq s₁ s₂ st st' st'' _ _ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨f₁ + f₂ + 1, ?_⟩
    have e₁ : s₁.eval st (f₁ + f₂) = some st' :=
      Stmt.eval_mono (Nat.le_add_right f₁ f₂) hf₁
    have e₂ : s₂.eval st' (f₁ + f₂) = some st'' :=
      Stmt.eval_mono (Nat.le_add_left f₂ f₁) hf₂
    rw [eval_seq, e₁, Option.bind_some]
    exact e₂
  | ifTrue b s₁ s₂ st st' hb _ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [eval_if, if_pos hb]
    exact hf
  | ifFalse b s₁ s₂ st st' hb _ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [eval_if, if_neg hb]
    exact hf
  | whileFalse b body st hb =>
    refine ⟨1, ?_⟩
    rw [eval_while, if_neg hb]
  | whileTrue b body st st' st'' hb _ _ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨f₁ + f₂ + 1, ?_⟩
    have e₁ : body.eval st (f₁ + f₂) = some st' :=
      Stmt.eval_mono (Nat.le_add_right f₁ f₂) hf₁
    have e₂ : (Stmt.while b body).eval st' (f₁ + f₂) = some st'' :=
      Stmt.eval_mono (Nat.le_add_left f₂ f₁) hf₂
    rw [eval_while, if_pos hb, e₁, Option.bind_some]
    exact e₂

/-- Every successful bounded evaluation yields a big-step derivation. -/
theorem eval_to_bigstep :
    ∀ (fuel : Nat) {s : Stmt} {st st' : State},
    s.eval st fuel = some st' → BigStep st s st' := by
  intro fuel
  induction fuel with
  | zero =>
    intro s st st' h
    rw [eval_zero] at h
    nomatch h
  | succ n ih =>
    intro s st st' h
    cases s with
    | «skip» =>
      rw [eval_skip] at h
      cases h
      exact BigStep.skip _
    | assign x a =>
      rw [eval_assign] at h
      cases h
      exact BigStep.assign _ _ _
    | seq s₁ s₂ =>
      rw [eval_seq] at h
      cases h₁ : s₁.eval st n with
      | none => rw [h₁, Option.bind_none] at h; nomatch h
      | some st'' =>
        rw [h₁, Option.bind_some] at h
        exact BigStep.seq _ _ _ _ _ (ih h₁) (ih h)
    | ifThenElse b s₁ s₂ =>
      rw [eval_if] at h
      by_cases hb : beval b st = Bool.true
      · rw [if_pos hb] at h
        exact BigStep.ifTrue _ _ _ _ _ hb (ih h)
      · rw [if_neg hb] at h
        exact BigStep.ifFalse _ _ _ _ _ hb (ih h)
    | «while» b body =>
      rw [eval_while] at h
      by_cases hb : beval b st = Bool.true
      · rw [if_pos hb] at h
        cases h₁ : body.eval st n with
        | none => rw [h₁, Option.bind_none] at h; nomatch h
        | some st'' =>
          rw [h₁, Option.bind_some] at h
          exact BigStep.whileTrue _ _ _ _ _ hb (ih h₁) (ih h)
      · rw [if_neg hb] at h
        cases h
        exact BigStep.whileFalse _ _ _ hb

/-- Big-step semantics agrees with bounded evaluation. -/
theorem eval_bigstep_true (s : Stmt) (st st' : State) :
    BigStep st s st' ↔ ∃ fuel, s.eval st fuel = some st' := by
  constructor
  · exact bigstep_to_eval
  · rintro ⟨fuel, h⟩
    exact eval_to_bigstep fuel h

end Imp
