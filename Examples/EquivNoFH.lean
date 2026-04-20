/-
Equivalence of `count_up` and `count_down` proved directly from the
big-step semantics — no Floyd–Hoare logic, no VC generation.

The point of this file is to show that a direct big-step proof is
possible without Floyd–Hoare logic. `grind` is still used to shorten
proofs. Compare with `Examples.Imp.Equiv`, where the same theorem
falls out of `vc'_sound` + a `grind` call.
-/

import Examples.Imp.AST
import Examples.Imp.Syntax
import Examples.Imp.Eval
import Examples.Imp.Semantics

namespace Imp
namespace CountNoFH

attribute [local grind unfold] State.update beval aeval

-- ============================================================
-- The two programs
-- ============================================================

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

-- ============================================================
-- Arithmetic helpers
-- ============================================================

/-- The triangle-number step law: `T(i) + i = T(i+1)` where `T(i) = i*(i-1)/2`. -/
@[grind =]
theorem tri_step (i : Int) : i * (i - 1) / 2 + i = i * (i + 1) / 2 := by grind

/-- `tri_step` restated so the RHS matches the shape `(i+1) * ((i+1) - 1) / 2`
    produced when the invariant `sum = i * (i - 1) / 2` is specialised at the
    post-increment value `i + 1`. -/
@[grind =]
theorem tri_step_post (i : Int) :
    i * (i - 1) / 2 + i = (i + 1) * ((i + 1) - 1) / 2 := by grind

-- ============================================================
-- A reusable induction principle on `while` derivations
-- ============================================================

/--
Principle of induction on the big-step derivation of a `while` loop.
Any predicate `P` closed under the two while cases holds for every pair
of states related by the loop.
-/
theorem while_ind (b : BExp) (body : Stmt) (P : State → State → Prop)
    (hfalse : ∀ st, ¬ beval b st → P st st)
    (htrue : ∀ st₁ st₂ st₃,
        beval b st₁ →
        BigStep st₁ body st₂ →
        BigStep st₂ (.while b body) st₃ →
        P st₂ st₃ →
        P st₁ st₃)
    {st st' : State} (h : BigStep st (.while b body) st') : P st st' := by
  generalize hs : Stmt.while b body = s at h
  induction h <;> grind

-- ============================================================
-- Loop lemma for count_up (0 ≤ n case)
-- ============================================================

/-- Loop invariant preservation for count_up's while loop when `0 ≤ n`. -/
theorem count_up_loop_pos (n : Int) (_hn : 0 ≤ n) :
    ∀ (st st' : State),
    BigStep st
      (.while (.le (.var "i") (.var "n"))
        (.seq (.assign "sum" (.add (.var "sum") (.var "i")))
              (.assign "i" (.add (.var "i") (.lit 1)))))
      st' →
    st "n" = n →
    0 ≤ st "i" → st "i" ≤ n + 1 →
    st "sum" = st "i" * (st "i" - 1) / 2 →
    st' "n" = n ∧ st' "sum" = n * (n + 1) / 2 := by
  intro st st' h
  refine while_ind _ _
    (fun s s' =>
      s "n" = n → 0 ≤ s "i" → s "i" ≤ n + 1 →
      s "sum" = s "i" * (s "i" - 1) / 2 →
      s' "n" = n ∧ s' "sum" = n * (n + 1) / 2)
    ?hF ?hT h
  · -- false branch: guard fails, so st "i" > n, combined with ≤ n+1 gives = n+1
    grind [Int.mul_comm]
  · -- true branch: body runs; peel off the two assignments
    intro s₁ s₂ s₃ hb hbody _hwhile ih hn_eq hi_lo hi_hi hsum
    cases hbody with
    | seq _ _ _ sM _ hb1 hb2 =>
      have facts : s₂ "n" = s₁ "n"
                 ∧ s₂ "i" = s₁ "i" + 1
                 ∧ s₂ "sum" = s₁ "sum" + s₁ "i" := by
        cases hb1 with | assign => cases hb2 with | assign => grind
      obtain ⟨h2_n, h2_i, h2_sum⟩ := facts
      apply ih <;> first | grind | (rw [h2_sum, h2_i, hsum]; grind)

-- ============================================================
-- Loop lemma for count_down (0 ≤ n case)
-- ============================================================

theorem count_down_loop_pos (n : Int) (_hn : 0 ≤ n) :
    ∀ (st st' : State),
    BigStep st
      (.while (.le (.lit 0) (.var "i"))
        (.seq (.assign "sum" (.add (.var "sum") (.var "i")))
              (.assign "i" (.sub (.var "i") (.lit 1)))))
      st' →
    st "n" = n →
    -1 ≤ st "i" → st "i" ≤ n →
    st "sum" = n * (n + 1) / 2 - st "i" * (st "i" + 1) / 2 →
    st' "n" = n ∧ st' "sum" = n * (n + 1) / 2 := by
  intro st st' h
  refine while_ind _ _
    (fun s s' =>
      s "n" = n → -1 ≤ s "i" → s "i" ≤ n →
      s "sum" = n * (n + 1) / 2 - s "i" * (s "i" + 1) / 2 →
      s' "n" = n ∧ s' "sum" = n * (n + 1) / 2)
    ?hF ?hT h
  · -- false branch: guard fails, so s "i" < 0, combined with ≥ -1 gives = -1
    grind
  · intro s₁ s₂ s₃ hb hbody _hwhile ih hn_eq hi_lo hi_hi hsum
    cases hbody with
    | seq _ _ _ sM _ hb1 hb2 =>
      have facts : s₂ "n" = s₁ "n"
                 ∧ s₂ "i" = s₁ "i" - 1
                 ∧ s₂ "sum" = s₁ "sum" + s₁ "i" := by
        cases hb1 with | assign => cases hb2 with | assign => grind
      obtain ⟨h2_n, h2_i, h2_sum⟩ := facts
      apply ih <;> first | grind | (rw [h2_sum, h2_i, hsum]; grind)

-- ============================================================
-- Loop lemma for count_up (n < 0 case)
-- ============================================================

theorem count_up_loop_neg (n : Int) (hn : n < 0) :
    ∀ (st st' : State),
    BigStep st
      (.while (.le (.var "i") (.var "n"))
        (.seq (.assign "sum" (.add (.var "sum") (.var "i")))
              (.assign "i" (.add (.var "i") (.lit 1)))))
      st' →
    st "n" = n → st "i" = 0 → st "sum" = 0 →
    st' "n" = n ∧ st' "sum" = 0 := by
  intro st st' h hn_eq hi hsum
  cases h <;> grind

-- ============================================================
-- Loop lemma for count_down (n < 0 case)
-- ============================================================

theorem count_down_loop_neg (n : Int) (hn : n < 0) :
    ∀ (st st' : State),
    BigStep st
      (.while (.le (.lit 0) (.var "i"))
        (.seq (.assign "sum" (.add (.var "sum") (.var "i")))
              (.assign "i" (.sub (.var "i") (.lit 1)))))
      st' →
    st "n" = n → st "i" = n → st "sum" = 0 →
    st' "n" = n ∧ st' "sum" = 0 := by
  intro st st' h hn_eq hi hsum
  cases h <;> grind

-- ============================================================
-- Full program semantics for count_up
-- ============================================================

theorem count_up_end_sum (st st' : State) (h : BigStep st count_up st') :
    st' "sum" = (if st "n" < 0 then 0 else st "n" * (st "n" + 1) / 2) := by
  simp only [count_up] at h
  cases h with
  | seq _ _ _ s1 _ hInit hLoop =>
    have hs1 : s1 "n" = st "n" ∧ s1 "i" = 0 ∧ s1 "sum" = 0 := by
      cases hInit with
      | seq _ _ _ s0 _ hA hB =>
        cases hA with | assign => cases hB with | assign => grind
    by_cases hn : 0 ≤ st "n"
    · grind [count_up_loop_pos]
    · grind [count_up_loop_neg]

-- ============================================================
-- Full program semantics for count_down
-- ============================================================

theorem count_down_end_sum (st st' : State) (h : BigStep st count_down st') :
    st' "sum" = (if st "n" < 0 then 0 else st "n" * (st "n" + 1) / 2) := by
  simp only [count_down] at h
  cases h with
  | seq _ _ _ s1 _ hInit hLoop =>
    have hs1 : s1 "n" = st "n" ∧ s1 "i" = st "n" ∧ s1 "sum" = 0 := by
      cases hInit with
      | seq _ _ _ s0 _ hA hB =>
        cases hA with | assign => cases hB with | assign => grind
    by_cases hn : 0 ≤ st "n"
    · grind [count_down_loop_pos]
    · grind [count_down_loop_neg]

-- ============================================================
-- Equivalence
-- ============================================================

/-- Direct big-step equivalence of `count_up` and `count_down` on `sum`,
    without VC generation or Floyd–Hoare logic. -/
theorem count_up_down_equiv_sum
    (st st₁ st₂ : State)
    (h₁ : BigStep st count_up st₁)
    (h₂ : BigStep st count_down st₂) :
    st₁ "sum" = st₂ "sum" := by
  grind [count_up_end_sum, count_down_end_sum]

end CountNoFH
end Imp
