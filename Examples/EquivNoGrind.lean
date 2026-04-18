/-
Equivalence of `count_up` and `count_down` proved directly from the
big-step semantics — no Floyd–Hoare logic, no VC generation, no `grind`.

The point of this file is to show that a direct big-step proof is
possible but painful. Compare with `Examples.Imp.Equiv`, where the
same theorem falls out of `vc'_sound` + a `grind` call.
-/

import Examples.Imp.AST
import Examples.Imp.Syntax
import Examples.Imp.Eval
import Examples.Imp.Semantics

namespace Imp
namespace CountNoGrind

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
theorem tri_step (i : Int) : i * (i - 1) / 2 + i = i * (i + 1) / 2 := by
  have h : i * (i + 1) = i * (i - 1) + i * 2 := by
    have e1 : i * (i + 1) = i * i + i := by rw [Int.mul_add, Int.mul_one]
    have e2 : i * (i - 1) = i * i - i := by rw [Int.mul_sub, Int.mul_one]
    omega
  rw [h, Int.add_mul_ediv_right _ _ (by decide : (2:Int) ≠ 0)]

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
  induction h with
  | «skip» => cases hs
  | assign => cases hs
  | seq => cases hs
  | ifTrue => cases hs
  | ifFalse => cases hs
  | whileFalse b' body' st'' hne =>
      injection hs with hb hbd
      subst hb; subst hbd
      exact hfalse st'' hne
  | whileTrue b' body' s₁ s₂ s₃ hb hbody hwhile _ih₁ ih₂ =>
      injection hs with hbeq hbdeq
      subst hbeq; subst hbdeq
      exact htrue s₁ s₂ s₃ hb hbody hwhile (ih₂ rfl)

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
    intro s hne hn_eq hi_lo hi_hi hsum
    simp only [beval, aeval, decide_eq_true_eq] at hne
    rw [hn_eq] at hne
    have hi_eq : s "i" = n + 1 := by omega
    refine ⟨hn_eq, ?_⟩
    rw [hsum, hi_eq]
    -- Goal: (n+1) * (n+1 - 1) / 2 = n * (n+1) / 2
    have h1 : (n + 1) * (n + 1 - 1) = n * (n + 1) := by
      have hs : (n + 1 - 1 : Int) = n := by omega
      rw [hs, Int.mul_comm]
    rw [h1]
  · -- true branch: body runs; peel off the two assignments
    intro s₁ s₂ s₃ hb hbody _hwhile ih hn_eq hi_lo hi_hi hsum
    simp only [beval, aeval, decide_eq_true_eq] at hb
    rw [hn_eq] at hb
    cases hbody with
    | seq _ _ _ sM _ hb1 hb2 =>
      -- Derive all facts about s₂ in a single sub-proof so that `cases` inside
      -- does not substitute `s₂` away from the outer context.
      have facts : s₂ "n" = s₁ "n"
                 ∧ s₂ "i" = s₁ "i" + 1
                 ∧ s₂ "sum" = s₁ "sum" + s₁ "i" := by
        cases hb1 with
        | assign =>
          cases hb2 with
          | assign =>
            refine ⟨?_, ?_, ?_⟩ <;> simp [State.update, aeval]
      obtain ⟨h2_n, h2_i, h2_sum⟩ := facts
      apply ih
      · rw [h2_n, hn_eq]
      · rw [h2_i]; omega
      · rw [h2_i]; omega
      · rw [h2_sum, h2_i, hsum]
        -- Goal: s₁ "i" * (s₁ "i" - 1) / 2 + s₁ "i"
        --      = (s₁ "i" + 1) * (s₁ "i" + 1 - 1) / 2
        have hs : (s₁ "i" + 1 - 1 : Int) = s₁ "i" := by omega
        rw [hs, Int.mul_comm (s₁ "i" + 1) (s₁ "i")]
        exact tri_step (s₁ "i")

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
    intro s hne hn_eq hi_lo hi_hi hsum
    simp only [beval, aeval, decide_eq_true_eq] at hne
    have hi_eq : s "i" = -1 := by omega
    refine ⟨hn_eq, ?_⟩
    rw [hsum, hi_eq]
    -- Goal: n*(n+1)/2 - (-1) * (-1 + 1) / 2 = n*(n+1)/2
    have h1 : ((-1 : Int)) * ((-1 : Int) + 1) = 0 := by decide
    rw [h1]; simp
  · intro s₁ s₂ s₃ hb hbody _hwhile ih hn_eq hi_lo hi_hi hsum
    simp only [beval, aeval, decide_eq_true_eq] at hb
    cases hbody with
    | seq _ _ _ sM _ hb1 hb2 =>
      have facts : s₂ "n" = s₁ "n"
                 ∧ s₂ "i" = s₁ "i" - 1
                 ∧ s₂ "sum" = s₁ "sum" + s₁ "i" := by
        cases hb1 with
        | assign =>
          cases hb2 with
          | assign =>
            refine ⟨?_, ?_, ?_⟩ <;> simp [State.update, aeval]
      obtain ⟨h2_n, h2_i, h2_sum⟩ := facts
      apply ih
      · rw [h2_n, hn_eq]
      · rw [h2_i]; omega
      · rw [h2_i]; omega
      · rw [h2_sum, h2_i, hsum]
        -- Goal:  n*(n+1)/2 - s₁"i"*(s₁"i"+1)/2 + s₁"i"
        --      = n*(n+1)/2 - (s₁"i" - 1) * ((s₁"i" - 1) + 1) / 2
        have hs : (s₁ "i" - 1 + 1 : Int) = s₁ "i" := by omega
        rw [hs, Int.mul_comm (s₁ "i" - 1) (s₁ "i")]
        have hstep := tri_step (s₁ "i")
        -- hstep: s₁"i" * (s₁"i" - 1) / 2 + s₁"i" = s₁"i" * (s₁"i" + 1) / 2
        omega

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
  cases h with
  | whileFalse _ _ _ hne =>
    exact ⟨hn_eq, hsum⟩
  | whileTrue _ _ _ _ _ hb _ _ =>
    -- guard is `st "i" ≤ st "n"` = `0 ≤ n`, contradicting n < 0
    exfalso
    simp only [beval, aeval, decide_eq_true_eq] at hb
    rw [hi, hn_eq] at hb
    omega

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
  cases h with
  | whileFalse _ _ _ _ =>
    exact ⟨hn_eq, hsum⟩
  | whileTrue _ _ _ _ _ hb _ _ =>
    -- guard is `0 ≤ st "i"` = `0 ≤ n`, contradicting n < 0
    exfalso
    simp only [beval, aeval, decide_eq_true_eq] at hb
    rw [hi] at hb
    omega

-- ============================================================
-- Full program semantics for count_up
-- ============================================================

theorem count_up_end_sum (st st' : State) (h : BigStep st count_up st') :
    st' "sum" = (if st "n" < 0 then 0 else st "n" * (st "n" + 1) / 2) := by
  simp only [count_up] at h
  cases h with
  | seq _ _ _ s1 _ hInit hLoop =>
    -- Extract facts about s1 without letting the sub-cases collapse s1 away.
    have hs1 : s1 "n" = st "n" ∧ s1 "i" = 0 ∧ s1 "sum" = 0 := by
      cases hInit with
      | seq _ _ _ s0 _ hA hB =>
        cases hA with | assign =>
        cases hB with | assign =>
        refine ⟨?_, ?_, ?_⟩ <;> simp [State.update, aeval]
    obtain ⟨hs1_n, hs1_i, hs1_sum⟩ := hs1
    by_cases hn : 0 ≤ st "n"
    · have hres := count_up_loop_pos (st "n") hn s1 st' hLoop
          hs1_n (by rw [hs1_i]; omega) (by rw [hs1_i]; omega)
          (by rw [hs1_sum, hs1_i]; decide)
      rw [if_neg (by omega : ¬ st "n" < 0)]
      exact hres.2
    · have hn' : st "n" < 0 := by omega
      have hres := count_up_loop_neg (st "n") hn' s1 st' hLoop hs1_n hs1_i hs1_sum
      rw [if_pos hn']
      exact hres.2

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
        cases hA with | assign =>
        cases hB with | assign =>
        refine ⟨?_, ?_, ?_⟩ <;> simp [State.update, aeval]
    obtain ⟨hs1_n, hs1_i, hs1_sum⟩ := hs1
    by_cases hn : 0 ≤ st "n"
    · have hres := count_down_loop_pos (st "n") hn s1 st' hLoop
          hs1_n (by rw [hs1_i]; omega) (by rw [hs1_i]; omega)
          (by rw [hs1_sum, hs1_i]; omega)
      rw [if_neg (by omega : ¬ st "n" < 0)]
      exact hres.2
    · have hn' : st "n" < 0 := by omega
      have hres := count_down_loop_neg (st "n") hn' s1 st' hLoop hs1_n hs1_i hs1_sum
      rw [if_pos hn']
      exact hres.2

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
  rw [count_up_end_sum st st₁ h₁, count_down_end_sum st st₂ h₂]

end CountNoGrind
end Imp
