
import Examples.Imp.Syntax
import Examples.Imp.AStmtSyntax
import Examples.Imp.Semantics
import Examples.Imp.Hoare

namespace Imp

abbrev State.equivOn (vars : List String) (s₁ s₂ : State) : Prop :=
  ∀ x ∈ vars, s₁ x = s₂ x

abbrev EquivOn (vars : List String) (s₁ s₂ : Stmt) : Prop :=
  ∀ st st₁' st₂',
    BigStep st s₁ st₁' →
    BigStep st s₂ st₂' →
    st₁'.equivOn vars st₂'

attribute [local grind unfold] AStmt.toStmt
attribute [local grind unfold] State.update beval aeval
attribute [local grind] vc pre
attribute [local grind unfold] Assertion.entails Assertion.subst

@[grind →]
theorem valid_implies_big_step {P Q : Assertion} {st st' : State} {s : Stmt}: Valid P s Q → BigStep st s st' → P st → Q st' := by
  grind [Valid]


namespace Swap

def swap1 := [aimp|
  tmp := x;
  x := y;
  y := tmp
]


def swap2 := [aimp|
  x := x + y;
  y := x - y;
  x := x - y
]


def swap_spec (st : State) : State :=
  let x := st "x"
  let y := st "y"
  (st.update "x" y).update "y" x


theorem swap1_meets_spec (initial : State):
  Valid (fun st => st = initial) swap1.toStmt (fun st => st.equivOn ["x", "y"] (swap_spec initial)) := by
  apply vc'_sound
  simp [swap1, swap_spec]
  grind


theorem swap2_meets_spec (initial : State):
  Valid (fun st => st = initial) swap2.toStmt (fun st => st.equivOn ["x", "y"] (swap_spec initial)) := by
  apply vc'_sound
  simp [swap2, swap_spec]
  grind


theorem swap1_swap2_equiv : EquivOn ["x", "y"] swap1.toStmt swap2.toStmt := by
  simp [EquivOn]
  intros st st₁' st₂' H1 H2
  grind [swap1_meets_spec st, swap2_meets_spec st]


end Swap


namespace Count



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

def inv_up (k : Int) : Assertion := fun st =>
  let n := st "n"
  let i := st "i"
  let sum := st "sum"
  let case1 := 0 = i ∧ n < 0 ∧ sum == 0
  let case2 := 0 ≤ i ∧ i ≤ n + 1 ∧ 0 ≤ n ∧ sum == (i * (i - 1)) / 2
  n = k ∧ (case1 ∨ case2)


def count_up_inv (k : Int) := [aimp|
  sum := 0;
  i := 0;
  while (i <= n) inv(inv_up k) {
    sum := sum + i;
    i := i + 1
  }
]

@[grind =]
theorem count_up_inv_stmt {k : Int} : (count_up_inv k).toStmt = count_up := by
  simp [count_up, count_up_inv, AStmt.toStmt]


def count_end_state (k : Int) : Assertion := fun st =>
  let n := st "n"
  let sum := st "sum"
  if n < 0 then
    sum == 0 ∧ n = k
  else
    sum == (n * (n + 1)) / 2 ∧ n = k



@[grind →]
theorem squish_up (a b : Int): a ≤ b + 1 ∧ b < a → a = b + 1 := by omega


theorem count_up_to_end_state {k : Int} : Valid (fun st => st "n" = k) (count_up_inv k).toStmt (count_end_state k) := by
  apply vc'_sound
  simp [count_up_inv, count_end_state]
  grind [inv_up, Int.mul_comm]


@[grind →]
theorem count_up_end_state' (st st' : State) :
  BigStep st count_up st' → count_end_state (st "n") st' := by
  grind [count_up_to_end_state (k := st "n")]


def inv_down (k : Int) : Assertion := fun st =>
  let n := st "n"
  let i := st "i"
  let sum := st "sum"
  let case1 := n < 0 ∧ i = n ∧ sum == 0
  let case2 := 0 ≤ n ∧ -1 ≤ i ∧ i ≤ n ∧ sum == (n * (n + 1)) / 2 - (i * (i + 1)) / 2
  n = k ∧ (case1 ∨ case2)

def count_down_inv (k : Int) := [aimp|
  sum := 0;
  i := n;
  while (0 <= i) inv(inv_down k) {
    sum := sum + i;
    i := i - 1
  }
]

@[grind =]
theorem count_down_inv_stmt {k : Int} : (count_down_inv k).toStmt = count_down := by
  simp [count_down, count_down_inv, AStmt.toStmt]

@[grind →]
theorem squish_down (a b : Int) : a < (b + 1) → b ≤ a → a = b := by omega


theorem count_down_to_end_state {k : Int} : Valid (fun st => st "n" = k) (count_down_inv k).toStmt (count_end_state k):= by
  apply vc'_sound
  simp [count_down_inv, count_end_state]
  grind [inv_down]

@[grind →]
theorem count_down_end_state' (st st' : State) :
  BigStep st count_down st' → count_end_state (st "n") st' := by
  grind [count_down_to_end_state (k := st "n")]


theorem count_up_down_equiv : EquivOn ["sum"] count_up count_down := by
  grind [
    count_end_state,
    count_up_end_state',
    count_down_end_state'
  ]


end Count
end Imp
