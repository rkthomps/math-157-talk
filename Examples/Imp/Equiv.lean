
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
  simp [vc', Assertion.entails, swap1, Assertion.subst, aeval, State.update, swap_spec, State.equivOn]

theorem swap2_meets_spec (initial : State):
  Valid (fun st => st = initial) swap2.toStmt (fun st => st.equivOn ["x", "y"] (swap_spec initial)) := by
  apply vc'_sound
  simp [vc', Assertion.entails, swap2, Assertion.subst, aeval, State.update, swap_spec, State.equivOn]
  omega


theorem swap1_swap2_equiv : EquivOn ["x", "y"] swap1.toStmt swap2.toStmt := by
  simp [EquivOn]
  intros st st₁' st₂' H1 H2
  have st1 : st₁'.equivOn ["x", "y"] (swap_spec st) := by
    apply (swap1_meets_spec st) st st₁' (by simp) H1
  have st2 : st₂'.equivOn ["x", "y"] (swap_spec st) := by
    apply (swap2_meets_spec st) st st₂' (by simp) H2
  grind

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

def inv_up : Assertion := fun st =>
  let n := st "n"
  let i := st "i"
  let sum := st "sum"
  let case1 := 0 = i ∧ n < 0 ∧ sum == 0
  let case2 := 0 ≤ i ∧ i ≤ n + 1 ∧ 0 ≤ n ∧ sum == (i * (i - 1)) / 2
  case1 ∨ case2



def count_up_inv := [aimp|
  sum := 0;
  i := 0;
  while (i <= n) inv(inv_up) {
    sum := sum + i;
    i := i + 1
  }
]

def count_spec (initial : State) : State :=
  let n := initial "n"
  if n < 0 then
    initial.update "sum" 0
  else
    initial.update "sum" ((n * (n + 1)) / 2)


def count_end_state : Assertion := fun st =>
  let n := st "n"
  let sum := st "sum"
  if n < 0 then
    sum == 0
  else
    sum == (n * (n + 1)) / 2


theorem count_up_to_end_state : Valid (fun _ => True) count_up_inv.toStmt count_end_state := by
  apply vc'_sound
  simp [vc', Assertion.entails, count_up_inv, Assertion.subst, aeval, State.update, count_end_state]
  simp [inv_up, beval, aeval, State.update]
  constructor
  · constructor
    · intros st h1 h2
      grind
    · intros s h1 h2
      cases h1
      · simp_all
      · have : s "n" >= 0 := by omega
        split
        · omega
        · have : s "i" = s "n" + 1 := by omega
          simp_all
          grind
  · omega



def inv_down: Assertion := fun st =>
  let n := st "n"
  let i := st "i"
  let sum := st "sum"
  let case1 := n < 0 ∧ i = n ∧ sum == 0
  let case2 := 0 ≤ n ∧ -1 ≤ i ∧ i ≤ n ∧ sum == (n * (n + 1)) / 2 - (i * (i + 1)) / 2
  case1 ∨ case2

def count_down_inv := [aimp|
  sum := 0;
  i := n;
  while (0 <= i) inv(inv_down) {
    sum := sum + i;
    i := i - 1
  }
]

theorem count_down_to_end_state : Valid (fun _ => True) count_down_inv.toStmt count_end_state := by
  apply vc'_sound
  simp [vc', Assertion.entails, count_down_inv, Assertion.subst, aeval, State.update, count_end_state]
  simp [inv_down, beval, aeval, State.update]
  constructor
  · constructor
    · intros st h1 h2
      grind
    · intros s h1 h2
      cases h1
      · simp_all
      · have : s "n" >= 0 := by omega
        split
        · omega
        · have : s "i" = -1 := by omega
          simp_all
  · omega


def inv_n_eq (k : Int) : Assertion := fun st => st "n" = k

def count_up_n_inv (k : Int) := [aimp|
  sum := 0;
  i := 0;
  while (i <= n) inv(inv_n_eq k) {
    sum := sum + i;
    i := i + 1
  }
]

def count_down_n_inv (k : Int) := [aimp|
  sum := 0;
  i := n;
  while (0 <= i) inv(inv_n_eq k) {
    sum := sum + i;
    i := i - 1
  }
]

theorem count_up_preserves_n (k : Int) :
    Valid (fun st => st "n" = k) count_up_inv.toStmt (fun st' => st' "n" = k) := by
  show Valid (fun st => st "n" = k) (count_up_n_inv k).toStmt (inv_n_eq k)
  apply vc'_sound
  simp [vc', count_up_n_inv, vc, inv_n_eq, Assertion.subst, aeval, State.update,
        beval, pre, Assertion.entails]
  constructor <;> intro st h _ <;> exact h

theorem count_down_preserves_n (k : Int) :
    Valid (fun st => st "n" = k) count_down_inv.toStmt (fun st' => st' "n" = k) := by
  show Valid (fun st => st "n" = k) (count_down_n_inv k).toStmt (inv_n_eq k)
  apply vc'_sound
  simp [vc', count_down_n_inv, vc, inv_n_eq, Assertion.subst, aeval, State.update,
        beval, pre, Assertion.entails]
  constructor <;> intro st h _ <;> exact h

theorem count_up_down_equiv : EquivOn ["sum"] count_up_inv.toStmt count_down_inv.toStmt := by
  simp [EquivOn, State.equivOn]
  intros st st₁' st₂' H1 H2
  have ce1 := count_up_to_end_state st st₁' trivial H1
  have ce2 := count_down_to_end_state st st₂' trivial H2
  have hn1 : st₁' "n" = st "n" := count_up_preserves_n (st "n") st st₁' rfl H1
  have hn2 : st₂' "n" = st "n" := count_down_preserves_n (st "n") st st₂' rfl H2
  simp only [count_end_state] at ce1 ce2
  rw [hn1] at ce1
  rw [hn2] at ce2
  split at ce1 <;> simp_all <;> omega



end Count


end Imp
