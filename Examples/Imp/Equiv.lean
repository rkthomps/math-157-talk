
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
  let i := st "i"
  if i == 0 then
    st "sum" == 0 ∧ i >= 0
  else
    (st "sum" == (i * (i - 1)) / 2) ∧ i > 0


def count_up_inv := [aimp|
  sum := 0;
  i := 0;
  while (i <= n) inv(inv_up){
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


theorem count_up_meets_spec (initial : State):
  Valid (fun st => st = initial) count_up_inv.toStmt (fun st => st.equivOn ["sum"] (count_spec initial)) := by
  apply vc'_sound
  simp [vc', Assertion.entails, count_up_inv, Assertion.subst, aeval, State.update, count_spec, State.equivOn, inv_up]
  constructor
  · intros st vc
    simp [beval, aeval]
    intros h
    split
    · contradiction
  · sorry




end Count


end Imp
