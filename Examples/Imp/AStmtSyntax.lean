import Examples.Imp.AST
import Examples.Imp.Hoare
import Examples.Imp.Syntax

open Lean in
private def asTerm (s : TSyntax k) : TSyntax `term := ⟨s.raw⟩

namespace Imp

/-! # Annotated IMP Syntax (aimp)

Extends the `imp` syntax to produce `AStmt` values (annotated statements).
The only difference from plain `imp` is that `while` loops carry an inline
loop invariant written as a Lean term in square brackets:

```
[aimp|
  while (x <= 10) inv(fun st => st "x" ≥ 0) {
    x := x + 1
  }
]
```

The invariant must be a Lean term of type `Assertion` (i.e., `State → Prop`).
Arithmetic and boolean sub-expressions reuse the `imp_aexp` / `imp_bexp`
syntax categories defined in `Imp/Syntax.lean`.
-/

-- ============================================================
-- Syntax category
-- ============================================================

declare_syntax_cat aimp_stmt

syntax "skip"                                                           : aimp_stmt
syntax ident " := " imp_aexp                                            : aimp_stmt
syntax:10 aimp_stmt:10 "; " aimp_stmt:11                               : aimp_stmt
syntax "if " imp_bexp " then " aimp_stmt " else " aimp_stmt            : aimp_stmt
syntax "while " imp_bexp " inv(" term ")" " { " aimp_stmt " }"        : aimp_stmt
syntax "(" aimp_stmt ")"                                                : aimp_stmt

-- ============================================================
-- Entry point
-- ============================================================

syntax "[aimp| " aimp_stmt " ]" : term

-- ============================================================
-- Macro rules
-- ============================================================

macro_rules
  | `(aimp_stmt| skip) =>
      `(Imp.AStmt.skip)
  | `(aimp_stmt| $x:ident := $a:imp_aexp) => do
      let a' := asTerm (← `(imp_aexp| $a))
      `(Imp.AStmt.assign $(Lean.quote (toString x.getId)) $a')
  | `(aimp_stmt| $s₁ ; $s₂) => do
      let s₁' := asTerm (← `(aimp_stmt| $s₁))
      let s₂' := asTerm (← `(aimp_stmt| $s₂))
      `(Imp.AStmt.seq $s₁' $s₂')
  | `(aimp_stmt| if $b then $s₁ else $s₂) => do
      let b'  := asTerm (← `(imp_bexp| $b))
      let s₁' := asTerm (← `(aimp_stmt| $s₁))
      let s₂' := asTerm (← `(aimp_stmt| $s₂))
      `(Imp.AStmt.ifThenElse $b' $s₁' $s₂')
  | `(aimp_stmt| while $b inv($inv) { $body }) => do
      let b'    := asTerm (← `(imp_bexp| $b))
      let body' := asTerm (← `(aimp_stmt| $body))
      `(Imp.AStmt.while $inv $b' $body')
  | `(aimp_stmt| ($s)) =>
      `(aimp_stmt| $s)

macro_rules
  | `([aimp| $s:aimp_stmt ]) => `(aimp_stmt| $s)

-- ============================================================
-- Triple syntax:  [triple| pre(P) stmt post(Q) ]
-- Expands to `Imp.vc' P stmt Q : Prop`, which packages the
-- verification conditions together with the entailment check.
-- ============================================================

declare_syntax_cat aimp_triple
syntax "pre(" term ")" aimp_stmt "post(" term ")" : aimp_triple

syntax "[triple| " aimp_triple " ]" : term

macro_rules
  | `([triple| pre($p) $s post($q) ]) => do
      let s' := asTerm (← `(aimp_stmt| $s))
      `(Imp.FH $p (Imp.AStmt.toStmt $s') $q)

end Imp
