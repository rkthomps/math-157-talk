

import Examples.Imp.AST

open Lean in
private def asTerm (s : TSyntax k) : TSyntax `term := ⟨s.raw⟩

namespace Imp

/-! # IMP Syntax Macros

Lean 4 syntax extensions that let users write IMP programs inline as `[imp| ...]`,
which macro-expands to the existing `Imp.Stmt`, `Imp.AExp`, and `Imp.BExp` constructors.
-/

-- ============================================================
-- Syntax categories
-- ============================================================

declare_syntax_cat imp_aexp
declare_syntax_cat imp_bexp
declare_syntax_cat imp_stmt

-- ============================================================
-- Arithmetic expressions
-- ============================================================

-- Atoms
syntax num                          : imp_aexp  -- integer literal
syntax "-" noWs num                 : imp_aexp  -- negative literal
syntax ident                        : imp_aexp  -- variable
syntax "(" imp_aexp ")"             : imp_aexp  -- parenthesized

-- Binary operators (left-associative, usual precedence)
syntax:50 imp_aexp:50 " + " imp_aexp:51 : imp_aexp
syntax:50 imp_aexp:50 " - " imp_aexp:51 : imp_aexp
syntax:60 imp_aexp:60 " * " imp_aexp:61 : imp_aexp

-- ============================================================
-- Boolean expressions
-- ============================================================

syntax "true"                       : imp_bexp
syntax "false"                      : imp_bexp
syntax imp_aexp " == " imp_aexp     : imp_bexp  -- equality
syntax imp_aexp " <= " imp_aexp     : imp_bexp  -- less-or-equal
syntax "!" imp_bexp                 : imp_bexp  -- negation
syntax:30 imp_bexp:30 " && " imp_bexp:31 : imp_bexp  -- conjunction
syntax "(" imp_bexp ")"             : imp_bexp  -- parenthesized

-- ============================================================
-- Statements
-- ============================================================

syntax "skip"                                         : imp_stmt
syntax ident " := " imp_aexp                          : imp_stmt  -- assignment
syntax:10 imp_stmt:10 "; " imp_stmt:11                : imp_stmt  -- sequencing
syntax "if " imp_bexp " then " imp_stmt " else " imp_stmt : imp_stmt
syntax "while " imp_bexp " { " imp_stmt " }"         : imp_stmt
syntax "(" imp_stmt ")"                               : imp_stmt  -- parenthesized

-- ============================================================
-- Entry point
-- ============================================================

syntax "[imp| " imp_stmt " ]" : term

-- ============================================================
-- Macro rules — arithmetic expressions
-- ============================================================

macro_rules
  | `(imp_aexp| $n:num)    => `(Imp.AExp.lit $n)
  | `(imp_aexp| -$n:num)   => `(Imp.AExp.lit (-$n))
  | `(imp_aexp| $x:ident)  => `(Imp.AExp.var $(Lean.quote (toString x.getId)))
  | `(imp_aexp| ($a))      => `(imp_aexp| $a)
  | `(imp_aexp| $a + $b)   => do
      let a' := asTerm (← `(imp_aexp| $a))
      let b' := asTerm (← `(imp_aexp| $b))
      `(Imp.AExp.add $a' $b')
  | `(imp_aexp| $a - $b)   => do
      let a' := asTerm (← `(imp_aexp| $a))
      let b' := asTerm (← `(imp_aexp| $b))
      `(Imp.AExp.sub $a' $b')
  | `(imp_aexp| $a * $b)   => do
      let a' := asTerm (← `(imp_aexp| $a))
      let b' := asTerm (← `(imp_aexp| $b))
      `(Imp.AExp.mul $a' $b')

-- ============================================================
-- Macro rules — boolean expressions
-- ============================================================

macro_rules
  | `(imp_bexp| true)      => `(Imp.BExp.true)
  | `(imp_bexp| false)     => `(Imp.BExp.false)
  | `(imp_bexp| $a:imp_aexp == $b:imp_aexp) => do
      let a' := asTerm (← `(imp_aexp| $a))
      let b' := asTerm (← `(imp_aexp| $b))
      `(Imp.BExp.eq $a' $b')
  | `(imp_bexp| $a:imp_aexp <= $b:imp_aexp) => do
      let a' := asTerm (← `(imp_aexp| $a))
      let b' := asTerm (← `(imp_aexp| $b))
      `(Imp.BExp.le $a' $b')
  | `(imp_bexp| ! $b)      => do
      let b' := asTerm (← `(imp_bexp| $b))
      `(Imp.BExp.not $b')
  | `(imp_bexp| $a && $b)  => do
      let a' := asTerm (← `(imp_bexp| $a))
      let b' := asTerm (← `(imp_bexp| $b))
      `(Imp.BExp.and $a' $b')
  | `(imp_bexp| ($b))      => `(imp_bexp| $b)

-- ============================================================
-- Macro rules — statements
-- ============================================================

macro_rules
  | `(imp_stmt| skip)      => `(Imp.Stmt.skip)
  | `(imp_stmt| $x:ident := $a:imp_aexp) => do
      let a' := asTerm (← `(imp_aexp| $a))
      `(Imp.Stmt.assign $(Lean.quote (toString x.getId)) $a')
  | `(imp_stmt| $s₁ ; $s₂) => do
      let s₁' := asTerm (← `(imp_stmt| $s₁))
      let s₂' := asTerm (← `(imp_stmt| $s₂))
      `(Imp.Stmt.seq $s₁' $s₂')
  | `(imp_stmt| if $b then $s₁ else $s₂) => do
      let b'  := asTerm (← `(imp_bexp| $b))
      let s₁' := asTerm (← `(imp_stmt| $s₁))
      let s₂' := asTerm (← `(imp_stmt| $s₂))
      `(Imp.Stmt.ifThenElse $b' $s₁' $s₂')
  | `(imp_stmt| while $b { $body }) => do
      let b'    := asTerm (← `(imp_bexp| $b))
      let body' := asTerm (← `(imp_stmt| $body))
      `(Imp.Stmt.while $b' $body')
  | `(imp_stmt| ($s))      => `(imp_stmt| $s)

-- ============================================================
-- Entry-point macro
-- ============================================================

macro_rules
  | `([imp| $s:imp_stmt ]) => `(imp_stmt| $s)

end Imp
