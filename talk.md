# Verifying Code with Lean 

## Lean is a Fully-Featured Functional Programming Language!

### You probably know that you can write functional programs in Lean. 
```lean
def insert (n : Nat) : List Nat → List Nat
| [] => [n]
| (x :: xs) =>
  if n ≤ x then
    n :: x :: xs
  else
    x :: insert n xs


def insertion_sort : List Nat → List Nat
| [] => []
| (x :: xs) => insert x (insertion_sort xs)

#eval insertion_sort [3, 1, 4, 1, 5, 9]
-- [1, 1, 3, 4, 5, 9]
```


### You probably also know that you can prove functional programs correct in Lean.
```lean
theorem insertion_sort_correct (xs : List Nat) :
  is_sorted (insertion_sort xs) = true ∧
  is_permutation xs (insertion_sort xs) = true := by
  -- Proof ...
```


### You may not know that you can write programs that interact with your operating system like other main-stream languages. 
```bash
lake exe examples ins sort-in/10.txt
```

### This is great! This means that we can *run* code that is proven to behave according to our specifications. 

### This also means that we can write optimized programs that are more complicated without risking correctness. 
```lean
inductive BinaryTree where
  | empty
  | node (value : Nat) (count : Nat) (left right : BinaryTree)

inductive IsBST : BinaryTree → Prop where
 | emp : IsBST BinaryTree.empty
 | node (value count : Nat) (left right : BinaryTree) :
   IsBST left →
   IsBST right →
   (∀ x, x ∈ left → x < value) →
   (∀ x, x ∈ right → x > value) →
   IsBST (BinaryTree.node value count left right)

structure BST where
  tree : BinaryTree
  is_bst : IsBST tree

def BinaryTree.insert (n : Nat) : BinaryTree → BinaryTree
  | .empty => .node n 1 .empty .empty
  | .node value count left right =>
    if n = value then .node value (count + 1) left right
    else if n < value then .node value count (BinaryTree.insert n left) right
    else .node value count left (BinaryTree.insert n right)

def BST.insert (n : Nat) (bst : BST) : BST :=
  { tree := BinaryTree.insert n bst.tree,
    is_bst := bst_insert_preserves_bst n bst.tree bst.is_bst }

def BST.to_sorted_list (bst : BST) : List Nat := BinaryTree.to_list bst.tree

def bst_sort (xs : List Nat) : List Nat :=
  let bst := xs.foldl (fun acc x => BST.insert x acc) { tree := BinaryTree.empty, is_bst := IsBST.emp }
  BST.to_sorted_list bst
```

### For example, Sorting by repeated insertion into a Binary Search Tree, followed by flattening runs much faster than insertion sort.
```bash
time lake exe examples ins sort-in/100000.txt
# 30.65s
```

```bash
time lake exe examples bin sort-in/100000.txt
# 0.08s 
```

### We can rest assured that our algorithm that sorts with BSTs is correct despite the added complexity.


## But what about imperative programs? 

### The world is full of imperative code -- programs that have implicit state, use while loops, & assignment. 

### Most people only write imperative code! We should be able to prove it. 

### How can Lean help with this if it's a functional programming language?

### Idea: *Embed* the imperative language *in Lean*
Imagine the most basic imperative programming language you've ever seen. 
It might look a little like this:

### It might only have numbers as values
```imp
0, 1, 2, 3
```

### It would support assignment & variables
```imp
x := 1
y := x
```

### It would have conditions
```imp
if (x <= y) {
    z := 1
} else {
    z := 2
}
```

### It would have loops
```imp
sum := 0;
i := 0;
while (i <= n) {
  sum := sum + i;
  i := i + 1
}
```

### So What? How can we talk about these programs in Lean?

### We can modify Lean's Syntax!!
Lean allows us to add parsing rules to the language:
```lean
syntax num                          : imp_aexp  -- integer literal
syntax "-" noWs num                 : imp_aexp  -- negative literal
syntax ident                        : imp_aexp  -- variable
syntax "(" imp_aexp ")"             : imp_aexp  -- parenthesized

-- Binary operators (left-associative, usual precedence)
syntax:50 imp_aexp:50 " + " imp_aexp:51 : imp_aexp
syntax:50 imp_aexp:50 " - " imp_aexp:51 : imp_aexp
syntax:60 imp_aexp:60 " * " imp_aexp:61 : imp_aexp

-- And so on ...
```

### At the end of the day, we can write things like
```lean
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
```

### `count_up` and `count_down` refer to *Imperative Programs*

### So what does Lean buy us? 

### We can use Lean to *reason* about these programs 

### For example, we can use Lean to *prove* the equivalence between these two programs.


## How!

### First, let's consider the naive approach 

### We must tell Lean what these programs mean 

### In other words, we must give Lean the *semantics* of our language

### You can think of *semantics* as telling Lean how to *evaluate* our programs

### We can define this as a runnable Lean function. 
```lean
def Stmt.eval (s : Stmt) (st : State) (fuel : Nat := 1000) : Option State :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match s with
    | .skip => some st
    | .assign x a => some (st.update x (aeval a st))
    | .seq s₁ s₂ => do
        let st' ← s₁.eval st fuel
        s₂.eval st' fuel
    | .ifThenElse b s₁ s₂ =>
        if beval b st then s₁.eval st fuel else s₂.eval st fuel
    | .while b body =>
        if beval b st then do
          let st' ← body.eval st fuel
          Stmt.eval (.while b body) st' fuel
        else some st
```

### We can also define evaluation as a Lean Inductive Proposition. This ends up being easier to use in proofs. 
```lean
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
```

### These two definitions are equivalent. That is:
```lean
theorem eval_bigstep_true (s : Stmt) (st st' : State) :
  BigStep st s st' ↔ ∃ fuel, s.eval st fuel = some st' := by
  -- Proof ...
```

### From here on out we'll use `BigStep` to give meaning to Imp Programs


### Great! Let's prove it!
```lean
-- TODO: Giant proof via Big-Step Semantics
```

### That was painful. Maybe there is a better way.


## Floyd-Hoare Logic

### We want **easier** proofs with **more** automation.

### Good news! Floyd-Hoare Logic was designed for this! 

### In Floyd-Hoare Logic, programs have *preconditions* and *postconditions*

### Preconditions are assertions over the state before the program runs

### Postconditions are assertions over the state after the program runs
```lean

```


