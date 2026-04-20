---
marp: true
---

# Verifying Code with Lean 

Math 157 Guest Lecture
Kyle Thompson
04/20/2026


---

## Lean is a Fully-Featured Functional Programming Language!

---

## What you've likely already seen:
Writing functional programs
```lean
def insertion_sort : List Nat → List Nat
| [] => []
| (x :: xs) => insert x (insertion_sort xs)
```

Writing proofs about those programs
```lean
theorem insertion_sort_correct (xs : List Nat) :
  is_sorted (insertion_sort xs) = true ∧
  is_permutation xs (insertion_sort xs) = true := by
  -- Proof ...
```

---

## What may be new
*Running verified programs*
```bash
lake exe examples ins sort-in/10.txt
```

<!-- ### This is great! This means that we can *run* code that is proven to behave according to our specifications.  -->

---

## One step further: Optimizing Programs

We can optimize our programs while maintaining our correctness proofs. 

*Example*: Sorting by insertion into a Binary Tree.

```bash
time lake exe examples ins sort-in/100000.txt
# 30.65s
```

```bash
time lake exe examples bin sort-in/100000.txt
# 0.08s 
```

---

## But what about "normal" code? 

---

## Most People are more familiar with Imperative Programs

```c
int sum_n(int n) {
  int sum = 0;
  int i = 0;
  while (i <= n) {
    sum = sum + i;
    i = i + 1;
  }
  return sum;
}
```

---

## How can we reason about these programs in Lean - a functional programming language?

---


## Idea: *Embed* the imperative language *in Lean*

---

# Picture the tiniest imperative language possible. 

---

# Picture the tiniest imperative language possible. 

### It might only have numbers as values
```imp
0, 1, 2, 3
```

---

# Picture the tiniest imperative language possible. 

### It might support assignment & variables
```imp
x := 1
y := x
```

---

# Picture the tiniest imperative language possible. 

### It might have conditions
```imp
if (x <= y) {
    z := 1
} else {
    z := 2
}
```

---

# Picture the tiniest imperative language possible. 

### It might have loops
```imp
sum := 0;
i := 0;
while (i <= n) {
  sum := sum + i;
  i := i + 1
}
```

---

## So What? How can we talk about these programs in Lean?

### We can modify Lean's Syntax!!
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

---

## At the end of the day, we can write things like
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

---

## What can we use Lean for?

With Lean, we can **prove** the **equivalence** between `count_up` and `count_down`.

---

## How?

First, We should tell Lean what our programs mean.

In other words, we should define the **semantics** of our language. 

---

## *Semantics*: Interpreter 

**Semantics by Evaluation**: 
```lean
def Stmt.eval (s : Stmt) (st : State) (fuel : Nat := 1000) : Option State :=
  ...
```

**Run it!**
```lean
#eval (count_up.eval (State.empty.update "n" 5)).get! "sum"
-- 15
```

---

## *Semantics*: Relation
We can define the relation *evaluates to*
```lean
inductive EvaluatesTo : State → Stmt → State → Prop 
```

**Example 1**
```lean
EvaluatesTo (n := 5) count_up (sum := 15) ✅
```

**Example 2**
```lean
EvaluatesTo (n := 5) count_up (sum := 14) ❌
```

---

## These Semantics are the Same!

```lean
theorem eval_bigstep_true (s : Stmt) (st st' : State) :
  EvaluatesTo st s st' <-> ∃ fuel, s.eval st fuel = some st' := by
```

---


## Now we Can Write Our Proof!

Theorem: `count_up` and `count_down` are equivalent

---

## Current Problem:

**Any Proof with a `while` loop will require induction**

**That's a lot of work!**

**Worse**: Most proof automation struggles to reason about induction

---

## A Better, More Grind-able Way: Floyd Hoare Logic

We can prove properties over looping programs as follows. Prove that:

1. The property holds before entering the loop.
2. The property holds after each loop iteration.
3. The property holds after exiting the loop. 

Such properties are called **loop invariants**

---

## Example! Loop Invariant for `count_up`

```lean
def count_up := [imp|
  sum := 0;
  i := 0;
  while (i <= n) {
    sum := sum + i;
    i := i + 1
  }
]
```


```lean
sum == (i * (i - 1)) / 2
```

---

## Verification Conditions with Loop Invariants

Now, instead of doing an induction to prove every property of any program with `while` loops, we just need to prove: 
1. The property holds before entering the loop.
2. The property holds after each loop iteration.
3. The property holds after exiting the loop. 

These requirements are packaged up into a **verification condition**

Verification conditions play nicely with proof automation!!

---

## Conclusion
- In Lean, we can **define**, **verify** and **execute** functional programs.
- We can also **define**, **verify** and **execute** imperative programs. 
- Verification and execution of imperative programs requires defining their **semantics**.
- Imperative programs can become more automatable via **verification conditions**
