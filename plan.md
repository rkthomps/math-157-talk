
# Lean (Title: TBD)

## Why is it great?

### Appeal in Math 
- Verified foundations. 
- Large scale collaboration.
- Proof automation 

### Appeal for Software Verification 
- Proof automation
- Metaprogramming

## What is Software Verification?   
- Lean is a fully-featured programming language 
  - Example: We can define insertion sort and *actually run it on an input file of numbers* 
- The most common way to check program correctness is through unit tests.
  - Example: Unit tests for insertion sort
  - Example: Property based tests for insertion sort
  The problem: you could miss a test. 
  - Example: Buggy version of insertion sort (keeps only one unique number)
- We can address this by *proving properties about our programs*
  - Example: Proof of insertion sort correctness. 
  - Example: Proof of BST sort correctness. Demo of speed boost. 


## Proof Automation for Software Verification  
- Proofs about code: SMT Solvers 
- The grind tactic
- Claude for verifying a compiler


## What is Metaprogramming? 
- Metaprogramming is programming the programming language
- With metaprogramming one change the behavior of Lean. 
  - Custom syntax
    - Example: Imp
  - Custom tactics
    - Example: Some tactic that does something with imp?
  - Modifying existing tactics 
    - Example: Modifying grind?
- None of this affects Lean's correctness guarantees due to 
  the trusted kernel.

## Real World Examples: Loom & Strata 


## Conclusion
- Lean is great
- We can use it to prove properties about code. 
- It is good for this because of metaprogramming and proof automation.


