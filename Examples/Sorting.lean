
namespace Examples

-- Defining Insertion Sort
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


-- A Specification for Being Sorted
def is_sorted : List Nat → Bool
| [] => true
| [_] => true
| (x :: y :: xs) =>
  if x ≤ y then
    is_sorted (y :: xs)
  else
    false


def count (n : Nat) : List Nat → Nat
| [] => 0
| (x :: xs) =>
  if x = n then
    1 + count n xs
  else
    count n xs


def items_equally_represented (items: List Nat) (xs ys : List Nat) : Bool :=
  match items with
  | [] => true
  | (item :: items') =>
    if count item xs = count item ys then
      items_equally_represented items' xs ys
    else
      false


def is_permutation (xs ys : List Nat) : Bool :=
  items_equally_represented xs xs ys


#eval is_permutation [1, 2, 3] [3, 2, 1]
#eval is_permutation [1, 2, 3] [1, 2, 3]
#eval is_permutation [1, 2, 3] [3, 2, 1, 1]
#eval is_permutation [1, 2, 3] [3, 2]


theorem insert_preserves_sortedness (x : Nat) (xs : List Nat) :
  is_sorted xs = true → is_sorted (insert x xs) = true := by
  intros h
  induction xs with
  | nil => simp [insert, is_sorted]
  | cons y ys ih =>
    simp [insert]
    split
    · -- Case 1: x ≤ y
      simp_all [is_sorted]
    · -- Case 2: x > y
      sorry


theorem insertion_sort_correct (xs : List Nat) :
  is_sorted (insertion_sort xs) = true ∧
  is_permutation xs (insertion_sort xs) = true := by
  induction xs with
  | nil => simp [insertion_sort, is_sorted, is_permutation, items_equally_represented]
  | cons x xs ih =>
    constructor
    · -- is_sorted
      simp [insertion_sort]
      sorry
    · -- is_permutation
      sorry


inductive BinaryTree where
  | empty
  | node (value : Nat) (count : Nat) (left right : BinaryTree)


def mem (bt : BinaryTree) (n : Nat) : Bool :=
  match bt with
  | BinaryTree.empty => false
  | BinaryTree.node value _ left right =>
    if n = value then
      true
    else
      let mem_left := mem left n
      let mem_right := mem right n
      mem_left || mem_right


instance : Membership Nat BinaryTree where
  mem bt n := mem bt n


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


def BST.insert (n : Nat) (bst : BST) : BST :=
  match bst with
  | { tree, is_bst } =>
    match tree with
    | BinaryTree.empty =>
      { tree := BinaryTree.node n 1 .empty .empty, is_bst := sorry }
    | BinaryTree.node value count left right =>
      if h_eq : n = value then
        { tree := BinaryTree.node value (count + 1) left right, is_bst := sorry }
      else if h_lt: n < value then
        have left_bst : IsBST left := by cases is_bst <;> assumption
        let new_left := BST.insert n { tree := left, is_bst := left_bst }
        {
          tree := BinaryTree.node value count new_left.tree right,
          is_bst := by sorry
        }
      else
        have right_bst : IsBST right := by cases is_bst <;> assumption
        let new_right := BST.insert n { tree := right, is_bst := right_bst }
        { tree := BinaryTree.node value count left new_right.tree,
          is_bst := by sorry }


def BST.to_sorted_list (bst : BST) : List Nat :=
  match bst with
  | { tree, is_bst } =>
    match tree with
    | BinaryTree.empty => []
    | BinaryTree.node value count left right =>
      have left_bst : IsBST left := by cases is_bst <;> assumption
      let left_list := BST.to_sorted_list { tree := left, is_bst := left_bst }
      have right_bst : IsBST right := by cases is_bst <;> assumption
      let right_list := BST.to_sorted_list { tree := right, is_bst := right_bst }
      left_list ++ List.replicate count value ++ right_list


def bst_sort (xs : List Nat) : List Nat :=
  let bst := xs.foldl (fun acc x => BST.insert x acc) { tree := BinaryTree.empty, is_bst := IsBST.emp }
  BST.to_sorted_list bst


#eval! timeit "foo" (do let s := bst_sort [3, 1, 4, 1, 5, 9])
