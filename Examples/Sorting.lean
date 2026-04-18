
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

#eval insertion_sort [3, 1, 4, 1, 5, 9]

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


@[grind →]
theorem is_sorted_tail (y : Nat) (ys : List Nat) :
    is_sorted (y :: ys) = true → is_sorted ys = true := by
  intro h; cases ys <;> grind [is_sorted]

@[grind →]
theorem sorted_cons_le (y z : Nat) (zs : List Nat) :
    is_sorted (y :: z :: zs) = true → y ≤ z := by
  grind [is_sorted]

@[grind →]
theorem sorted_lb (y : Nat) (ys : List Nat) :
    is_sorted (y :: ys) = true → ∀ z ∈ ys, y ≤ z := by
  induction ys generalizing y with
  | nil => simp
  | cons w ws ih =>
    intro h z hz; grind

@[grind =]
theorem mem_insert (w x : Nat) (xs : List Nat) :
    w ∈ insert x xs ↔ w = x ∨ w ∈ xs := by
  induction xs with
  | nil => simp [insert]
  | cons a as ih =>
    unfold insert
    by_cases hxa : x ≤ a
    · simp [if_pos hxa, List.mem_cons]
    · simp only [if_neg hxa, List.mem_cons, ih]; grind

theorem insert_lb (n x : Nat) (xs : List Nat) :
    n ≤ x → (∀ z ∈ xs, n ≤ z) → ∀ w ∈ insert x xs, n ≤ w := by
  grind

@[grind ←]
theorem is_sorted_cons_of_lb (y : Nat) (ys : List Nat) :
    (∀ z ∈ ys, y ≤ z) → is_sorted ys = true → is_sorted (y :: ys) = true := by
  intro hbound hsorted; cases ys <;> grind [is_sorted]

theorem insert_preserves_sortedness (x : Nat) (xs : List Nat) :
  is_sorted xs = true → is_sorted (insert x xs) = true := by
  intros h
  induction xs with
  | nil => simp [insert, is_sorted]
  | cons y ys ih =>
    simp [insert]; grind [is_sorted]


@[grind =]
theorem count_insert (n x : Nat) (xs : List Nat) :
    count n (insert x xs) = count n (x :: xs) := by
  induction xs with
  | nil => simp [insert, count]
  | cons a as ih =>
    unfold insert
    by_cases hxa : x ≤ a
    · simp [if_pos hxa]
    · simp only [if_neg hxa, count, ih]; grind

@[grind =]
theorem count_insertion_sort (n : Nat) (xs : List Nat) :
    count n (insertion_sort xs) = count n xs := by
  induction xs <;> simp_all [insertion_sort, count_insert, count]

theorem items_equally_represented_of_count (items xs ys : List Nat)
    (h : ∀ n, count n xs = count n ys) :
    items_equally_represented items xs ys = true := by
  induction items <;> simp_all [items_equally_represented]

theorem insertion_sort_correct (xs : List Nat) :
  is_sorted (insertion_sort xs) = true ∧
  is_permutation xs (insertion_sort xs) = true := by
  induction xs with
  | nil => simp [insertion_sort, is_sorted, is_permutation, items_equally_represented]
  | cons x xs ih =>
    constructor
    · -- is_sorted
      simp only [insertion_sort]
      exact insert_preserves_sortedness x _ ih.1
    · -- is_permutation
      simp only [is_permutation]
      apply items_equally_represented_of_count
      intro n
      simp only [insertion_sort, count_insert, count, count_insertion_sort]


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


def BinaryTree.to_list : BinaryTree → List Nat
  | .empty => []
  | .node value count left right =>
    BinaryTree.to_list left ++ List.replicate count value ++ BinaryTree.to_list right

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

@[grind =]
theorem BinaryTree.mem_insert (n x : Nat) (t : BinaryTree) :
    mem (BinaryTree.insert n t) x = true ↔ x = n ∨ mem t x = true := by
  induction t with
  | empty =>
    simp [BinaryTree.insert, mem]
  | node v c l r ihl ihr =>
    simp only [BinaryTree.insert]
    by_cases h_eq : n = v
    · simp only [if_pos h_eq, mem]; grind
    · by_cases h_lt : n < v
      · simp only [if_neg h_eq, if_pos h_lt, mem]
        by_cases hxv : x = v <;> simp_all [Bool.or_eq_true]
        exact or_assoc
      · simp only [if_neg h_eq, if_neg h_lt, mem]
        by_cases hxv : x = v <;> simp_all [Bool.or_eq_true]
        grind


theorem bst_insert_preserves_bst (n : Nat) (t : BinaryTree) (h : IsBST t) :
    IsBST (BinaryTree.insert n t) := by
  induction h with
  | emp =>
    simp only [BinaryTree.insert]
    apply IsBST.node <;> try exact IsBST.emp
    all_goals (intro x hx; simp [Membership.mem, mem] at hx)
  | node value count left right _ hr hlb hrb ihl ihr =>
    simp only [BinaryTree.insert]
    by_cases h_eq : n = value
    · simp only [if_pos h_eq]
      exact IsBST.node value (count + 1) left right ‹_› hr hlb hrb
    · by_cases h_lt : n < value
      · simp only [if_neg h_eq, if_pos h_lt]
        apply IsBST.node _ _ _ _ ihl hr _ hrb
        intro x hx
        rcases (BinaryTree.mem_insert n x left).mp hx with rfl | hx'
        · exact h_lt
        · exact hlb x hx'
      · simp only [if_neg h_eq, if_neg h_lt]
        apply IsBST.node _ _ _ _ ‹_› ihr hlb
        intro x hx
        rcases (BinaryTree.mem_insert n x right).mp hx with rfl | hx'
        · omega
        · exact hrb x hx'

def BST.insert (n : Nat) (bst : BST) : BST :=
  { tree := BinaryTree.insert n bst.tree,
    is_bst := bst_insert_preserves_bst n bst.tree bst.is_bst }


def BST.to_sorted_list (bst : BST) : List Nat := BinaryTree.to_list bst.tree


def bst_sort (xs : List Nat) : List Nat :=
  let bst := xs.foldl (fun acc x => BST.insert x acc) { tree := BinaryTree.empty, is_bst := IsBST.emp }
  BST.to_sorted_list bst









-- ============================================================
-- Helpers for bst_sort_correct
-- Now using BinaryTree.to_list (transparent, no IsBST needed)
-- ============================================================

theorem is_sorted_replicate (x n : Nat) : is_sorted (List.replicate n x) = true := by
  induction n with
  | zero => simp [is_sorted]
  | succ n ih =>
    rw [List.replicate_succ]
    exact is_sorted_cons_of_lb x (List.replicate n x)
      (fun z hz => by simp [List.mem_replicate] at hz; omega) ih

theorem sorted_append_le (xs ys : List Nat)
    (hxs : is_sorted xs = true) (hys : is_sorted ys = true)
    (hle : ∀ a ∈ xs, ∀ b ∈ ys, a ≤ b) :
    is_sorted (xs ++ ys) = true := by
  induction xs with
  | nil => simpa
  | cons x xs ih =>
    rw [List.cons_append]
    apply is_sorted_cons_of_lb
    · intro z hz
      rw [List.mem_append] at hz
      rcases hz with hz | hz
      · exact sorted_lb x xs hxs z hz
      · exact hle x (List.mem_cons.mpr (Or.inl rfl)) z hz
    · exact ih (is_sorted_tail x xs hxs)
              (fun a ha b hb => hle a (List.mem_cons.mpr (Or.inr ha)) b hb)

-- Elements of BinaryTree.to_list are in the tree
theorem BinaryTree.to_list_mem (t : BinaryTree) (x : Nat) :
    x ∈ BinaryTree.to_list t → mem t x = true := by
  induction t with
  | empty => simp [BinaryTree.to_list]
  | node v c l r ihl ihr =>
    intro hmem
    simp only [BinaryTree.to_list, List.mem_append, List.mem_replicate] at hmem
    rcases hmem with (hmem | ⟨-, rfl⟩) | hmem
    · have hxl : mem l x = true := ihl hmem
      simp only [mem]; by_cases hxv : x = v <;> simp_all
    · simp [mem]
    · have hxr : mem r x = true := ihr hmem
      simp only [mem]; by_cases hxv : x = v <;> simp_all

-- BST.to_sorted_list is sorted for any BST
theorem to_sorted_list_sorted (t : BinaryTree) (h : IsBST t) :
    is_sorted (BinaryTree.to_list t) = true := by
  induction h with
  | emp => simp [BinaryTree.to_list, is_sorted]
  | node v c l r _ _ hlb hrb ihl ihr =>
    simp only [BinaryTree.to_list]
    apply sorted_append_le (BinaryTree.to_list l ++ List.replicate c v)
    · apply sorted_append_le _ _ ihl (is_sorted_replicate v c)
      intro a ha b hb
      simp [List.mem_replicate] at hb; obtain ⟨-, rfl⟩ := hb
      exact Nat.le_of_lt (hlb a (BinaryTree.to_list_mem l a ha))
    · exact ihr
    · intro a ha b hb
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · have h1 := hlb a (BinaryTree.to_list_mem l a ha)
        have h2 := hrb b (BinaryTree.to_list_mem r b hb)
        omega
      · simp [List.mem_replicate] at ha
        obtain ⟨-, rfl⟩ := ha
        exact Nat.le_of_lt (hrb b (BinaryTree.to_list_mem r b hb))

-- ---- count helpers ----

theorem count_append (n : Nat) (xs ys : List Nat) :
    count n (xs ++ ys) = count n xs + count n ys := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    simp only [List.cons_append, count, ih]; grind

theorem count_replicate (n x k : Nat) :
    count n (List.replicate k x) = if x = n then k else 0 := by
  induction k with
  | zero => simp [count]
  | succ k ih =>
    rw [List.replicate_succ, count, ih]; grind

-- ---- tree_count relates BinaryTree.to_list counts to tree structure ----

def tree_count (n : Nat) : BinaryTree → Nat
  | .empty => 0
  | .node value c left right =>
    (if value = n then c else 0) + tree_count n left + tree_count n right

theorem count_to_list (t : BinaryTree) (n : Nat) :
    count n (BinaryTree.to_list t) = tree_count n t := by
  induction t with
  | empty => simp [BinaryTree.to_list, count, tree_count]
  | node v c l r ihl ihr =>
    simp only [BinaryTree.to_list, tree_count, count_append, count_replicate, ihl, ihr]; grind

theorem tree_count_insert (n x : Nat) (t : BinaryTree) :
    tree_count n (BinaryTree.insert x t) = (if x = n then 1 else 0) + tree_count n t := by
  induction t with
  | empty =>
    simp [BinaryTree.insert, tree_count]
  | node v c l r ihl ihr =>
    unfold BinaryTree.insert tree_count
    by_cases h_eq : x = v
    · simp [h_eq]; grind
    · by_cases h_lt : x < v
      · simp [h_eq, h_lt, ihl]; omega
      · simp [h_eq, h_lt, ihr]; omega

theorem tree_count_foldl (n : Nat) (xs : List Nat) (init : BST) :
    tree_count n (xs.foldl (fun acc x => BST.insert x acc) init).tree =
    count n xs + tree_count n init.tree := by
  induction xs generalizing init with
  | nil => simp [count]
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (BST.insert x init)]
    show count n xs + tree_count n (BinaryTree.insert x init.tree) =
         count n (x :: xs) + tree_count n init.tree
    simp only [count, tree_count_insert]; grind

-- ============================================================
-- Main theorem: bst_sort is correct
-- ============================================================

theorem bst_sort_correct (xs : List Nat) :
    is_sorted (bst_sort xs) = true ∧ is_permutation xs (bst_sort xs) = true := by
  constructor
  · -- sorted
    let bst := xs.foldl (fun acc x => BST.insert x acc) ⟨.empty, IsBST.emp⟩
    exact to_sorted_list_sorted bst.tree bst.is_bst
  · -- permutation: counts agree
    apply items_equally_represented_of_count
    intro n
    simp only [bst_sort, BST.to_sorted_list, count_to_list]
    have h := tree_count_foldl n xs ⟨.empty, IsBST.emp⟩
    simp [tree_count] at h
    exact h.symm


#eval! timeit "foo" (do let s := bst_sort [3, 1, 4, 1, 5, 9])
