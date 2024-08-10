namespace Try1
/-
* https://en.wikipedia.org/wiki/Binary_tree#Types_of_binary_trees
-/

/-- Rooted binary tree -/
inductive Tree (α)
  | nil
  | node (left : Tree α) (value : α) (right : Tree α)

namespace Tree
variable {α}

-- instance {α : Type _} : EmptyCollection (Tree α) where emptyCollection := nil

def height : Tree α → Nat
  | nil => 0
  | node L _ R => max L.height R.height + 1

/-- A.k.a, **full**, **proper**, **plane**, **strict**. -/
inductive Full : Tree α → Prop
  | nil : Full nil
  | leaf {x} : Full (node nil x nil)
  | node {L x R} : Full L → Full R → Full (node L x R)

/-- All leaves have the same **depth**/**level**.
The **level** of a node is the number of **edges**/**links** from the root to a node.
-/
inductive Perfect : Tree α → Nat → Prop
  | nil : Perfect nil 0
  | node {L x R n} : Perfect L n → Perfect R n → Perfect (node L x R) n.succ

theorem height_of_perfect {t : Tree α} {n} : Perfect t n → n = t.height :=
  sorry

theorem perfect_of_same_height {L R : Tree α} {x n}
  : L.height = n → R.height = n → Perfect (node L x R) n.succ :=
  sorry

abbrev Perfect' (t : Tree α) : Prop := Perfect t t.height

theorem full_of_perfect {t : Tree α} {n} : Perfect t n → Full t
  | .nil => .nil
  | .node l r => .node (full_of_perfect l) (full_of_perfect r)

/-- A binary tree in which every level, except possibly the last, is completely
filled, and all nodes in the last level are as far left as possible. It can have
between `1` and `2ʰ` nodes at the last level `h`.
-/
inductive Complete : Tree α → Prop
  | ofFull {t} : Full t → Complete t
  | left {L x R} : L.height = R.height.succ → Complete L → Full R → Complete (node L x R)
  | right {L x R} : L.height = R.height → Full L → Complete R → Complete (node L x R)

theorem complete_of_perfect {t : Tree α} : Perfect' t → Complete t :=
  sorry

example : ∃ t : Tree α, Complete t ∧ ¬Perfect' t :=
  sorry

/-- The left and right subtrees of every node differ in height by no more than `1`,
i.e., the **skew** is no greater than `1`.
One may also consider binary trees where **no nil is much farther away** from the root
than any other nil; different **balancing schemes** allow different definitions
of "much farther".
-/
inductive Balanced : Tree α → Nat → Prop
  | nil : Balanced nil 0
  | same {L x R n} : Balanced L n → Balanced R n → Balanced (node L x R) n.succ
  | left {L x R n} : Balanced L n.succ → Balanced R n → Balanced (node L x R) n.succ
  | right {L x R n} : Balanced L n → Balanced R n.succ → Balanced (node L x R) n.succ

/-- A.k.a, **degenerate**, **pathalogical**.
Each parent has at most one child, making a degenerate tree essentially a list.
-/
inductive Degenerate : Tree α → Prop
  | nil : Degenerate nil
  | left {L x} : Degenerate L → Degenerate (node L x nil)
  | right {x R} : Degenerate R → Degenerate (node nil x R)

section Heap
variable [Le : LE α]

/-- A [**max-heap**](https://en.wikipedia.org/wiki/Heap_(data_structure)) to be precise.
Modelled on C++ [`std::priority_queue`](https://en.cppreference.com/w/cpp/container/priority_queue)
and [Heap operations](https://en.cppreference.com/w/cpp/header/algorithm#Heap_operations)
in `<algorithm>`.
-/
inductive Heap : Tree α → Prop
  | nil : Heap nil
  | leaf {x} : Heap (node nil x nil)
  | left {A x B y R} : x ≤ y → Heap (node A x B) → Heap (node (node A x B) y R)
  | right {L y C z D} : y ≥ z → Heap (node C z D) → Heap (node L y (node C z D))
  | node {A x B y C z D} : x ≤ y → Heap (node A x B) → y ≥ z → Heap (node C z D)
    → Heap (node (node A x B) y (node C z D))

inductive All : Tree α → α → Prop
  | nil {x} : All nil x
  | node {L x R} (y : α) : x ≤ y → All L x → All R x → All (node L x R) y

inductive MaxHeap : Tree α → Option α → Prop
  | nil : MaxHeap nil none
  | node {x y z : α} {L R} : x ≤ y → MaxHeap L x → y ≥ z → MaxHeap R z
    → MaxHeap (node L y R) y

variable [DecidableRel Le.le]
def max? : Tree α → Option α
  | nil => none
  | node L x R =>
    let max := @max α maxOfLe
    match L.max?, R.max? with
    | some a, some b => max (max a b) x
    | some a, none => max a x
    | none, some b => max b x
    | none, none => x

theorem max_heap {t : Tree α} {top : α} : MaxHeap t top → top = t.max? :=
  sorry

end Heap

/-! ## Radix tree
TODO
* https://en.wikipedia.org/wiki/Radix_tree
-/

end Tree

end Try1

namespace Try2

-- class Tree (α τ) where
--   nil : τ
--   node (left : τ) (value : α) (right : τ) : τ

class inductive Tree.{u, v} (α : Sort u) (τ : Type v)
  | nil : Tree α τ
  | node (left : Tree α τ) (value : α) (right : Tree α τ) : Tree α τ

/-- A priority queue implemented as a max-heap based on an array.
API is modelled on `Array`.
-/
structure MaxQ (α) where
  /-- Make constructor private -/
  private mk ::
  data : Array α

namespace MaxQ
variable {α}

def floyd (left : MaxQ α) (value : α) (right : MaxQ α) : MaxQ α :=
  sorry

def nil : MaxQ α where
  data := #[]

instance : Tree α (MaxQ α) := .nil

end MaxQ

end Try2

namespace Try3

-- class Tree (α τ) where
--   nil : τ
--   node (left : τ) (value : α) (right : τ) : τ

class inductive Tree.{u, v} (α : Sort u) (τ : Type v)
  | nil : Tree α τ
  | node (left : Tree α τ) (value : α) (right : Tree α τ) : Tree α τ

/-- A priority queue implemented as a max-heap based on an array.
API is modelled on `Array`.
-/
structure MaxQ (α) where
  /-- Make constructor private -/
  private mk ::
  data : Array α

namespace MaxQ
variable {α}

def floyd (left : MaxQ α) (value : α) (right : MaxQ α) : MaxQ α :=
  sorry

def nil : MaxQ α where
  data := #[]

instance : Tree α (MaxQ α) := .nil

end MaxQ

end Try3
