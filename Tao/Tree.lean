inductive Tree (α : Type)
  | leaf
  | root (left right : Tree α) (a : α)
namespace Tree
variable {α : Type}

instance : EmptyCollection (Tree α) where emptyCollection := leaf
instance : Singleton α (Tree α) where singleton := root ∅ ∅

inductive mem x : Tree α → Prop
  | left {left right a} : mem x left → mem x (root left right a)
  | right {left right a} : mem x right → mem x (root left right a)
  | rfl {left right} : mem x (root left right x)

instance : Membership α (Tree α) where mem := mem

instance decMem [DecidableEq α] x : (t : Tree α) → Decidable (x ∈ t)
  | leaf => isFalse nofun
  | root left right a =>
    if e : x = a then isTrue (e ▸ mem.rfl) else
    match decMem x left with
    | isTrue (h : x ∈ left) => isTrue (mem.left h)
    | isFalse (h : x ∉ left) =>
      match decMem x right with
      | isTrue (h' : x ∈ right) => isTrue (mem.right h')
      | isFalse (h' : x ∉ right) =>
        isFalse fun
        | mem.left k => h k
        | mem.right k => h' k
        | mem.rfl => e rfl

inductive All (p : Tree α → Tree α → α → Prop) : Tree α → Prop
  | leaf : All p ∅
  | root {left right a} : left.All p → right.All p → p left right a → (root left right a).All p
namespace All
variable {p : Tree α → Tree α → α → Prop} {L R : Tree α} {a : α}

def left : All p (.root L R a) → L.All p
  | root h _ _ => h
def right : All p (.root L R a) → R.All p
  | root _ h _ => h
def refl : All p (.root L R a) → p L R a
  | root _ _ h => h

end All

namespace Try1

-- theorem singleton_mem {a b : α} : a ∈ {b} → a = b
--   | mem.refl => rfl

instance : Setoid (Tree α) where
  r s t := ∀ x, x ∈ s ↔ x ∈ t
  iseqv.refl _ _ := Iff.rfl
  iseqv.symm h x := (h x).symm
  iseqv.trans h h' x := (h x).trans (h' x)

instance : HasSubset (Tree α) where
  Subset s t := ∀ x ∈ s, x ∈ t

variable [Lt : LT α]

-- def Sorted : Tree α → Prop := All fun left right a => (∀ x ∈ left, x < a) ∧ (∀ x ∈ right, a < x)
-- theorem singleton_sorted {a : α} : (root ∅ ∅ a).Sorted := All.root All.leaf All.leaf ⟨nofun, nofun⟩

-- def BST (α) [LT α] : Type := Subtype (@Sorted α _)
-- def BST (α : Type) [LT α] : Type := {t : Tree α // Sorted t}
structure BST (α) [LT α] where
  tree : Tree α
  sorted : tree.All fun left right a => ∀ {x}, (x ∈ left → x < a) ∧ (x ∈ right → a < x)

-- instance : Coe (BST α) (Tree α) where coe t := t.tree

-- theorem BST.ext {s t : BST α} : s.val ≈ t.val → s = t := sorry

instance : EmptyCollection (BST α) where
  emptyCollection := {
      tree := ∅
      sorted := All.leaf
    }
instance : Singleton α (BST α) where
  singleton a := {
      tree := root ∅ ∅ a
      sorted := All.root All.leaf All.leaf ⟨nofun, nofun⟩
   }

variable [DecidableRel Lt.lt]

/-
def BST.contains : BST α → α → Bool
  | ⟨∅, _⟩, _ => false
  | ⟨root left right a, h⟩, x =>
    if x < a then contains ⟨left, h.left⟩ x
    else if x > a then contains ⟨right, h.right⟩ x
    else true
termination_by t => t.val
-/

def BST.find? : BST α → α → Option (BST α)
  | ⟨leaf, _⟩, _ => none
  | t@⟨root left right b, h⟩, a =>
    if a < b then find? ⟨left, h.left⟩ a
    else if a > b then find? ⟨right, h.right⟩ a
    else t

def BST.contains (t : BST α) (x : α) : Bool := (t.find? x).isSome

-- def IsInsert (a : α) (s : Tree α) := {t : Tree α // ∀ {x}, x ∈ t ↔ x ∈ s ∨ x = a}
structure Insertion (a : α) (t : BST α) extends BST α where
  insert x : x = a ∨ x ∈ t.tree ↔ x ∈ tree

-- variable [Antisymm Lt.lt]
#check Union
def BST.insert (a : α) : (t : BST α) → Insertion a t
  | ⟨leaf, _⟩ => {
      toBST := {a}
      insert := fun _ => ⟨fun | .inl rfl => mem.rfl, fun | mem.rfl => .inl rfl⟩
    }
  | ⟨root L R b, sorted⟩ =>
    if Lt : a < b then
      let ⟨left, hl⟩ := insert a ⟨L, sorted.left⟩
      {
        tree := root left.tree R b
        sorted :=
          suffices ∀ {x}, x ∈ left.tree → x < b
          from All.root left.sorted sorted.right ⟨this, sorted.refl.right⟩
          fun {x} h => ((hl x).mpr h).rec (trans · Lt) sorted.refl.left
        insert := fun x => Iff.intro
          fun
          | h =>
            match x, h with
            | _, .inl rfl => mem.left ((hl a).mp (.inl rfl))
            | x, .inr (mem.left h) => mem.left ((hl x).mp (.inr h))
            | _, .inr (mem.right h) => mem.right h
            | _, .inr mem.rfl => mem.rfl
          fun
          | mem.left h => ((hl x).mpr h).imp_right mem.left
          | mem.right h => .inr (mem.right h)
          | mem.rfl => .inr mem.rfl
        -- insert.mpr := _
      }
    else if Gt : a > b then
      sorry
    else sorry
/-
def BST.insert : (s : BST α) (a : α) : {t : BST α // ∀ {x}, x ∈ t.val ↔ x ∈ s.val ∨ x = a} :=
  match s with
  | ⟨leaf, _⟩ => ⟨⟨root ∅ ∅ a, singleton_sorted⟩,
      fun | mem.refl => .inr rfl, Or.rec nofun fun | rfl => mem.refl⟩
  | t@⟨root L R b, h⟩ =>
    if Lt : a < b then
      let ⟨left, hl, hx⟩ := insert ⟨L, h.left⟩ a
      suffices ∀ x ∈ left, x < b
      from ⟨root left R b, All.root hl h.right ⟨this, h.refl.right⟩, sorry /-mem.left hx-/⟩
      have : ∀ x ∈ _, x < b := h.refl.left
      sorry
    else if Gt : a > b then
      have ⟨right, hr, hx⟩ := insert ⟨R, h.right⟩ a
      ⟨root L right b, All.root h.left hr ⟨h.refl.left, sorry⟩, sorry /-mem.right hx-/⟩
    else ⟨t.val, t.property, sorry⟩
termination_by s.val
-/
instance : Insert α (BST α) where insert a t := (BST.insert a t).toBST

end Try1

namespace Try2

structure BST (α) [LT α] where
  tree : Tree α
  sorted : tree.All fun left right a => ∀ {x}, (x ∈ left → x < a) ∧ (x ∈ right → a < x)

namespace BST
variable [Lt : LT α]

instance : EmptyCollection (BST α) where emptyCollection :=
  {
    tree := ∅
    sorted := All.leaf
  }
instance : Singleton α (BST α) where singleton a :=
  {
    tree := {a}
    sorted := All.root All.leaf All.leaf ⟨nofun, nofun⟩
  }

variable [DecidableRel Lt.lt]

def find? : BST α → α → Option (BST α)
  | ⟨leaf, _⟩, _ => none
  | t@⟨root left right b, h⟩, a =>
    if a < b then find? ⟨left, h.left⟩ a
    else if a > b then find? ⟨right, h.right⟩ a
    else t

def contains (t : BST α) (x : α) : Bool := (t.find? x).isSome

structure Insertion (a : α) (t : BST α) extends BST α where
  insert {x} : x ∈ tree → x = a ∨ x ∈ t.tree

def BST.insert (a : α) : (t : BST α) → Insertion a t
  | ⟨leaf, _⟩ =>
    {
      toBST := {a}
      insert := fun | mem.rfl => .inl rfl
    }
  | t@e:⟨root L R b, sorted⟩ =>
    if Lt : a < b then
      let ⟨left, hl⟩ := insert a ⟨L, sorted.left⟩
      {
        tree := root left.tree R b
        sorted :=
          suffices ∀ {x}, x ∈ left.tree → x < b
          from All.root left.sorted sorted.right ⟨this, sorted.refl.right⟩
          fun h => (hl h).rec (fun | rfl => Lt) sorted.refl.left
        insert := fun {x} h =>
          match x, h with
          | _, mem.left h => (hl h).imp_right mem.left
          | _, mem.right h => .inr (mem.right h)
          | _, mem.rfl => .inr mem.rfl
      }
    else if Gt : a > b then
      let ⟨right, hr⟩ := insert a ⟨R, sorted.right⟩
      {
        tree := root L right.tree b
        sorted :=
          suffices ∀ {x}, x ∈ right.tree → b < x
          from All.root sorted.left right.sorted ⟨sorted.refl.left, this⟩
          fun h => (hr h).rec (fun | rfl => Gt) sorted.refl.right
        insert := fun {x} h =>
          match x, h with
          | _, mem.left h => .inr (mem.left h)
          | _, mem.right h => (hr h).imp_right mem.right
          | _, mem.rfl => .inr mem.rfl
      }
    else
      {
        toBST := t
        insert := fun h => .inr (e ▸ h)
      }

instance : Insert α (BST α) where insert a t := (BST.insert a t).toBST

end BST

end Try2

namespace Try3

structure Insertion (a : α) (t : Tree α) where
  tree : Tree α
  insert {x} : x ∈ tree → x = a ∨ x ∈ t

section Insertion
variable [Lt : LT α] [DecidableRel Lt.lt]

def insert (a : α) : (t : Tree α) → Insertion a t
  | leaf => ⟨{a}, fun | mem.rfl => .inl rfl⟩
  | tree@e:(root left right b) =>
    if a < b then
      let ⟨left, hl⟩ := insert a left
      {
        tree := root left right b
        insert := fun {x} h =>
          match x, h with
          | _, mem.left h => (hl h).imp_right mem.left
          | _, mem.right h => .inr (mem.right h)
          | _, mem.rfl => .inr mem.rfl
      }
    else if a > b then
      let ⟨right, hr⟩ := insert a right
      {
        tree := root left right b
        insert := fun {x} h =>
          match x, h with
          | _, mem.left h => .inr (mem.left h)
          | _, mem.right h => (hr h).imp_right mem.right
          | _, mem.rfl => .inr mem.rfl
      }
    else ⟨tree, fun h => .inr (e ▸ h)⟩

end Insertion

structure BST (α) [LT α] where
  tree : Tree α
  sorted : tree.All fun left right a => ∀ {x}, (x ∈ left → x < a) ∧ (x ∈ right → a < x)

namespace BST
variable [Lt : LT α]

instance : EmptyCollection (BST α) where emptyCollection :=
  {
    tree := ∅
    sorted := All.leaf
  }
instance : Singleton α (BST α) where singleton a :=
  {
    tree := {a}
    sorted := All.root All.leaf All.leaf ⟨nofun, nofun⟩
  }

variable [DecidableRel Lt.lt]

structure Insertion (a : α) (t : BST α) extends BST α where
  insert {x} : x ∈ tree → x = a ∨ x ∈ t.tree

def BST.insert (a : α) : (t : BST α) → Insertion a t
  | ⟨leaf, _⟩ =>
    {
      toBST := {a}
      insert := fun | mem.rfl => .inl rfl
    }
  | t@e:⟨root L R b, sorted⟩ =>
    if Lt : a < b then
      let ⟨left, hl⟩ := insert a ⟨L, sorted.left⟩
      {
        tree := root left.tree R b
        sorted :=
          suffices ∀ {x}, x ∈ left.tree → x < b
          from All.root left.sorted sorted.right ⟨this, sorted.refl.right⟩
          fun h => (hl h).rec (fun | rfl => Lt) sorted.refl.left
        insert := fun {x} h =>
          match x, h with
          | _, mem.left h => (hl h).imp_right mem.left
          | _, mem.right h => .inr (mem.right h)
          | _, mem.rfl => .inr mem.rfl
      }
    else if Gt : a > b then
      let ⟨right, hr⟩ := insert a ⟨R, sorted.right⟩
      {
        tree := root L right.tree b
        sorted :=
          suffices ∀ {x}, x ∈ right.tree → b < x
          from All.root sorted.left right.sorted ⟨sorted.refl.left, this⟩
          fun h => (hr h).rec (fun | rfl => Gt) sorted.refl.right
        insert := fun {x} h =>
          match x, h with
          | _, mem.left h => .inr (mem.left h)
          | _, mem.right h => (hr h).imp_right mem.right
          | _, mem.rfl => .inr mem.rfl
      }
    else
      {
        toBST := t
        insert := fun h => .inr (e ▸ h)
      }

instance : Insert α (BST α) where insert a t := (BST.insert a t).toBST

end BST

end Try3

section Try4
variable [Lt : LT α] [DecidableRel Lt.lt]

def insert (a : α) : Tree α → Tree α
  | leaf => {a}
  | root left right b =>
    if a < b then root (insert a left) right b
    else if a > b then root left (insert a right) b
    else root left right b

def insertRec.{v} {motive : α → Tree α → Tree α → Sort v}
  (leaf : ∀ a, motive a leaf (insert a leaf))
  (left : ∀ {a b} left, a < b → motive a left (insert a left))
  (right : ∀ {a b} right, a > b → motive a right (insert a right))
  : ∀ {a t}, motive a t (insert a t) := sorry

theorem insert_def {a x} : {t : Tree α} → x ∈ insert a t → x = a ∨ x ∈ t
  | leaf, mem.rfl => .inl rfl
  | root left right b, h =>
    if h₁ : a < b then
      have :=
        calc  x
          _ ∈ if a < b then _ else _ := h
          _ = root (insert a left) right b := if_pos h₁
      match x, this with
      | _, mem.left h => (insert_def h).imp_right mem.left
      | _, mem.right h => .inr (mem.right h)
      | _, mem.rfl => .inr mem.rfl
    else if h₂ : a > b then
      have :=
        calc  x
          _ ∈ if a < b then _ else _ := h
          _ = if a > b then _ else _ := if_neg h₁
          _ = root left (insert a right) b := if_pos h₂
      match x, this with
      | _, mem.left h => .inr (mem.left h)
      | _, mem.right h => (insert_def h).imp_right mem.right
      | _, mem.rfl => .inr mem.rfl
    else
      have :=
        calc  x
          _ ∈ if a < b then _ else _ := h
          _ = if a > b then _ else _ := if_neg h₁
          _ = root left right b := if_neg h₂
      .inr this

inductive Sorted : Tree α → Prop
  | leaf : Sorted ∅
  | root {left right a}
    : Sorted left → (∀ {x}, x ∈ left → x < a)
    → Sorted right → (∀ {x}, x ∈ right → x > a)
    → Sorted (root left right a)

theorem insert_sorted {a} {t : Tree α} : t.Sorted → (insert a t).Sorted := sorry

end Try4

end Tree
