namespace Try1

inductive Tree.Color
  | protected red
  | protected black

inductive Tree (α : Type)
  | leaf
  | node (color : Tree.Color) (left right : Tree α) (a : α)

namespace Tree
variable {α : Type}

inductive mem x : Tree α → Prop
  | left {color left right a} : mem x left → mem x (node color left right a)
  | right {color left right a} : mem x right → mem x (node color left right a)
  | rfl {color left right} : mem x (node color left right x)

instance : Membership α (Tree α) where mem := mem

def height : Tree α → Nat
  | leaf => 0
  | node _ left right _ => max left.height right.height + 1

inductive All (p : Color → Tree α → Tree α → α → Prop) : Tree α → Prop
  | leaf : leaf.All p
  | node {color left right a} : left.All p → right.All p → p color left right a
    → (node color left right a).All p

@[match_pattern] abbrev red := @node α Color.red
@[match_pattern] abbrev black := @node α Color.black

-- protected def color : Tree α → Color
--   | leaf | black .. => .black
--   | red .. => .red

inductive BH : Tree α → Nat → Prop
  | leaf : BH leaf 0
  | red {left right a n} : BH left n → BH right n → BH (red left right a) n
  | black {left right a n} : BH left n → BH right n → BH (black left right a) n.succ

-- inductive RedViolation : Tree α → Prop
--   | left {left right a right' a'} : RedViolation (red (red left right a) right' a')
--   | right {left right a left' a'} : RedViolation (red left' (red left right a) a')

-- theorem unique_bh {m n} {t : Tree α} : BH t m → BH t n → m = n
--   | .leaf, .leaf => rfl
--   | .red h₁ _, .red h₂ _ => unique_bh h₁ h₂
--   | .black h₁ _, .black h₂ _ => congrArg _ (unique_bh h₁ h₂)

def bh : Tree α → Nat
  | leaf => 0
  | red left right _ => max left.bh right.bh
  | black left right _ => max left.bh right.bh + 1

theorem bh_def {t : Tree α} {n} : BH t n → t.bh = n
  | .leaf => rfl
  | .red h₁ h₂ => aux (bh_def h₁) (bh_def h₂)
  | .black h₁ h₂ => congrArg _ <| aux (bh_def h₁) (bh_def h₂)
where aux : {m n k : Nat} → m = k → n = k → max m n = k
  | _, _, _, rfl, rfl => Nat.max_self _

theorem unique_bh {m n} {t : Tree α} (h₁ : BH t m) (h₂ : BH t n) : m = n :=
  trans (bh_def h₁).symm (bh_def h₂)

def RH : Tree α → Prop := All fun
  | .red, .red ..,       _, _
  | .red,       _, .red .., _ => False
  |    _,       _, _      , _ => True

/-
theorem half_height_le_bh {n} {t : Tree α} : BH t n → t.height ≤ 2 * n
  | .leaf => .refl
  | .red (left := left) (right := right) h₁ h₂ =>
    have k₁ : left.height ≤ 2 * n := half_height_le_bh h₁
    calc  max left.height right.height + 1 ≤ 2 * n := sorry
  | .black (left := left) (right := right) (n := m) h₁ h₂ =>
    have h₁ : left.height ≤ 2 * m := half_height_le_bh h₁
    have h₂ : right.height ≤ 2 * m := half_height_le_bh h₂
    calc  max left.height right.height + 1
      _ ≤ 2 * m + 1 := Nat.succ_le_succ (Nat.max_le_of_le_of_le h₁ h₂)
      _ ≤ 2 * m + 1 + 1 := Nat.le_succ _
-/

theorem half_height_le_bh : {n : Nat} → {t : Tree α} → RH t → BH t n → t.height ≤ 2 * n
  | _, _, _, .leaf => .refl
  | n, red left right _, _, .red k₁ k₂ =>
    have k₁ : left.height ≤ 2 * n := half_height_le_bh sorry k₁
    calc  max left.height right.height + 1 ≤ 2 * n := sorry
  | .succ n, black left right _, .node h₁ h₂ _, .black k₁ k₂ =>
    have h₁ :  left.height ≤ 2 * n := half_height_le_bh h₁ k₁
    have h₂ : right.height ≤ 2 * n := half_height_le_bh h₂ k₂
    calc  max left.height right.height + 1
      _ ≤ 2 * n + 1 := Nat.succ_le_succ (Nat.max_le_of_le_of_le h₁ h₂)
      _ ≤ 2 * n + 1 + 1 := Nat.le_succ _

end Tree

structure RBTree (α : Type) [LT α] where
  tree : Tree α
  sorted : tree.All fun _ left right a => ∀ {x}, (x ∈ left → x < a) ∧ (x ∈ right → x > a)
  redProp : tree.All fun | .red, .red .., _, _ | .red, _, .red .., _ => False | _, _, _, _ => True
  -- fun color left right _ => color = Color.red → left.color ≠ Color.red ∧ right.color ≠ Color.red
  blackProp h : tree.BH h

namespace RBTree

variable {α : Type} [LT α]

end RBTree

end Try1

theorem Nat.le_max_left_of_le {m n k : Nat} (h : k ≤ m) : k ≤ max m n :=
  trans h (m.le_max_left n)

example {m n k : Nat} (h₁ : m < k) (h₂ : n < k) : max m n + 1 < k + 1 :=
  Nat.succ_lt_succ (Nat.max_lt.mpr ⟨h₁, h₂⟩)

namespace Try2

inductive Tree.Color
  | protected red
  | protected black

inductive Tree (α : Type)
  | leaf
  | node (color : Tree.Color) (left right : Tree α) (a : α)

namespace Tree
variable {α : Type}

@[match_pattern] abbrev red := @node α Color.red
@[match_pattern] abbrev black := @node α Color.black

def size : Tree α → Nat
  | leaf => 1
  | node _ left right _ => left.size + right.size + 1

def height : Tree α → Nat
  | leaf => 1
  | node _ left right _ => max left.height right.height + 1

/-- Similar to [[Nat.max_le_of_le_of_le]]. -/
theorem height_le_of_le_of_le {left right : Tree α} {color a n}
  (h₁ : left.height ≤ n) (h₂ : right.height ≤ n) : (node color left right a).height ≤ n + 1 :=
  Nat.succ_le_succ (Nat.max_le_of_le_of_le h₁ h₂)

theorem height_lt_of_lt_of_lt {left right : Tree α} {color a n}
  (h₁ : left.height < n) (h₂ : right.height < n) : (node color left right a).height < n + 1 :=
  Nat.succ_lt_succ (Nat.max_lt.mpr ⟨h₁, h₂⟩)

/-!
inductive BH : Tree α → Nat → Prop
  | leaf : BH leaf 0
  | black {left right a n} : BH left n → BH right n → BH (black left right a) n.succ
  | red0 {a n} : BH leaf n → BH leaf n → BH (red leaf leaf a) n
  | red1 {left right a b n} : BH leaf n → BH (black left right a) n
    → BH (red leaf (black left right a) b) n
  | red2 {left right a b n} : BH (black left right a) n → BH leaf n
    → BH (red (black left right a) leaf b) n
  | red3 {left left' right right' a a' b n}
    : BH (black left right a) n → BH (black left' right' a') n
    → BH (red (black left right a) (black left' right' a') b) n
-/

inductive BH : Tree α → Nat → Prop
  | leaf : BH leaf 1
  | black {left right a n} : BH left n → BH right n → BH (black left right a) n.succ
  | red0 {a} : BH (red leaf leaf a) 1
  | red {left left' right right' a a' b n}
    : BH (black left right a) n → BH (black left' right' a') n
    → BH (red (black left right a) (black left' right' a') b) n

/-!
/-- `leaf.height = 0 ∧ BH leaf 1` -/
theorem half_height_le_bh : {n : Nat} → {t : Tree α} → BH t n → t.height ≤ 2 * n
  | _, _, .leaf => show 0 ≤ 2 from Nat.zero_le _
  | _, _, .red0 => show 1 ≤ 2 from Nat.le_succ _
  | .succ n, red (black left right _) (black left' right' _) _,
    .red (.black h k) (.black h' k') =>
    have h  :   left.height ≤ 2 * n := half_height_le_bh h
    have k  :  right.height ≤ 2 * n := half_height_le_bh k
    have h' :  left'.height ≤ 2 * n := half_height_le_bh h'
    have k' : right'.height ≤ 2 * n := half_height_le_bh k'
    height_le_of_le_of_le (height_le_of_le_of_le h k) (height_le_of_le_of_le h' k')
  | .succ n, black left right _, .black h k =>
    have h :  left.height ≤ 2 * n := half_height_le_bh h
    have k : right.height ≤ 2 * n := half_height_le_bh k
    (height_le_of_le_of_le h k).step

/-- `leaf.height = 0 ∧ BH leaf 1` -/
theorem half_height_le_bh {t : Tree α} {n} : BH t n → t.height ≤ 2 * n
  | .leaf => show 0 ≤ 2 from Nat.zero_le _
  | .red0 => show 1 ≤ 2 from Nat.le_succ _
  | .red (.black h k) (.black h' k') =>
    height_le_of_le_of_le
      (height_le_of_le_of_le (half_height_le_bh h ) (half_height_le_bh k ))
      (height_le_of_le_of_le (half_height_le_bh h') (half_height_le_bh k'))
  | .black h k =>
    Nat.le.step (height_le_of_le_of_le (half_height_le_bh h) (half_height_le_bh k))

/-- `leaf.height = 0 ∧ BH leaf 1` -/
theorem half_height_lt_bh {t : Tree α} {n} : BH t n → t.height < 2 * n
  | .leaf => show 0 < 2 from Nat.le_succ _
  | .red0 => show 1 < 2 from Nat.le.refl
  | .red (.black h k) (.black h' k') =>
    height_lt_of_lt_of_lt
      (height_lt_of_lt_of_lt (half_height_lt_bh h ) (half_height_lt_bh k ))
      (height_lt_of_lt_of_lt (half_height_lt_bh h') (half_height_lt_bh k'))
  | .black h k =>
    Nat.lt_succ_of_lt (height_lt_of_lt_of_lt (half_height_lt_bh h) (half_height_lt_bh k))
-/

/-- `leaf.height = 1 ∧ BH leaf 1` -/
theorem half_height_le_bh {t : Tree α} {n} : BH t n → t.height ≤ 2 * n
  | .leaf => show 1 ≤ 2 from Nat.le_succ 1
  | .red0 => show 2 ≤ 2 from .refl
  | .red (.black h k) (.black h' k') =>
    height_le_of_le_of_le
      (height_le_of_le_of_le (half_height_le_bh h ) (half_height_le_bh k ))
      (height_le_of_le_of_le (half_height_le_bh h') (half_height_le_bh k'))
  | .black h k =>
    .step (height_le_of_le_of_le (half_height_le_bh h) (half_height_le_bh k))

theorem bh_le_height {t : Tree α} {n} : BH t n → n ≤ t.height
  | .leaf => show 1 ≤ 1 from .refl
  | .red0 => show 1 ≤ 2 from Nat.le_succ 1
  | .red h _ => .step (Nat.le_max_left_of_le (bh_le_height h))
  | .black h _ => Nat.succ_le_succ (Nat.le_max_left_of_le (bh_le_height h))

theorem left_size_le {left right : Tree α} {color a}
  : left.size ≤ (node color left right a).size :=
  calc  left.size
    _ ≤ left.size + right.size := Nat.le_add_right ..
    _ ≤ left.size + right.size + 1 := Nat.le_succ _

theorem bh_size_rel : {n : Nat} → {t : Tree α} → BH t n → 2^n ≤ t.size + 1
  | _, _, .leaf => show 2^1 ≤ 1 + 1 from .refl
  | _, _, .red0 => show 2^1 ≤ 3 + 1 from (Nat.le_succ 2).step
  | .succ n, red (black left ..) (black left' ..) _, .red (.black h _) (.black h' _) =>
    calc  0 + 2^n + 2^n
      _ = 2^n + 2^n := congrArg (· + _) (Nat.zero_add _)
      _ ≤ left.size + 1 + (left'.size + 1) := Nat.add_le_add (bh_size_rel h) (bh_size_rel h')
      _ = left.size + left'.size + (1 + 1) := Nat.add_add_add_comm ..
      _ ≤ (black left ..).size + (black left' ..).size + (1 + 1) :=
        Nat.add_le_add_right (Nat.add_le_add left_size_le left_size_le) 2
      _ = (black left ..).size + (black left' ..).size + 1 + 1 := Nat.add_assoc ..
  | .succ n, black left right _, .black h k =>
    calc  0 + 2^n + 2^n
      _ = 2^n + 2^n := congrArg (· + _) (Nat.zero_add _)
      _ ≤ left.size + 1 + (right.size + 1) := Nat.add_le_add (bh_size_rel h) (bh_size_rel k)
      _ = left.size + right.size + (1 + 1) := Nat.add_add_add_comm ..
      _ = left.size + right.size + 1 + 1 := Nat.add_assoc ..

theorem height_size_rel {t : Tree α} {n} (h : BH t n) : 2^t.height ≤ t.size.succ^2 :=
  calc  2^t.height
    _ ≤ 2^(2 * n) := Nat.pow_le_pow_right (Nat.le_succ 1) (half_height_le_bh h)
    _ = (2^n)^2 := Nat.pow_mul' ..
    _ ≤ t.size.succ^2 := Nat.pow_le_pow_left (bh_size_rel h) 2

/-!
/-- Rotate left : `node c' l' (node c l r a) a' => node c (node c' l' l a') r a` -/
def rol (color' : Color) (left' : Tree α) (color : Color) (left right : Tree α) (a a' : α) : Tree α :=
  node color (node color' left' left a') right a

/-- Rotate right : `node c' (node c l r a) r' a' => node c l (node c' r r' a') a` -/
def ror (color' color : Color) (left right : Tree α) (a : α) (right' : Tree α) (a' : α) : Tree α :=
  node color left (node color' right right' a') a
-/

variable [Lt : LT α] [DecidableRel Lt.lt]

def insert (a : α) (t : Tree α) : Tree α :=
  match ins t with
  | red L@(red ..) R a
  | red L R@(red ..) a => black L R a
  | t => t
where ins : Tree α → Tree α
  | leaf => red leaf leaf a
  | t@(red L R b) =>
    if a < b then red (ins L) R b
    else if b < a then red L (ins R) b
    else t
  | t@(black L R b) =>
    if a < b then
      match ins L with
      | red (red A B x) C y
      | red A (red B C y) x => red (black A B x) (black C R b) y
      | L => black L R b
    else if b < a then
      match ins R with
      | red (red B C y) D z
      | red B (red C D z) y => red (black L B b) (black C D z) y
      | R => black L R b
    else t

end Tree

end Try2

namespace Okasaki

inductive Tree.Color
  | protected red
  | protected black

inductive Tree (α : Type)
  | leaf
  | node (color : Tree.Color) (left : Tree α) (a : α) (right : Tree α)

namespace Tree
variable {α : Type}

@[match_pattern] abbrev red := @node α Color.red
@[match_pattern] abbrev black := @node α Color.black

variable [Lt : LT α] [DecidableRel Lt.lt]

/-- Figure 3.6 -/
example (a : α) (t : Tree α) : Tree α :=
  let rec ins : Tree α → {t : Tree α // t ≠ leaf}
    | leaf => ⟨red leaf a leaf, nofun⟩
    | t@e:(node c L b R) =>
      if a < b then balance c (ins L) b R
      else if b < a then balance c L b (ins R)
      else ⟨t, e ▸ nofun⟩
  match ins t with
  | ⟨node _ L a R, _⟩ => black L a R
where balance : Color → Tree α → α → Tree α → {t : Tree α // t ≠ leaf}
  | .black, red (red A x B) y C, z, D
  | .black, red A x (red B y C), z, D
  | .black, A, x, red (red B y C) z D
  | .black, A, x, red B y (red C z D) => ⟨red (black A x B) y (black C z D), nofun⟩
  | c, L, a, R => ⟨node c L a R, nofun⟩

/-- Exercise 3.10 -/
example (a : α) (t : Tree α) : Tree α :=
  match ins t with
  | leaf => leaf -- Impossible
  -- | node _ L a R => black L a R
  | red L@(red ..) x R
  | red L x R@(red ..) => black L x R
  | t => t
where ins : Tree α → Tree α
  | leaf => red leaf a leaf
  | t@(node c L b R) =>
    if a < b then
      match c, ins L, b, R with
      | .black, red (red A x B) y C, z, D
      | .black, red A x (red B y C), z, D => red (black A x B) y (black C z D)
      | _, L, _, _ => node c L b R
    else if b < a then
      match c, L, b, ins R with
      | .black, A, x, red (red B y C) z D
      | .black, A, x, red B y (red C z D) => red (black A x B) y (black C z D)
      | _, L, _, _ => node c L b R
    else t

example (a : α) (t : Tree α) : Tree α :=
  match ins t with
  | red L@(red ..) x R
  | red L x R@(red ..) => black L x R
  | t => t
where ins : Tree α → Tree α
  | leaf => red leaf a leaf
  | t@(node c L b R) =>
    if a < b then
      match c, ins L with
      | .black, red (red A x B) y C
      | .black, red A x (red B y C) => red (black A x B) y (black C b R)
      | _, L => node c L b R
    else if b < a then
      match c, ins R with
      | .black, red (red B y C) z D
      | .black, red B y (red C z D) => red (black L b B) y (black C z D)
      | _, R => node c L b R
    else t

def insert (a : α) (t : Tree α) : Tree α :=
  match ins t with
  | red L@(red ..) x R
  | red L x R@(red ..) => black L x R
  | t => t
where ins : Tree α → Tree α
  | leaf => red leaf a leaf
  | t@(red L b R) =>
    if a < b then red (ins L) b R
    else if b < a then red L b (ins R)
    else t
  | t@(black L b R) =>
    if a < b then
      match ins L with
      | red (red A x B) y C
      | red A x (red B y C) => red (black A x B) y (black C b R)
      | L => black L b R
    else if b < a then
      match ins R with
      | red (red B y C) z D
      | red B y (red C z D) => red (black L b B) y (black C z D)
      | R => black L b R
    else t

/-
insert :: Ord a => a -> Tree a -> Tree a
insert x s = T B a y b
  where
  ins E = ((T, T), T R E x E)
  ins s@(T color a y b)
    | x < y = let (f, a') = ins a in ((llbalance, rlbalance), fst f color a' y b)
    | y < x = let (f, b') = ins b in ((lrbalance, rrbalance), snd f color a y b')
    | otherwise = ((T, T), s)
  (_, T _ a y b) = ins s

insert' Empty = (leaf v, (nobalance, nobalance))
  insert' n@(Node c l x r)
    | v < x = let (t, b) = insert' l in ((fst b) c t x r, (balancell, balancerl))
    | v > x = let (t, b) = insert' r in ((snd b) c l x t, (balancelr, balancerr))
    | otherwise = (n, (nobalance, nobalance))
-/
abbrev Cons (α) := Color → Tree α → α → Tree α → Tree α
/--
* https://github.com/rst76/pfds/blob/master/ch03/ex.3.10b.hs
* https://github.com/kgeorgiy/okasaki/blob/master/Okasaki/Chapter3/RBTree.hs
-/
example (a : α) (t : Tree α) : Tree α :=
  match (ins t).1 with
  | red L@(red ..) x R
  | red L x R@(red ..) => black L x R
  | t => t
where ins : Tree α → Tree α × Cons α × Cons α
  | leaf => ⟨red leaf a leaf, node, node⟩
  | t@(node c L b R) =>
    if a < b then
      have ⟨L, f, _⟩ := ins L
      ⟨f c L b R
      , fun | .black, red (red A x B) y C, z, D => red (black A x B) y (black C z D)
            | c, L, a, R => node c L a R
      , fun | .black, A, x, red (red B y C) z D => red (black A x B) y (black C z D)
            | c, L, a, R => node c L a R
      ⟩
    else if b < a then
      have ⟨R, _, f⟩ := ins R
      ⟨f c L b R
      , fun | .black, red A x (red B y C), z, D => red (black A x B) y (black C z D)
            | c, L, a, R => node c L a R
      , fun | .black, A, x, red B y (red C z D) => red (black A x B) y (black C z D)
            | c, L, a, R => node c L a R
      ⟩
    else ⟨t, node, node⟩

end Tree

end Okasaki


namespace Try3Inorder

inductive Tree.Color
  | protected red
  | protected black

inductive Tree (α : Type)
  | leaf
  | node (color : Tree.Color) (left : Tree α) (value : α) (right : Tree α)

namespace Tree
variable {α : Type}

@[match_pattern] abbrev red := @node α Color.red
@[match_pattern] abbrev black := @node α Color.black

instance : EmptyCollection (Tree α) where
  emptyCollection := leaf

instance : Singleton α (Tree α) where
  singleton x := red ∅ x ∅

def size : Tree α → Nat
  | leaf => 1
  | node _ A _ B => A.size + B.size + 1

def height : Tree α → Nat
  | leaf => 1
  | node _ A _ B => max A.height B.height + 1

/-- Similar to `Nat.max_le_of_le_of_le` -/
theorem height_le_of_le_of_le {A B : Tree α} {c x n}
  (h₁ : A.height ≤ n) (h₂ : B.height ≤ n) : (node c A x B).height ≤ n + 1 :=
  Nat.succ_le_succ (Nat.max_le_of_le_of_le h₁ h₂)

inductive BH : Tree α → Nat → Prop
  | leaf : BH ∅ 1
  | single {x} : BH {x} 1
  | black {A x B n} : BH A n → BH B n → BH (black A x B) n.succ
  | red {A x B y C z D n}
    : BH (black A x B) n → BH (black C z D) n
    → BH (red (black A x B) y (black C z D)) n

theorem half_height_le_bh {t : Tree α} {n} : BH t n → t.height ≤ 2 * n
  | .leaf => show 1 ≤ 2 from Nat.le_succ 1
  | .single => show 2 ≤ 2 from .refl
  | .black hA hB =>
    .step (height_le_of_le_of_le (half_height_le_bh hA) (half_height_le_bh hB))
  | .red (.black hA hB) (.black hC hD) =>
    height_le_of_le_of_le
      (height_le_of_le_of_le (half_height_le_bh hA) (half_height_le_bh hB))
      (height_le_of_le_of_le (half_height_le_bh hC) (half_height_le_bh hD))

theorem bh_le_height {t : Tree α} {n} : BH t n → n ≤ t.height
  | .leaf => show 1 ≤ 1 from .refl
  | .single => show 1 ≤ 2 from Nat.le_succ 1
  | .black h _ => Nat.succ_le_succ (Nat.le_max_left_of_le (bh_le_height h))
  | .red h _ => .step (Nat.le_max_left_of_le (bh_le_height h))

theorem left_size_le {A B : Tree α} {c x} : A.size ≤ (node c A x B).size :=
  calc  A.size
    _ ≤ A.size + B.size := Nat.le_add_right ..
    _ ≤ A.size + B.size + 1 := Nat.le_succ _

theorem bh_size_rel : {n : Nat} → {t : Tree α} → BH t n → 2^n ≤ t.size + 1
  | _, _, .leaf => show 2^1 ≤ 1 + 1 from .refl
  | _, _, .single => show 2^1 ≤ 3 + 1 from (Nat.le_succ 2).step
  | .succ n, black A _ B, .black hA hB =>
    calc  0 + 2^n + 2^n
      _ = 2^n + 2^n := congrArg (· + _) (Nat.zero_add _)
      _ ≤ A.size + 1 + (B.size + 1) := Nat.add_le_add (bh_size_rel hA) (bh_size_rel hB)
      _ = A.size + B.size + (1 + 1) := Nat.add_add_add_comm ..
      _ = A.size + B.size + 1 + 1 := Nat.add_assoc ..
  | .succ n, red (black A ..) _ (black C ..), .red (.black hA _) (.black hC _) =>
    calc  0 + 2^n + 2^n
      _ = 2^n + 2^n := congrArg (· + _) (Nat.zero_add _)
      _ ≤ A.size + 1 + (C.size + 1) := Nat.add_le_add (bh_size_rel hA) (bh_size_rel hC)
      _ = A.size + C.size + (1 + 1) := Nat.add_add_add_comm ..
      _ ≤ (black A ..).size + (black C ..).size + (1 + 1) :=
        Nat.add_le_add_right (Nat.add_le_add left_size_le left_size_le) 2
      _ = (black A ..).size + (black C ..).size + 1 + 1 := Nat.add_assoc ..

theorem height_size_rel {t : Tree α} {n} (h : BH t n) : 2^t.height ≤ t.size.succ^2 :=
  calc  2^t.height
    _ ≤ 2^(2 * n) := Nat.pow_le_pow_right (Nat.le_succ 1) (half_height_le_bh h)
    _ = (2^n)^2 := Nat.pow_mul' ..
    _ ≤ t.size.succ^2 := Nat.pow_le_pow_left (bh_size_rel h) 2

variable [Lt : LT α] [DecidableRel Lt.lt]

def insert (x : α) (t : Tree α) : Tree α :=
  match ins t with
  | red L@(red ..) x R
  | red L x R@(red ..) => black L x R
  | t => t
where ins : Tree α → Tree α
  | leaf => {x}
  | t@(red L a R) =>
    if x < a then red (ins L) a R
    else if a < x then red L a (ins R)
    else t
  | t@(black L a R) =>
    if x < a then
      match ins L with
      | red (red A x B) y C
      | red A x (red B y C) => red (black A x B) y (black C a R)
      | L => black L a R
    else if a < x then
      match ins R with
      | red (red B y C) z D
      | red B y (red C z D) => red (black L a B) y (black C z D)
      | R => black L a R
    else t

instance : Insert α (Tree α) where
  insert := insert

instance : LawfulSingleton α (Tree α) where
  insert_emptyc_eq _ := rfl

theorem ins_black_BH {L R : Tree α} {a x}
  : {n : Nat} → BH (black L a R) n → BH (insert.ins x (black L a R)) n
  | .succ n, .black hL hR =>
    let t := black L a R
    if h₁ : x < a then
      have : insert.ins x t =
        match insert.ins x L with
        | red (red A x B) y C
        | red A x (red B y C) => red (black A x B) y (black C a R)
        | L => black L a R
        := if_pos h₁
      sorry
    else if h₂ : a < x then
      have : insert.ins x t =
        match insert.ins x R with
        | red (red B y C) z D
        | red B y (red C z D) => red (black L a B) y (black C z D)
        | R => black L a R
        := trans (if_neg h₁) (if_pos h₂)
      sorry
    else
      have : insert.ins x t = t := trans (if_neg h₁) (if_neg h₂)
      sorry


theorem insert_BH {t : Tree α} {x m n} : BH t m → BH (t.insert x) n :=
  sorry

end Tree

end Try3Inorder

class TotalOrder (α) extends LT α where
  irrefl {a : α} : ¬ a < a
  -- asymm {a b : α} : a < b → a > b → False
  trans {a b c : α} : a < b → b < c → a < c
  total {a b : α} : ¬a < b → ¬b < a → a = b

namespace TotalOrder
variable {α} [self : TotalOrder α] {a b : α}

theorem asymm : a < b → ¬ a > b
  | h₁, h₂ => irrefl (trans h₁ h₂)

instance : @Trans α α α (· < ·) (· < ·) (· < ·) where
  trans := trans

section LE

instance : LE α where
  le a b := a = b ∨ a < b

theorem refl : a ≤ a := .inl rfl

instance : @Antisymm α (· ≤ ·) where
  antisymm
    | .inl rfl, _
    | _, .inl rfl => rfl
    | .inr h₁, .inr h₂ => (asymm h₁ h₂).rec

instance : @Trans α α α (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans
    | .inl rfl, h
    | h, .inl rfl => h
    | .inr h₁, .inr h₂ => .inr (trans h₁ h₂)

end LE

section Decidable
variable [decLt : DecidableRel self.lt]

instance : DecidableEq α
  | a, b =>
    match decLt a b, decLt b a with
    | isFalse h₁, isFalse h₂ => isTrue (total h₁ h₂)
    | isFalse h₁, isTrue h₂ => isFalse fun | rfl => h₁ h₂
    | isTrue h₁, isFalse h₂ => isFalse fun | rfl => h₂ h₁
    | isTrue h₁, isTrue h₂ => isFalse (asymm h₁ h₂).rec

instance (a b : α) : Decidable (a ≤ b) :=
  show Decidable (a = b ∨ a < b) from inferInstance

end Decidable

section Trichotomy

theorem not_lt_iff_ge : ¬a < b ↔ a ≥ b := sorry

theorem not_le_iff_gt : ¬a ≤ b ↔ a > b := sorry

theorem ne_iff_lt_or_gt : a ≠ b ↔ a < b ∨ a > b := sorry

theorem eq_iff_not_le_nor_gt : a = b ↔ ¬a < b ∧ ¬a > b := sorry

theorem trichotomy : a < b ∨ a = b ∨ a > b := sorry

end Trichotomy

end TotalOrder
