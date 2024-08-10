mutual
  inductive Tree (α)
    | ofRed (tree : Red α)
    | ofBlack (tree : Black α)
  inductive Red (α)
    | red (left right : Black α) (a : α)
  inductive Black (α)
    | leaf
    | node (left right : Tree α) (a : α)
end

namespace Tree
universe u
variable {α : Sort u}

instance : Coe (Red α) (Tree α) where coe := ofRed
instance : Coe (Black α) (Tree α) where coe := ofBlack

export Red (red)
export Black (leaf node)

/-
@[match_pattern] abbrev leaf : Tree α := @Black.leaf α
@[match_pattern] abbrev red (left right : Black α) (a : α) : Tree α := Red.red left right a
@[match_pattern] abbrev node (left right : Tree α) (a : α) : Tree α := Black.node left right a

abbrev height : Tree α → Nat
  | leaf => 0
  | red left right _ => max (height <| ofBlack left) (height <| ofBlack right) + 1
  | node left right _ => max (height left) (height right) + 1

inductive BH : Tree α → Nat → Prop
  | leaf : BH leaf 0
  | red {left right : Black α} {a n} : BH left n → BH right n → BH (red left right a) n
  | node {left right a n} : BH left n → BH right n → BH (node left right a) n.succ

theorem half_height_le_bh {t : Tree α} {n} : BH t n → height t ≤ 2 * n
  | .leaf => .refl
  | .red (left := left) (right := right) h₁ h₂ =>
    have k₁ : height left ≤ 2 * n := half_height_le_bh h₁
    calc  (red left right _).height
      _ = max (height (ofBlack left)) (height (ofBlack right)) + 1 := rfl
      _ ≤ 2 * n := sorry
  | .node h₁ h₂ => sorry
-/
end Tree
variable {α}

mutual
  def Tree.height : Tree α → Nat
    | .ofRed tree
    | .ofBlack tree => tree.height
  def Red.height : Red α → Nat
    | .red left right _ => max left.height right.height + 1
  def Black.height : Black α → Nat
    | .leaf => 0
    | .node left right _ => max left.height right.height + 1
end

namespace Tree

example {t : Black α} : height (ofBlack t) = Black.height t := rfl

inductive BH : Tree α → Nat → Prop
  | leaf : BH (@leaf α) 0
  | red {left right : Black α} {a n} : BH left n → BH right n → BH (red left right a) n
  | node {left right a n} : BH left n → BH right n → BH (node left right a) n.succ

theorem half_height_le_bh {n} : {t : Tree α} → BH t n → t.height ≤ 2 * n
  | @leaf α, .leaf => .refl
  | @red α left right _, .red h₁ h₂ =>
    have k₁ : height left ≤ 2 * n := half_height_le_bh h₁
    calc  (red left right _).height
      _ = max (height (ofBlack left)) (height (ofBlack right)) + 1 := rfl
      _ ≤ 2 * n := sorry
  | @node α left right _, .node h₁ h₂ => sorry

end Tree
