/-- Unique existence: `∃! x : α, ⋯`. -/
inductive ExistsUnique {α} (p : α → Prop) : Prop
  | intro (w : α) (h : p w) (unique : ∀ {a}, p a → a = w)

section

open Lean (explicitBinders expandExplicitBinders)
open Lean.TSyntax.Compat
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b
end

theorem Classical.mtr {p q} (h : ¬p → ¬q) (hq : q) : p := byContradiction (h · hq)
