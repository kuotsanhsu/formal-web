/-- Unique existence: `∃! x : α, ⋯`. -/
inductive ExistsUnique {α} (p : α → Prop) : Prop
  | intro (w : α) (h : p w) (unique : ∀ {a}, p a → a = w)

abbrev ExistsAtMostOne {α} [HasEquiv α] (p : α → Prop) : Prop := ∀ x, p x → ∀ a, p a → a ≈ x

section
open Lean (explicitBinders expandExplicitBinders)
open Lean.TSyntax.Compat

macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b
@[app_unexpander ExistsUnique]
def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($_ fun $x:ident => $b)                      => `(∃! $x:ident, $b)
  | `($_ fun ($x:ident : $t) => $b)               => `(∃! ($x:ident : $t), $b)
  | _ => throw ()

macro "∃?" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsAtMostOne xs b
@[app_unexpander ExistsAtMostOne]
def unexpandExistsAtMostOne : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => ∃? $xs:binderIdent*, $b) => `(∃? $x:ident $xs:binderIdent*, $b)
  | `($_ fun $x:ident => $b)                      => `(∃? $x:ident, $b)
  | `($_ fun ($x:ident : $t) => $b)               => `(∃? ($x:ident : $t), $b)
  | _ => throw ()

end

section «Test ExistsAtMostOne notation»

local instance : Setoid Nat where
  r a b := a = b
  iseqv.refl _ := rfl
  iseqv.symm := Eq.symm
  iseqv.trans | rfl, rfl => rfl

example
  (h : ∃? x : Nat, x = 0)
     : ∃? (x : Nat), x = 0 :=
  show ∀ x, x = 0 → ∀ a, a = 0 → a = x from h

example
  (h : ∃? x y : Nat, x = 0 ∧ y = 0)
     : ∃? (x : Nat) (y : Nat), x = 0 ∧ y = 0 :=
  show ∃? x y, x = 0 ∧ y = 0 from
  show ∃? x, ∃? y, x = 0 ∧ y = 0 from
  show ∃? x, ∀ y, x = 0 ∧ y = 0 → ∀ b, x = 0 ∧ b = 0 → b = y from
  show ∀ x, (∀ y, x = 0 ∧ y = 0 → ∀ b, x = 0 ∧ b = 0 → b = y)
    → ∀ a, ((∀ y, a = 0 ∧ y = 0 → ∀ b, a = 0 ∧ b = 0 → b = y)) → a = x from h

end «Test ExistsAtMostOne notation»

theorem Classical.mtr {p q} (h : ¬p → ¬q) (hq : q) : p := byContradiction (h · hq)

/-- Following the definition of `∉`. -/
notation:50 a:50 " ≉ " b:50 => ¬ (a ≈ b)
theorem Setoid.rfl {α} [Setoid α] {a : α} : a ≈ a := refl a

@[inherit_doc Sep.sep]
macro "{ " a:ident " ∈ " c:term " | " b:term " }" : term => ``(Sep.sep (fun $a => $b) $c)
/-- FIXME: https://github.com/leanprover/lean4/issues/465 -/
@[app_unexpander Sep.sep]
def unexpandSep : Lean.PrettyPrinter.Unexpander
  | `($_ (fun $a:ident => $b) $c)
  | `($_ (fun ($a:ident : $_)=> $b) $c)  => `({ $a ∈ $c | $b })
  | _ => throw ()

class Powerset (α : Type _) where
  /-- Powerset: `𝒫 A`  -/
  powerset : α → α
@[inherit_doc] prefix:75 "𝒫 " => Powerset.powerset


class AbsoluteValue (α : Sort _) (β : Sort _) where
  /-- Absolute value: `|x|` -/
  abs : α → β
@[inherit_doc AbsoluteValue.abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(AbsoluteValue.abs $a)
/-- Unexpander for the notation `|a|` for `abs a`.
Tries to add discretionary parentheses in unparseable cases. -/
@[app_unexpander AbsoluteValue.abs]
def unexpandAbs : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()
