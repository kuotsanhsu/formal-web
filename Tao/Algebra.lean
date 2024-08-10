/-
The bibliography of this Wikipedia entry is exceptional:
[Special classes of semigroups](https://en.wikipedia.org/wiki/Special_classes_of_semigroups)
-/

class Magma (α) where
  /-- A binary operator. -/
  op : α → α → α

-- local instance {α} [self : Magma α] : Mul α where
--   mul := self.op
@[inherit_doc] local infixl:70 " ⊙ "   => Magma.op
-- macro_rules | `($x ⊙ $y) => `(binop% Magma.op $x $y)

class Semigroup (α) extends Magma α where
  assoc {a b c : α} : a ⊙ b ⊙ c = a ⊙ (b ⊙ c)

class CommSemigroup (α) extends Semigroup α where
  comm {a b : α} : a ⊙ b = b ⊙ a

class CommMonoid (α) extends CommSemigroup α where
  unit : α
  unit_l {a} : unit ⊙ a = a
  unit_r {a} : a ⊙ unit = a := trans comm unit_l

@[app_unexpander CommMonoid.unit]
def CommMonoid.unit.unexpand : Lean.PrettyPrinter.Unexpander
  | _ => `(1)

local instance {α} [self : CommMonoid α] : OfNat α 1 where
  ofNat := self.unit

-- local instance {α} {self : CommSemigroup α} : Magma α where
--   op := self.op
-- local instance {α} {self : CommMonoid α} : Magma α where
--   op := self.op

namespace Semigroup
variable {α} [Semigroup α] {a b c d a' b' c' d' : α}

/-
theorem assoc4 : a ⊙ b ⊙ c ⊙ d = a ⊙ (b ⊙ c ⊙ d) :=
  calc  a ⊙ b ⊙ c ⊙ d
    _ = a ⊙ b ⊙ (c ⊙ d) := assoc
    _ = a ⊙ (b ⊙ (c ⊙ d)) := assoc
    _ = a ⊙ (b ⊙ c ⊙ d) := congrArg _ assoc.symm
-/
theorem congr4 (h : a ⊙ b = a' ⊙ b') (k : c ⊙ d = c' ⊙ d')
  : a ⊙ b ⊙ c ⊙ d = a' ⊙ b' ⊙ c' ⊙ d' :=
  calc  a  ⊙ b  ⊙  c  ⊙ d
    _ =         _           := assoc
    _ = a' ⊙ b' ⊙     _     := congrArg (· ⊙ _) h
    _ =    _    ⊙ (c' ⊙ d') := congrArg _ k
    _ =         _           := assoc.symm

end Semigroup

namespace CommSemigroup
open Semigroup
variable {α} [self : CommSemigroup α] {a b c d e f : α}

theorem comm3_12 : a ⊙ b ⊙ c = b ⊙ a ⊙ c := congrArg (· ⊙ c) comm
theorem comm3_23 : a ⊙ b ⊙ c = a ⊙ c ⊙ b :=
  calc
    _ = a ⊙ (b ⊙ c) := assoc
    _ = a ⊙ (c ⊙ b) := congrArg _ comm
    _ =   _         := assoc.symm
theorem comm3_13 : a ⊙ b ⊙ c = c ⊙ b ⊙ a := trans (trans comm3_12 comm3_23) comm3_12

theorem comm4_12 : a ⊙ b ⊙ c ⊙ d = b ⊙ a ⊙ c ⊙ d := congrArg (· ⊙ d) comm3_12
theorem comm4_13 : a ⊙ b ⊙ c ⊙ d = c ⊙ b ⊙ a ⊙ d := congrArg (· ⊙ d) comm3_13
theorem comm4_23 : a ⊙ b ⊙ c ⊙ d = a ⊙ c ⊙ b ⊙ d := congrArg (· ⊙ d) comm3_23
theorem comm4_34 : a ⊙ b ⊙ c ⊙ d = a ⊙ b ⊙ d ⊙ c :=
  calc
    _ = _ ⊙ (c ⊙ d) := assoc
    _ = _ ⊙ (d ⊙ c) := congrArg _ comm
    _ =   _         := assoc.symm
theorem comm4_14 : a ⊙ b ⊙ c ⊙ d = d ⊙ b ⊙ c ⊙ a := trans (trans comm4_13 comm4_34) comm4_13
theorem comm4_24 : a ⊙ b ⊙ c ⊙ d = a ⊙ d ⊙ c ⊙ b := trans (trans comm4_23 comm4_34) comm4_23

theorem setoid_helper (h : a ⊙ d = c ⊙ b) (k : c ⊙ f = e ⊙ d)
  : a ⊙ f ⊙ c ⊙ d = e ⊙ b ⊙ c ⊙ d :=
  calc  _ ⊙ f ⊙ _ ⊙ d
    _ = a ⊙ d ⊙ c ⊙ f := comm4_24
    _ = c ⊙ b ⊙ e ⊙ d := congr4 h k
    _ = e ⊙ _ ⊙ c ⊙ _ := comm4_13

end CommSemigroup

/-
structure UnitalMagma (α) extends Magma α where
  unit : α
  unit_l {a} : unit ⊙ a = a
  unit_r {a} : a ⊙ unit = a

structure Quasigroup (α) extends Magma α where
  div_l {x a b : α} : x ⊙ a = x ⊙ b → a = b
  div_r {a b y : α} : a ⊙ y = b ⊙ y → a = b

structure Monoid (α) extends Semigroup α, UnitalMagma α
structure Loop (α) extends Quasigroup α, UnitalMagma α
structure AssocQuasigroup (α) extends Semigroup α, Quasigroup α
structure Group (α) extends Semigroup α, Quasigroup α, UnitalMagma α


-- local instance {α} {self : CommSemigroup α} : Magma α where
--   op := self.op
-- local instance {α} {self : CommMonoid α} : Magma α where
--   op := self.op

section
variable {α} (self : CommMonoid α)

example : self.unit ⊙ 1 = self.unit := sorry
example : self.toMagma = self.toUnital.toMagma := rfl
example : self.toMagma = self.toCommSemigroup.toMagma := rfl

end

-/
