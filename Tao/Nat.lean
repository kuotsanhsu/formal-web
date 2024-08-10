import Tao.Nat.Peano
import Tao.Nat.Add
import Tao.Nat.Mul

/-
## Extra
https://en.wikipedia.org/wiki/Semiring
-/

import Tao.Algebra

class CommSemiring {α} (add mul : CommMonoid α) : Prop where
  zero_l {a} : mul.op add.unit a = add.unit
  zero_r {a} : mul.op a add.unit = add.unit := trans mul.comm zero_l
  dist_l {x a b} : mul.op x (add.op a b) = add.op (mul.op x a) (mul.op x b)
  dist_r {a b y} : mul.op (add.op a b) y = add.op (mul.op a y) (mul.op b y) :=
    calc  mul.op (add.op a b) y
      _ = mul.op y (add.op a b) := mul.comm
      _ = add.op (mul.op y a) (mul.op y b) := dist_l
      _ = add.op _            (mul.op b y) := congrArg _ mul.comm
      _ = add.op (mul.op a y) _            := congrArg (add.op · _) mul.comm
  /-- Categorical requirement: https://math.stackexchange.com/a/30241 -/
  one_ne_zero : mul.unit ≠ add.unit

namespace ℕ

theorem add_cancel {a b y : ℕ} (h : a + y = b + y) : a = b :=
  suffices y + a = y + b from cancel_add this
  calc  y + a
    _ = a + y := add_comm
    _ = b + y := h
    _ = y + b := add_comm

noncomputable instance add : CommMonoid ℕ where
  op a b := a + b
  assoc := add_assoc
  comm := add_comm
  unit := 0
  unit_l := zero_add

noncomputable instance mul : CommMonoid ℕ where
  op a b := a * b
  assoc := mul_assoc
  comm := mul_comm
  unit := 1
  unit_l := one_mul

theorem rig : CommSemiring add mul where
  zero_l := zero_mul
  dist_l := mul_add
  one_ne_zero := succ_ne_zero 0

end ℕ
