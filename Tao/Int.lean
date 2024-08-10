import Tao.Nat

protected instance ℤ.setoid : Setoid (ℕ × ℕ) where
  r | (a, b), (c, d) => a + d = c + b
  iseqv.refl | (a, b) => show a + b = a + b from rfl
  iseqv.symm {a b} (h : a.1 + b.2 = b.1 + a.2) := show b.1 + a.2 = a.1 + b.2 from h.symm
  iseqv.trans {x y z} h k :=
    match x, y, z, h, k with
    | ⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, (h : a + d = c + b), (k : c + f = e + d) =>
      show a + f = e + b from
      suffices _ + c = _ + c from ℕ.add_cancel this
      suffices _ + d = _ + d from ℕ.add_cancel this
      ℕ.add.setoid_helper h k

/-- #### Definition 4.1.1 (Integers) -/
def ℤ : Type := Quotient ℤ.setoid
namespace ℤ

noncomputable instance : Coe ℕ ℤ where
  coe a := .mk' ⟨a, 0⟩

@[default_instance] noncomputable instance {n} : OfNat ℤ n where
  ofNat := ℕ.ofNat n

/-- #### Definition 4.1.2 -/
noncomputable instance : Add ℤ where
  add := Quotient.lift₂ (fun ⟨a, b⟩ ⟨c, d⟩ => .mk' ⟨a + c, b + d⟩) fun
    | ⟨a, b⟩, ⟨c, d⟩, ⟨a', b'⟩, ⟨c', d'⟩, (h : a + b' = a' + b), (k : c + d' = c' + d) =>
      suffices (a + c, b + d) ≈ (a' + c', b' + d') from Quotient.sound this
      calc  a + c + (b' + d')
        _ = a + c + b' + d' := ℕ.add.assoc.symm
        _ = a + b' + c + d' := ℕ.add.comm4_23
        _ = a' + b + c' + d := ℕ.add.congr4 h k
        _ = a' + c' + b + d := ℕ.add.comm4_23
        _ = a' + c' + (b + d) := ℕ.add.assoc

/-- #### Definition 4.1.2
`(a - b)(c - d) = ac - ad - bc + bd = (ac + bd) - (ad + cb)`
-/
noncomputable instance : Mul ℤ where
  mul := Quotient.lift₂ (fun ⟨a, b⟩ ⟨c, d⟩ => .mk' ⟨a * c + b * d, a * d + c * b⟩) fun
    | ⟨a, b⟩, ⟨c, d⟩, ⟨a', b'⟩, ⟨c', d'⟩, (h : a + b' = a' + b), (k : c + d' = c' + d) =>
      suffices (a * c + b * d, a * d + c * b)
        ≈ (a' * c' + b' * d', a' * d' + c' * b') from Quotient.sound this

      have : a * c + b' * d' + (a * d' + c * b') = a' * c' + b * d + (a' * d + c' * b) := sorry
      calc  a * c + b * d + (a' * d' + c' * b')
        _ = a' * c' + b' * d' + (a * d + c * b) := sorry

noncomputable instance : Neg ℤ where
  neg := Quotient.lift (fun (a, b) => Quotient.mk' (b, a)) fun
    | (a, b), (c, d), (h : a + d = c + b) =>
      suffices (b, a) ≈ (d, c) from Quotient.sound this
      calc  b + c
        _ = c + b := ℕ.add_comm
        _ = a + d := h.symm
        _ = d + a := ℕ.add_comm

noncomputable instance : Sub ℤ where
  sub m n := m + (-n)

/-
## Extra
-/
section
variable {a b c x y : ℤ}

-- theorem no_zero_divisor : a ≠ 0 ∧ b ≠ 0 ↔ a * b ≠ 0 := sorry
theorem cancel_mul (pos : x ≠ 0) : x * a = x * b → a = b := sorry
theorem mul_cancel (pos : y ≠ 0) : a * y = b * y → a = b := sorry

noncomputable def add : CommMonoid ℤ where
  op a b := a + b
  assoc := sorry
  comm := sorry
  unit := 0
  unit_l := sorry

noncomputable def mul : CommMonoid ℤ where
  op a b := a * b
  assoc := sorry
  comm := sorry
  unit := 1
  unit_l := sorry

theorem rig : CommSemiring add mul where
  zero_l := sorry
  dist_l := sorry
  one_ne_zero (h : 1 = 0) : False := ℕ.rig.one_ne_zero <|
    calc  1
      _ = 1 + 0 := ℕ.add_zero.symm
      _ = 0 + 0 := Quotient.exact h
      _ = 0 := ℕ.zero_add

end

end ℤ
