import Tao.Int

protected instance ℚ.setoid : Setoid (ℤ × (d : ℤ) ×' d ≠ (0 : ℕ)) where
  r | ⟨a, b, _⟩, ⟨c, d, _⟩ => a * d = c * b
  iseqv.refl | ⟨a, b, _ ⟩ => show a * b = a * b from rfl
  iseqv.symm {x y} h :=
    match x, y, h with
    | ⟨a, b, _⟩, ⟨c, d, _⟩, (h : a * d = c * b) => show c * b = a * d from h.symm
  iseqv.trans {x y z} h k :=
    match x, y, z, h, k with
    | ⟨a, b, _⟩, ⟨c, d, hd⟩, ⟨e, f, _⟩, (h : a * d = c * b), (k : c * f = e * d) =>
      show a * f = e * b from
      Classical.byCases (fun hc : c = 0 =>
        have ha : a = 0 := sorry
        have he : e = 0 := sorry
        calc  a * f
          _ = 0 * f := congrArg _ ha
          _ = 0 := ℤ.rig.zero_l
          _ = 0 * b := ℤ.rig.zero_l.symm
          _ = e * b := congrArg (· * _) he.symm
      ) fun hc : c ≠ 0 =>
        suffices a * f * c = e * b * c from ℤ.mul_cancel hc this
        suffices _ * d = _ * d from ℤ.mul_cancel hd this
        ℤ.mul.setoid_helper h k

def ℚ : Type := Quotient ℚ.setoid
namespace ℚ

noncomputable instance : Coe ℤ ℚ where
  coe a := .mk' ⟨a, 1, ℤ.rig.one_ne_zero⟩

@[default_instance] noncomputable instance {n} : OfNat ℚ n where
  ofNat := ℕ.ofNat n

noncomputable instance : Add ℚ where
  add := Quotient.lift₂ (fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ =>
    suffices b * d ≠ 0 from .mk' ⟨a * d + c * b, b * d, this⟩
    -- fun e : b * d = .mk' (0, 0) => show False from
      -- have ⟨x, (hx : .mk' x = b * d)⟩ := Quotient.exists_rep (b * d)
      -- have : x ≈ (0, 0) := Quotient.exact (trans hx e)
      -- have ⟨y, (hy : .mk' y = b)⟩ := Quotient.exists_rep b
      -- have ⟨z, (hz : .mk' z = d)⟩ := Quotient.exists_rep d
      -- have : (.mk' y : ℤ) * (.mk' z : ℤ) = Quotient.mk' (0, 0) := hy ▸ hz ▸ e
      -- _
    -- Quotient.inductionOn₂ b d fun
    -- | (x, y), (x', y'), (h : .mk' (x * x' + y * y', x * y' + y * x') = zero) => show False from
    --   have : x * x' + y * y' + 0 = 0 + (x * y' + y * x') := Quotient.exact h
    --   sorry
    sorry
  ) sorry

noncomputable instance : Mul ℚ where
  mul := Quotient.lift₂ (fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ =>
    let zero := .mk' (0, 0)
    suffices b * d ≠ zero from .mk' ⟨a * c, b * d, this⟩
    sorry
  ) sorry

noncomputable instance : Neg ℚ where
  neg := Quotient.lift (fun ⟨a, b, hb⟩ => .mk' ⟨-a, b, hb⟩) sorry
noncomputable instance : Sub ℚ where
  sub x y := x + (-y)

noncomputable instance : Coe ℤ ℚ where
  coe n := .mk' ⟨n, (1 : ℕ), sorry⟩
noncomputable instance : Coe ℕ ℚ where
  coe n := ℚ.instCoeℤ.coe (ℤ.instCoeℕ.coe n)

noncomputable instance : HDiv ℤ {n : ℤ // n ≠ (0 : ℕ)} ℤ where
  hDiv | m, ⟨n, hn⟩ => sorry

noncomputable instance : LE ℚ := sorry
noncomputable instance : LT ℚ := sorry
noncomputable instance : AbsoluteValue ℚ ℚ := sorry

#check Int.natAbs

/-
## Extra
-/
section
variable {a b c x y : ℚ}

-- theorem no_zero_divisor : a ≠ 0 ∧ b ≠ 0 ↔ a * b ≠ 0 := sorry
theorem cancel_mul (pos : x ≠ 0) : x * a = x * b → a = b := sorry
theorem mul_cancel (pos : y ≠ 0) : a * y = b * y → a = b := sorry

noncomputable def add : CommMonoid ℚ where
  op a b := a + b
  assoc := sorry
  comm := sorry
  unit := 0
  unit_l := sorry

noncomputable def mul : CommMonoid ℚ where
  op a b := a * b
  assoc := sorry
  comm := sorry
  unit := 1
  unit_l := sorry

theorem rig : CommSemiring add mul where
  zero_l := sorry
  dist_l := sorry
  one_ne_zero (h : 1 = 0) : False := ℤ.rig.one_ne_zero <|
    calc  1
      _ = 1 * 1 := ℤ.mul.unit_l.symm
      _ = 0 * 1 := Quotient.exact h
      _ = 0 := ℤ.rig.zero_l

end

end ℚ
