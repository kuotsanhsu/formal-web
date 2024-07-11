import Tao.Logic

/-- #### Assumption 2.6
There exists a number system `ℕ`, whose elements we will call natural numbers, for
which Axioms 2.1–2.5 are true.
-/
axiom ℕ : Type
namespace ℕ

/-- #### Axiom 2.1
`0` is a natural number.
-/
axiom zero : ℕ

/-- #### Axiom 2.2
If `n` is a natural number, then `n++` is also a natural number.
-/
axiom succ : ℕ → ℕ
postfix:arg "++" => succ
noncomputable def ofNat : Nat → ℕ
  | 0 => zero
  | n+1 => (ofNat n)++
@[default_instance] noncomputable instance {n} : OfNat ℕ n where
  ofNat := ofNat n
/-- #### Proposition 2.1.4
`3` is a natural number.
-/
noncomputable example : ℕ := 3

/-- #### Axiom 2.3
`0` is not the successor of any natural number; i.e., we have `n++ ≠ 0` for every
natural number `n`.
-/
axiom succ_ne_zero (n : ℕ) : n++ ≠ 0
/-- #### Proposition 2.1.6
`4` is not equal to `0`.
-/
theorem four_ne_zero : 4 ≠ 0 := succ_ne_zero 3

/-- #### Axiom 2.4
Different natural numbers must have different successors; i.e., if `n`, `m` are
natural numbers and `n ≠ m`, then `n++ ≠ m++`. Equivalently, if `n++ = m++` then
we must have `n = m`.
-/
axiom succ.inj {n m : ℕ} : n++ = m++ → n = m
/-- #### Proposition 2.1.8
`6` is not equal to `2`.
-/
example : 6 ≠ 2 :=
  fun h : 6 = 2 => show False from
    suffices 4 = 0 from four_ne_zero this
    suffices 5 = 1 from succ.inj this
    succ.inj h

/-- #### Axiom 2.5 : Principle of mathematical induction
Let `P n` be any property pertaining to a natural number `n`. Suppose that `P 0`
is true, and suppose that whenever `P n` is true, `P n++` is also true. Then `P n`
is true for every natural number `n`.
-/
axiom ind {P : ℕ → Prop} (zero : P 0) (succ : ∀ n, P n → P n++) : ∀ n, P n
/-- #### Proposition 2.1.16 : Recursive definitions
Suppose for each natural number `n`, we have some function `fₙ : ℕ → ℕ` from the
natural numbers to the natural numbers. Let `c` be a natural number. Then we can
assign a unique natural number `aₙ` to each natural number `n`, such that `a₀ = c`
and `aₙ₊₊ = fₙ aₙ` for each natural number `n`. -/
theorem rec (f : ℕ → ℕ → ℕ) (c : ℕ) : ∃ a : ℕ → ℕ, a 0 = c ∧ ∀ n, a n++ = f n (a n) :=
  sorry

end ℕ
