import Tao.Rat

noncomputable instance ℝ.setoid : Setoid (ℕ → ℚ) where
  r x y := ∀ ε : ℚ, ε > (0 : ℕ) → ∃ N : ℕ, ∀ n > N, |x n - y n| < ε
  iseqv := sorry
