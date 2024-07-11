import Tao.Nat.Add

namespace ℕ
variable {n m a b c : ℕ}

/-- #### Definition 2.3.1 (Multiplication of natural numbers) -/
theorem mul_def : ∃ mul : ℕ → ℕ → ℕ, ∀ m, mul 0 m = 0 ∧ ∀ n, mul n++ m = (mul n m) + m :=
  suffices ∀ m, ∃ mul' : ℕ → ℕ, mul' 0 = 0 ∧ ∀ n, mul' n++ = mul' n + m
  from ⟨fun n m => (this m).choose n, fun m => (this m).choose_spec⟩
  fun m => rec (fun _ x => x + m) 0

noncomputable def mul : ℕ → ℕ → ℕ := mul_def.choose
noncomputable instance : Mul ℕ where
  mul := mul
theorem zero_mul : 0 * m = 0 := (mul_def.choose_spec m).1
theorem succ_mul : n++ * m = n * m + m := (mul_def.choose_spec m).2 n

theorem one_mul : 1 * m = m :=
  calc
    _ = 0 * m + m := succ_mul
    _ = 0 + m := congrArg (· + m) zero_mul
    _ = m := zero_add
theorem two_mul : 2 * m = m + m :=
  calc
    _ = 1 * m + m := succ_mul
    _ = m + m := congrArg (· + m) one_mul

theorem mul_zero : n * 0 = 0 :=
  suffices ∀ n, n * 0 = 0 from this n
  ind zero_mul fun n ih =>
    calc  n++ * 0
      _ = n * 0 + 0 := succ_mul
      _ = n * 0 := add_zero
      _ = 0 := ih

theorem mul_succ : n * m++ = n * m + n :=
  suffices ∀ n m, n * m + n = n * m++ from (this n m).symm
  ind (fun m =>
    calc  0 * m + 0
      _ = 0 * m := add_zero
      _ = 0 := zero_mul
      _ = 0 * m++ := zero_mul.symm
  ) fun n ih m =>
    calc  n++ * m + n++
      _ = n * m + m + n++ := congrArg (· + n++) succ_mul
      _ = n * m + (m + n++) := add_assoc
      _ = n * m + (n + m++) :=
        suffices m + n++ = n + m++ from congrArg (n * m + ·) this
        calc
          _ = (m + n)++ := add_succ
          _ = (n + m)++ := congrArg _ add_comm
          _ = n + m++ := add_succ.symm
      _ = n * m + n + m++ := add_assoc.symm
      _ = n * m++ + m++ := congrArg (· + m++) (ih m)
      _ = n++ * m++ := succ_mul.symm

/-- #### Lemma 2.3.2 (Multiplication is commutative)
#### Exercise 2.3.1
-/
theorem mul_comm : n * m = m * n :=
  suffices ∀ n, n * m = m * n from this n
  ind (
    calc  0 * m
      _ = 0 := zero_mul
      _ = m * 0 := mul_zero.symm
  ) fun n ih =>
    calc  n++ * m
      _ = n * m + m := succ_mul
      _ = m * n + m := congrArg (· + m) ih
      _ = m * n++ := mul_succ.symm

/-- #### Lemma 2.3.3 (Positive natural numbers have no zero divisors)
#### Exercise 2.3.2
-/
theorem eq_zero_iff_mul_eq_zero : n * m = 0 ↔ n = 0 ∨ m = 0 :=
  .intro (
    suffices ∀ n m, n * m = 0 → n = 0 ∨ m = 0 from this n m
    ind (fun _ _ => show 0 = 0 ∨ _ from .inl rfl) fun n _ m (h : n++ * m = 0) =>
      show _ ∨ m = 0 from
      suffices m = 0 from .inr this
      suffices n * m + m = 0 from (eq_zero_of_add_eq_zero this).2
      calc
        _ = n++ * m := succ_mul.symm
        _ = 0 := h
  ) fun
    | .inl (e : n = 0) =>
      calc  n * m
        _ = 0 * m := congrArg (· * m) e
        _ = 0 := zero_mul
    | .inr (e : m = 0) =>
      calc  n * m
        _ = n * 0 := congrArg _ e
        _ = 0 := mul_zero
theorem pos_of_mul_pos : n ≠ 0 → m ≠ 0 → n * m ≠ 0 :=
  fun (hn : n ≠ 0) (hm : m ≠ 0) (h : n * m = 0) => show False from
    suffices n = 0 ∨ m = 0 from this.rec hn hm
    eq_zero_iff_mul_eq_zero.mp h

/-- #### Proposition2.3.4 (Distributive law) -/
theorem mul_add : a * (b + c) = a * b + a * c :=
  suffices ∀ a, a * (b + c) = a * b + a * c from this a
  ind (
    suffices 0 * b + 0 * c = 0 * (b + c) from this.symm
    calc
      _ = 0 * b + 0 := congrArg _ zero_mul
      _ = 0 * b := add_zero
      _ = 0 := zero_mul
      _ = 0 * (b + c) := zero_mul.symm
  ) fun a ih =>
    suffices a++ * b + a++ * c = a++ * (b + c) from this.symm
    calc
      _ = a++ * b + (a * c + c) := congrArg _ succ_mul
      _ = a * b + b + (a * c + c) := congrArg (· + _) succ_mul
      _ = (a * b + b + a * c) + c := add_assoc.symm
      _ = (a * b + a * c + b) + c :=
        suffices a * b + b + a * c = a * b + a * c + b from congrArg (· + c) this
        calc
          _ = a * b + (b + a * c) := add_assoc
          _ = a * b + (a * c + b) := congrArg _ add_comm
          _ = a * b + a * c + b := add_assoc.symm
      _ = a * b + a * c + (b + c) := add_assoc
      _ = a * (b + c) + (b + c) := congrArg (· + _) ih.symm
      _ = a++ * (b + c) := succ_mul.symm
theorem add_mul : (b + c) * a = b * a + c * a :=
  calc
    _ = a * (b + c) := mul_comm
    _ = a * b + a * c := mul_add
    _ = b * a + a * c := congrArg (· + a * c) mul_comm
    _ = b * a + c * a := congrArg _ mul_comm

/-- #### Proposition2.3.5 (Multiplicationisassociative)
#### Exercise 2.3.3
-/
theorem mul_assoc : a * b * c = a * (b * c) :=
  suffices ∀ a, a * b * c = a * (b * c) from this a
  ind (
    calc  0 * b * c
      _ = 0 * c := congrArg (· * c) zero_mul
      _ = 0 := zero_mul
      _ = 0 * (b * c) := zero_mul.symm
  ) fun a ih =>
    calc  a++ * b * c
      _ = (a * b + b) * c := congrArg (· * c) succ_mul
      _ = a * b * c + b * c := add_mul
      _ = a * (b * c) + b * c := congrArg (· + _) ih
      _ = a++ * (b * c) := succ_mul.symm

/-- #### Proposition 2.3.6 (Multiplication preserves order) -/
theorem lt_mul_pos (pos : c ≠ 0) : a < b → a * c < b * c :=
  fun h : a < b =>
    have ⟨⟨d, (hd : d ≠ 0)⟩, (e : b = a + d)⟩ := lt_iff_add_pos.mp h
    suffices ∃ D : Pos, b * c = a * c + D from lt_iff_add_pos.mpr this
    have :=
      calc  b * c
        _ = (a + d) * c := congrArg (· * c) e
        _ = a * c + d * c := add_mul
    ⟨⟨_, pos_of_mul_pos hd pos⟩, this⟩

/-- #### Corollary2.3.7 (Cancellationlaw) -/
theorem mul_cancel (pos : c ≠ 0) : a * c = b * c → a = b :=
  fun (e : a * c = b * c) =>
    match order_trichotomy a b with
    | .inl (h : a < b) =>
      suffices a * c ≠ b * c from (this e).rec
      suffices a * c < b * c from have ⟨ne, _⟩ := this ; ne
      lt_mul_pos pos h
    | .inr (.inl (h : a = b)) => h
    | .inr (.inr (h : a > b)) =>
      suffices a * c ≠ b * c from (this e).rec
      suffices a * c > b * c from have ⟨ne, _⟩ := this ; ne.symm
      lt_mul_pos pos h

/-- #### Proposition 2.3.9 (Euclid’s division lemma)
#### Exercise 2.3.5
-/
theorem Euclid_div (n : ℕ) (q : Pos) : ∃ m r : ℕ, 0 ≤ r ∧ r < q ∧ n = m * q + r :=
  have ⟨q, (pos : q ≠ 0)⟩ := q
  suffices ∀ n, ∃ m r : ℕ, 0 ≤ r ∧ r < q ∧ n = m * q + r from this n
  have pos : 0 < q := ⟨pos.symm, _, zero_add⟩
  ind (show ∃ m r : ℕ, 0 ≤ r ∧ r < q ∧ 0 = m * q + r from
    suffices 0 * q + 0 = 0 from ⟨0, 0, order_rfl, pos, this.symm⟩
    calc
      _ = 0 * q := add_zero
      _ = 0 := zero_mul
  ) fun n ⟨m, r, _, (hrq : r < q), (e : n = m * q + r)⟩ =>
    show ∃ m r : ℕ, 0 ≤ r ∧ r < q ∧ n++ = m * q + r from
    have e' :=
      calc  (n++)
        _ = (m * q + r)++ := congrArg _ e
        _ = m * q + r++ := add_succ.symm
    match lt_or_eq_of_le (lt_iff_succ_le.mp hrq : r++ ≤ q) with
    | .inl (h : r++ < q) => ⟨m, r++, ⟨_, zero_add⟩, h, e'⟩
    | .inr (h : r++ = q) =>
      suffices m++ * q + 0 = n++ from ⟨m++, 0, order_rfl, pos, this.symm⟩
      calc
        _ = m++ * q := add_zero
        _ = m * q + q := succ_mul
        _ = m * q + r++ := congrArg _ h.symm
        _ = n++ := e'.symm
where lt_or_eq_of_le {a b : ℕ} : a ≤ b → a < b ∨ a = b :=
  fun ⟨x, (hx : a + x = b)⟩ =>
    match order_trichotomy a b with
    | .inl (h : a < b) => .inl h
    | .inr (.inl (h : a = b)) => .inr h
    | .inr (.inr ⟨(ne : b ≠ a), y, (hy : b + y = a)⟩) =>
      suffices b = a from (ne this).rec
      suffices x = 0 from
        calc  b
          _ = a + x := hx.symm
          _ = a + 0 := congrArg _ this
          _ = a := add_zero
      suffices x + y = 0 from (eq_zero_of_add_eq_zero this).1
      suffices a + (x + y) = a + 0 from cancel_add this
      calc
        _ = (a + x) + y := add_assoc.symm
        _ = b + y := congrArg (· + y) hx
        _ = a := hy
        _ = a + 0 := add_zero.symm

/-- #### Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem pow_def : ∃ pow : ℕ → ℕ → ℕ, ∀ m, pow m 0 = 1 ∧ ∀ n, pow m n++ = pow m n * m :=
  suffices ∀ m, ∃ pow' : ℕ → ℕ, pow' 0 = 1 ∧ ∀ n, pow' n++ = pow' n * m
  from Classical.axiomOfChoice this
  fun m => rec (fun _ x => x * m) 1

noncomputable def pow : ℕ → ℕ → ℕ := pow_def.choose
noncomputable instance : Pow ℕ ℕ where
  pow := pow
theorem pow_zero : m^0 = 1 := (pow_def.choose_spec m).1
theorem pow_succ : m^n++ = m^n * m := (pow_def.choose_spec m).2 n

example : 0^0 = 1 := pow_zero
theorem pow_one : m^1 = m :=
  calc
    _ = m^0 * m := pow_succ
    _ = 1 * m := congrArg (· * m) pow_zero
    _ = m := one_mul
postfix:arg "²" => (·^2)
theorem pow_two : m² = m * m :=
  calc
    _ = m^1 * m := pow_succ
    _ = m * m := congrArg (· * m) pow_one
example :=
  calc  m^3
    _ = m^2 * m := pow_succ
    _ = m * m * m := congrArg (· * m) pow_two

/-- #### Exercise 2.3.4 -/
example : (a + b)² = a² + 2 * a * b + b² :=
  calc
    _ = (a + b) * (a + b) := pow_two
    _ = a * (a + b) + b * (a + b) := add_mul
    _ = (a² + a * b) + _ :=
      suffices a * (a + b) = a² + a * b from congrArg (· + _) this
      calc
        _ = a * a + a * b := mul_add
        _ = a² + _ := congrArg (· + _) pow_two.symm
    _ = _ + (a * b + b²) :=
      suffices b * (a + b) = a * b + b² from congrArg _ this
      calc
        _ = b * a + b * b := mul_add
        _ = _ + b² := congrArg _ pow_two.symm
        _ = a * b + _ := congrArg (· + _) mul_comm
    _ = (_ + _ + _) + _ := add_assoc.symm
    _ = _ + (_ + _) + _ := congrArg (· + _) add_assoc
    _ = _ + 2 * a * b + _ :=
      suffices 2 * a * b = a * b + a * b from congrArg (_ + · + _) this.symm
      calc
        _ = 2 * (a * b) := mul_assoc
        _ = (a * b) + a * b := two_mul

end ℕ
