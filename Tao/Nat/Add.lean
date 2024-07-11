import Tao.Nat.Peano

namespace ℕ

theorem add_def : ∃ add : ℕ → ℕ → ℕ, ∀ m, add 0 m = m ∧ ∀ n, add n++ m = (add n m)++ :=
  suffices ∀ m, ∃ add' : ℕ → ℕ, add' 0 = m ∧ ∀ n, add' n++ = (add' n)++
  from ⟨fun n m => (this m).choose n, fun m => (this m).choose_spec⟩
  rec _

noncomputable def add : ℕ → ℕ → ℕ := add_def.choose
noncomputable instance : Add ℕ where
  add := add

variable {n m : ℕ}

theorem zero_add : 0 + m = m := (add_def.choose_spec m).1
theorem succ_add : n++ + m = (n + m)++ := (add_def.choose_spec m).2 n

/-- #### Lemma 2.2.2
For any natural number `n`, `n + 0 = n`.
-/
theorem add_zero : n + 0 = n :=
  suffices ∀ n, n + 0 = n from this n
  ind zero_add fun n ih =>
    calc n++ + 0
     _ = (n + 0)++ := succ_add
     _ = n++ := congrArg _ ih

/-- #### Lemma2.2.3
For any natural numbers `n` and `m`, `n + (m++) = (n + m)++`.
-/
theorem add_succ : n + m++ = (n + m)++ :=
  suffices ∀ n, n + m++ = (n + m)++ from this n
  ind (
    calc  0 + m++
      _ = m++ := zero_add
      _ = (0 + m)++ := congrArg _ zero_add.symm
  ) fun n ih =>
    calc  n++ + m++
      _ = (n + m++)++ := succ_add
      _ = (n + m)++ ++ := congrArg _ ih
      _ = (n++ + m)++ := congrArg _ succ_add.symm

/--
As a particular corollary of Lemma 2.2.2 and Lemma 2.2.3 we see that `n++` = `n + 1`.
-/
theorem succ_eq_add_one : n++ = n + 1 :=
  suffices n + 1 = n++ from this.symm
  calc  n + 0++
    _ = (n + 0)++ := add_succ
    _ = n++ := congrArg _ add_zero

/-- #### Proposition 2.2.4 : Addition is commutative
For any natural numbers `n` and `m`, `n + m = m + n`.
-/
theorem add_comm : n + m = m + n :=
  suffices ∀ n, n + m = m + n from this n
  ind (
    calc  0 + m
      _ = m := zero_add
      _ = m + 0 := add_zero.symm
  ) fun n ih =>
    calc n++ + m
      _ = (n + m)++ := succ_add
      _ = (m + n)++ := congrArg _ ih
      _ = m + n++ := add_succ.symm


variable {a b c : ℕ}

/-- #### Proposition 2.2.5 : Addition is associative
For any natural numbers `a`, `b`, `c`, we have `(a + b) + c = a + (b + c)`.

#### Exercise 2.2.1
-/
theorem add_assoc : a + b + c = a + (b + c) :=
  suffices ∀ a, a + b + c = a + (b + c) from this a
  ind (
    calc  0 + b + c
      _ = b + c := congrArg (· + c) zero_add
      _ = 0 + (b + c) := zero_add.symm
  ) fun a ih =>
    calc  a++ + b + c
      _ = (a + b)++ + c := congrArg (· + c) succ_add
      _ = (a + b + c)++ := succ_add
      _ = (a + (b + c))++ := congrArg _ ih
      _ = a++ + (b + c) := succ_add.symm

/-- #### Proposition2.2.6 : Cancellation law
Let `a`, `b`, `c` be natural numbers such that `a + b = a + c`. Then we have `b = c`.
-/
theorem cancel_add : a + b = a + c → b = c :=
  suffices ∀ a, a + b = a + c → b = c from this a
  ind (fun (h : 0 + b = 0 + c) =>
    calc  b
      _ = 0 + b := zero_add.symm
      _ = 0 + c := h
      _ = c := zero_add
  ) fun a ih (h : a++ + b = a++ + c) =>
    suffices a + b = a + c from ih this
    suffices (a + b)++ = (a + c)++ from succ.inj this
    calc
      _ = a++ + b := succ_add.symm
      _ = a++ + c := h
      _ = (a + c)++ := succ_add

/-- #### Definition 2.2.7 : Positive natural numbers
A natural number `n` is said to be positive iff it is not equal to `0`.
-/
abbrev Pos := Subtype (· ≠ 0)

/-- #### Proposition 2.2.8
If `a` is a positive natural number, and `b` is a natural number, then `a + b` is
positive (and hence `b + a` is also, by Proposition 2.2.4).
-/
theorem pos_add (pos : a ≠ 0) : a + b ≠ 0 :=
  suffices ∀ b, a + b ≠ 0 from this b
  ind (
    calc  a + 0
      _ = a := add_zero
      _ ≠ 0 := pos
  ) fun b _ =>
    calc  a + b++
      _ = (a + b)++ := add_succ
      _ ≠ 0 := succ_ne_zero _

/-- #### Corollary 2.2.9
If `a` and `b` are natural numbers such that `a + b = 0`, then `a = 0` and `b = 0`.
-/
theorem eq_zero_of_add_eq_zero : a + b = 0 → a = 0 ∧ b = 0 :=
  Classical.mtr fun hn : ¬(a = 0 ∧ b = 0) => show a + b ≠ 0 from
    have : a ≠ 0 ∨ b ≠ 0 := Classical.not_and_iff_or_not_not.mp hn
    this.rec pos_add fun pos : b ≠ 0 =>
      calc  a + b
        _ = b + a := add_comm
        _ ≠ 0 := pos_add pos

/-- #### Lemma 2.2.10
Let `a` be a positive number. Then there exists exactly one natural number `b` such
that `b++ = a`.

#### Exercise 2.2.2
-/
theorem uniq_succ : a ≠ 0 → ∃! b, b++ = a :=
  suffices ∀ a, a ≠ 0 → ∃! b, b++ = a from this a
  ind (absurd rfl) fun a _ _ => show ∃! b, b++ = a++ from ⟨a, rfl, succ.inj⟩

/-- #### Definition 2.2.11 : Ordering of the natural numbers
Let `n` and `m` be natural numbers. We say that `n` is greater than or equal to
`m`, and write `n ≥ m` or `m ≤ n`, iff we have `n = m + a` for some natural number
`a`. We say that `n` is strictly greater than `m`, and write `n > m` or `m < n`,
iff `n ≥ m` and `n ≠ m`.
-/
instance : LE ℕ where
  le m n := ∃ a, m + a = n
instance : LT ℕ where
  lt m n := m ≠ n ∧ m ≤ n

/- #### Proposition 2.2.12 : Basic properties of order for natural numbers
Let `a`, `b`, `c` be natural numbers. Then
(a) (Order is reflexive) `a ≥ a`.
(b) (Order is transitive) If `a ≥ b` and `b ≥ c`, then `a ≥ c`.
(c) (Order is antisymmetric) If `a ≥ b` and `b ≥ a`, then `a = b`.
(d) (Addition preserves order) `a ≥ b` if and only if `a + c ≥ b + c`.
(e) `a < b` if and only if `a++ ≤ b`.
(f) `a < b` if and only if `b = a + d` for some positive number `d`.

#### Exercise 2.2.3
-/
theorem order_rfl : a ≥ a := show ∃ x, a + x = a from ⟨0, a.add_zero⟩
theorem order_trans : a ≥ b ∧ b ≥ c → a ≥ c :=
  fun ⟨⟨x, (hx : b + x = a)⟩, ⟨y, (hy : c + y = b)⟩⟩ =>
    suffices c + (x + y) = a from ⟨x + y, this⟩
    calc
      _ = c + (y + x) := congrArg _ add_comm
      _ = (c + y) + x := add_assoc.symm
      _ = b + x := congrArg (· + x) hy
      _ = a := hx
theorem order_antisymm : a ≥ b ∧ b ≥ a → a = b :=
  fun ⟨⟨x, (hx : b + x = a)⟩, ⟨y, (hy : a + y = b)⟩⟩ =>
    calc  a
      _ = a + 0 := add_zero.symm
      _ = a + y :=
        suffices y = 0 from congrArg _ this.symm
        suffices x + y = 0 from (eq_zero_of_add_eq_zero this).2
        suffices b + (x + y) = b + 0 from cancel_add this
        calc
          _ = b + x + y := add_assoc.symm
          _ = a + y := congrArg (· + y) hx
          _ = b := hy
          _ = b + 0 := add_zero.symm
      _ = b := hy
theorem order_congr_add : a ≥ b ↔ a + c ≥ b + c :=
  .intro (fun ⟨x, (hx : b + x = a)⟩ =>
    suffices b + c + x = a + c from ⟨_, this⟩
    calc
      _ = b + (c + x) := add_assoc
      _ = b + (x + c) := congrArg _ add_comm
      _ = (b + x) + c := add_assoc.symm
      _ = a + c := congrArg (· + c) hx
  ) fun ⟨x, (hx : b + c + x = a + c)⟩ =>
    suffices b + x = a from ⟨_, this⟩
    suffices c + (b + x) = c + a from cancel_add this
    calc
      _ = c + b + x := add_assoc.symm
      _ = b + c + x := congrArg (· + x) add_comm
      _ = a + c := hx
      _ = c + a := add_comm
theorem lt_iff_succ_le : a < b ↔ a++ ≤ b :=
  .intro (fun ⟨(ne : a ≠ b), x, (hx : a + x = b)⟩ =>
    show ∃ y, a++ + y = b from
    suffices ∃ y, y++ = x from
      have ⟨y, (h : y++ = x)⟩ := this
      suffices a++ + y = b from ⟨_, this⟩
      calc
        _ = (a + y)++ := succ_add
        _ = a + y++ := add_succ.symm
        _ = a + x := congrArg _ h
        _ = b := hx
    suffices 0 ≠ x from have ⟨y, (hy : y++ = x), _⟩ := uniq_succ this.symm ; ⟨y, hy⟩
    fun | rfl => show False from
      suffices a = b from ne this
      calc  a
        _ = a + 0 := add_zero.symm
        _ = b := hx
  ) fun ⟨x, (hx : a++ + x = b)⟩ =>
    suffices h : a + x++ = b from
      suffices a ≠ b from ⟨this, _, h⟩
      fun | rfl => show False from
        suffices x++ = 0 from succ_ne_zero _ this
        suffices a + x++ = a + 0 from cancel_add this
        calc
          _ = a := h
          _ = a + 0 := add_zero.symm
    calc
      _ = (a + x)++ := add_succ
      _ = a++ + x := succ_add.symm
      _ = b := hx
theorem lt_iff_add_pos : a < b ↔ ∃ d : Pos, b = a + d :=
  .intro (fun h : a < b =>
    have ⟨x, (hx : a++ + x = b)⟩ := lt_iff_succ_le.mp h
    suffices b = a + x++ from ⟨⟨_, succ_ne_zero _⟩, this⟩
    calc
      _ = a++ + x := hx.symm
      _ = (a + x)++ := succ_add
      _ = a + x++ := add_succ.symm
  ) fun ⟨⟨d, (pos : d ≠ 0)⟩, (h : b = a + d)⟩ =>
    suffices a++ ≤ b from lt_iff_succ_le.mpr this
    have ⟨x, (e : x++ = d), _⟩ := uniq_succ pos
    suffices a++ + x = b from ⟨_, this⟩
    calc
      _ = (a + x)++ := succ_add
      _ = a + x++ := add_succ.symm
      _ = a + d := congrArg _ e
      _ = b := h.symm

/-- #### Proposition 2.2.13 : Trichotomy of order for natural numbers
Let `a` and `b` be natural numbers. Then exactly one of the following statements
is true: `a < b`, `a = b`, or `a > b`.

#### Exercise 2.2.4
-/
theorem order_trichotomy : ∀ a b : ℕ, a < b ∨ a = b ∨ a > b := sorry

/-- #### Proposition 2.2.14 : Strong principle of induction
Let `m₀` be a natural number, and let `P m` be a property pertaining to an arbitrary
natural number `m`. Suppose that for each `m ≥ m₀`, we have the following implication:
if `P m'` is true for all natural numbers `m₀ ≤ m' < m`, then `P m` is also true.
(In particular, this means that `P m₀` is true, since in this case the hypothesis
is vacuous.) Then we can conclude that `P m` is true for all natural numbers `m ≥ m₀`.

#### Exercise 2.2.5
-/
theorem strongInd (m₀ : ℕ) {P : ℕ → Prop}
  (h : ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) : ∀ m, m ≥ m₀ → P m
:=
  fun m hm => show P m from
    suffices ∀ m m', m₀ ≤ m' ∧ m' < m → P m' from h m hm (this m)
    ind (fun m' ⟨_, (ne : m' ≠ 0), _, (hx : m' + _ = 0)⟩ =>
      suffices m' = 0 from (ne this).rec ; (eq_zero_of_add_eq_zero hx).1
    ) fun m ih m' (k : m₀ ≤ m' ∧ m' < m++) => show P m' from
      match Classical.em (m' = m) with
      | .inl (e : m' = m) =>
        suffices P m from e ▸ this
        suffices m₀ ≤ m from h m this ih ; e ▸ k.1
      | .inr (ne : m' ≠ m) =>
        suffices m₀ ≤ m' ∧ m' < m from ih _ this
        suffices m' ≤ m from ⟨k.1, ne, this⟩
        suffices m' + 1 ≤ m + 1 from order_congr_add.mpr this
        calc
          _ = m'++ := succ_eq_add_one.symm
          _ ≤ m++ := lt_iff_succ_le.mp k.2
          _ = m + 1 := succ_eq_add_one

/-- #### Exercise 2.2.6
Let `n` be a natural number, and let `P m` be a property pertaining to the natural
numbers such that whenever `P m++` is true, then `P m` is true. Suppose that `P n`
is also true. Prove that `P m` is true for all natural numbers `m ≤ n`; this is
known as the principle of backwards induction. (Hint: apply induction to the variable
`n`.)
-/
theorem backwardInd (n : ℕ) {P : ℕ → Prop} (h : ∀ m, P m++ → P m) : P n → ∀ m, m ≤ n → P m :=
  suffices ∀ n, P n → ∀ m, m ≤ n → P m from this n
  ind (fun (k : P 0) m ⟨_, (hx : m + _ = 0)⟩ => show P m from
    suffices m = 0 from this ▸ k ; (eq_zero_of_add_eq_zero hx).1
  ) fun n ih (k : P n++) m ⟨x, (hx : m + x = n++)⟩ => show P m from
    match Classical.em (x = 0) with
    | .inl (e : x = 0) =>
      suffices n++ = m from this ▸ k
      calc
        _ = m + x := hx.symm
        _ = m + 0 := congrArg _ e
        _ = m := add_zero
    | .inr (pos : x ≠ 0) =>
      suffices m ≤ n from ih (h _ k) m this
      have ⟨y, (hy : y++ = x), _⟩ := uniq_succ pos
      suffices (m + y)++ = n++ from ⟨_, succ.inj this⟩
      calc
        _ = m + y++ := add_succ.symm
        _ = m + x := congrArg _ hy
        _ = n++ := hx

/-- #### Exercise 2.2.7
Let `n` be a natural number, and let `P m` be a property pertaining to the natural
numbers such that whenever `P m` is true, `P m++` is true. Show that if `P n` is true,
then `P m` is true for all `m ≥ n`. (This principle is sometimes referred to as
the principle of induction starting from the base case `n`.)
-/
theorem forwardInd (n : ℕ) {P : ℕ → Prop} (h : ∀ m, P m → P m++) : P n → ∀ m, m ≥ n → P m :=
  fun (k : P n) m ⟨x, (hx : n + x = m)⟩ => show P m from
    suffices ∀ y, P (n + y) from hx ▸ this x
    ind (show P (n + 0) from add_zero.symm.rec k) fun y ih => show P (n + y++) from
      suffices P (n + y)++ from add_succ.symm.rec this ; h _ ih

end ℕ
