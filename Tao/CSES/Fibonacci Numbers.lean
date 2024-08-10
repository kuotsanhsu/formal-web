/-!
* https://www.nayuki.io/page/fast-fibonacci-algorithms
* https://www.nayuki.io/page/karatsuba-multiplication
* https://en.wikipedia.org/wiki/Strassen_algorithm
-/

inductive Fib : Nat → Nat → Prop
  | zero : Fib 0 0
  | one : Fib 1 1
  | succ {n a b} : Fib n a → Fib (n + 1) b → Fib (n + 2) (a + b)

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_def {n} : Fib n (fib n) := sorry

theorem Fib_func {n a b} : Fib n a → Fib n b → a = b
  | .zero, .zero => rfl
  | .one, .one => rfl
  | .succ h₁ h₁', .succ h₂ h₂' =>
    match Fib_func h₁ h₂, Fib_func h₁' h₂' with
    | rfl, rfl => rfl

instance {n} : Subsingleton (Subtype (Fib n)) where
  allEq | ⟨_, ha⟩, ⟨_, hb⟩ => Fib_func ha hb ▸ rfl
          -- match ha, hb, Fib_func ha hb with | _, _, rfl => rfl

theorem Fib_fib {n a} : Fib n a ↔ fib n = a := ⟨Fib_func fib_def, Eq.ndrec fib_def⟩

instance (n a) : Decidable (Fib n a) := propext Fib_fib ▸ (fib n).decEq a
  -- ((fib n).decEq a).rec
  --   fun | hn => isFalse <| hn ∘ Fib_func fib_def
  --   fun | rfl => isTrue fib_def
  -- if e : fib n = a then isTrue (e ▸ fib_def) else isFalse (e ∘ Fib_func fib_def)

class inductive DecFib (fib : Nat → Nat) : Nat → Nat → Prop
  | zero : DecFib fib (fib 0) 0
  | one : DecFib fib (fib 1) 1
  | succ {n a b} : DecFib fib (fib n) a → DecFib fib (fib (n + 1)) b
    → DecFib fib (fib (n + 2)) (a + b)

class FibDef (fib : Nat → Nat) where
  zero : 0 = fib 0 := by exact rfl
  one : 1 = fib 1 := by exact rfl
  succ {n} : fib n + fib (n + 1) = fib (n + 2) := by exact rfl

instance : FibDef fib where

def fib2 (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [:n] do
    let c := a + b
    a := b
    b := c
  return a

def fib3 (n : Nat) : Nat := Id.run do
  let mut A := ((0, 1), (1, 1))
  let mut F := ((1, 0), (0, 1))
  let mut m := n
  while m != 0 do
    if m % 2 == 1 then F := mul F A
    m := m / 2
    A := mul A A
  return F.1.2
where mul (A B : (Nat × Nat) × (Nat × Nat)) : (Nat × Nat) × (Nat × Nat) :=
  let u := (A.1.1 * B.1.1 + A.1.2 * B.2.1, A.1.1 * B.1.2 + A.1.2 * B.2.2)
  let v := (A.2.1 * B.1.1 + A.2.2 * B.2.1, A.2.1 * B.1.2 + A.2.2 * B.2.2)
  (u, v)

def fib4 (n : Nat) : Nat :=
  (f n).1
where f : Nat → Nat × Nat
  | 0 => (0, 1)
  | m@(.succ _) =>
    let (a, b) := f (m / 2)
    if m % 2 == 0 then
      (a * (2 * b - a), a * a + b * b)
    else
      (a * a + b * b, (2 * a + b) * b)
    /-
    let c := a * (b - a + b)
    let d := a * a + b * b
    if m % 2 == 0 then (c, d) else (d, c + d)
    -/

namespace Try1

abbrev Mat₂₂ := Nat × Nat × Nat × Nat

def naive : Mat₂₂ → Mat₂₂ → Mat₂₂
  | (A₁₁, A₁₂, A₂₁, A₂₂), (B₁₁, B₁₂, B₂₁, B₂₂) =>
    (
      A₁₁ * B₁₁ + A₁₂ * B₂₁, A₁₁ * B₁₂ + A₁₂ * B₂₂,
      A₂₁ * B₁₁ + A₂₂ * B₂₁, A₂₁ * B₁₂ + A₂₂ * B₂₂,
    )

def Strassen : Mat₂₂ → Mat₂₂ → Mat₂₂
  | (A₁₁, A₁₂, A₂₁, A₂₂), (B₁₁, B₁₂, B₂₁, B₂₂) =>
    let M₁ := (A₁₁ + A₂₂) * (B₁₁ + B₂₂)
    let M₂ := (A₂₁ + A₂₂) * B₁₁
    let M₃ := A₁₁ * (B₁₂ - B₂₂)
    let M₄ := A₂₂ * (B₂₁ - B₁₁)
    let M₅ := (A₁₁ + A₁₂) * B₂₂
    let M₆ := (A₂₁ - A₁₁) * (B₁₁ + B₁₂)
    let M₇ := (A₁₂ - A₂₂) * (B₂₁ + B₂₂)
    (M₁ + M₄ - M₅ + M₇, M₃ + M₅, M₂ + M₄, M₁ - M₂ + M₃ + M₆)

def Winogard : Mat₂₂ → Mat₂₂ → Mat₂₂
  | (a, b, c, d), (A, B, C, D) =>
    let t := a * A
    let u := (c - a) * (C - D)
    let v := (c + d) * (C - A)
    let w := t + (c + d - a) * (A + D - C)
    (
      t + b * B, w + v + (a + b - c - d) * D,
      w + u + d * (B + C - A - D), w + u + v
    )

end Try1
