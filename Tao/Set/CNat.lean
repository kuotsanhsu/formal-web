inductive CNat
  | zero
  | succ (n : CNat)

namespace CNat

instance : OfNat CNat 0 where ofNat := zero

instance decEq : (m n : CNat) → Decidable (m = n)
  | 0, 0 => isTrue rfl
  | 0, succ _ | succ _, 0 => isFalse nofun -- isFalse CNat.noConfusion
  | succ m, succ n => succ.injEq m n ▸ m.decEq n

inductive le (m : CNat) : CNat → Prop
  | refl : le m m
  | step {n} : le m n → le m n.succ

instance : LE CNat where le := le

theorem zero_le : {n : CNat} → 0 ≤ n
  | 0 => le.refl
  | succ _ => zero_le.step

/-- The successor function is monotonic. -/
theorem succ_mon {m n : CNat} : m ≤ n → m.succ ≤ n.succ
  | le.refl => le.refl
  | le.step h => (succ_mon h).step
theorem pred_mon {m n : CNat} : m.succ ≤ n.succ → m ≤ n
  | le.refl => le.refl
  | le.step le.refl => le.refl.step
  | le.step h@(le.step _) => (pred_mon h).step
theorem succ.monEq (m n : CNat) : (m.succ ≤ n.succ) = (m ≤ n) :=
  propext ⟨pred_mon, succ_mon⟩

instance decLe : (m n : CNat) → Decidable (m ≤ n)
  | 0, _ => isTrue zero_le
  | succ _, 0 => isFalse nofun
  | succ m, succ n => succ.monEq m n ▸ m.decLe n

instance : LT CNat where lt m n := m.succ ≤ n

instance decLt (m n : CNat) : Decidable (m < n) := decLe m.succ n

def add (m : CNat) : CNat → CNat
  | 0 => m
  | succ n => (m.add n).succ

instance : Add CNat where add := add

example {m : CNat} : m + 0 = m := rfl
theorem zero_add : {n : CNat} → 0 + n = n := sorry

theorem le_def {m n : CNat} : m ≤ n ↔ ∃ k, m + k = n := Iff.intro
  fun | le.refl => ⟨0, rfl⟩
      | le.step h => have ⟨k, h⟩ := le_def.mp h ; ⟨k.succ, congrArg _ h⟩
  fun | ⟨0, h⟩ => trans h le.refl
      | ⟨succ k, h⟩ => match h.symm, n with | _, succ _ => (le_def.mpr ⟨k, succ.inj h⟩).step

def sub : CNat → CNat → CNat
  | 0, _ => 0
  | m, 0 => m
  | succ m, succ n => m.sub n

theorem sub_zero : {m : CNat} → m.sub 0 = m
  | 0 | succ _ => rfl

theorem le_sub_def : {m n : CNat} → m ≤ n → (n.sub m) + m = n
  | 0, 0, _ | 0, succ _, _ => rfl
  | succ _, succ _, h => congrArg _ <| le_sub_def (pred_mon h)

theorem succ_no_fixpoint : {n : CNat} → succ n ≠ n
  | succ _, h => succ_no_fixpoint (succ.inj h)

example {n : CNat} : succ n ≠ n := nofun

def mul (m : CNat) : CNat → CNat
  | 0 => 0
  | succ n => m.mul n + m
instance : Mul CNat where mul := mul

instance : OfNat CNat 1 where ofNat := succ 0
def pow (m : CNat) : CNat → CNat
  | 0 => 1
  | succ n => m.pow n * n
instance : Pow CNat CNat where pow := pow

@[default_instance] instance : OfNat CNat 2 where ofNat := succ 1

end CNat

structure CFin (bound : CNat) where
  val : CNat
  le : val < bound

def u64 := CFin (2^2^(2^2 + 2))
