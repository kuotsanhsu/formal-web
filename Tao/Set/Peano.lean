class Peano.{u} (ω : Type u) where
  zero : ω
  succ : ω → ω
  succ_ne_zero {a : ω} : succ a ≠ zero
  succ_inj {a b : ω} : succ a = succ b → a = b
  ind {P : ω → Prop} : P zero → (∀ a, P a → P (succ a)) → ∀ a, P a

namespace Peano
universe u v
variable {ω : Type u} [Peano ω]

local postfix:arg "++" => succ
local macro_rules
  | `($x ++) => `(unop% Peano.succ $x)

-- local instance encode (n : Nat) : OfNat ω n where
--   ofNat := n.rec zero fun _ => succ
-- local instance encode (n : Nat) : OfNat ω n where
--   ofNat := match n with | 0 => zero | n+1 => (encode n).ofNat
local instance encode : (n : Nat) → OfNat ω n
  | 0 => OfNat.mk zero
  | n+1 => OfNat.mk (encode n).ofNat++
@[app_unexpander Peano.zero]
def zero.unexpand : Lean.PrettyPrinter.Unexpander
  | _ => `(0)

-- def ind' {P : ω → Prop} (a : ω) (zero : P 0) (succ : ∀ a, P a → P a++) : P a :=
--   ind zero succ a

/-- Completeness -/
theorem zero_or_succ : ∀ a : ω, a = 0 ∨ ∃ b, b++ = a :=
  ind (show 0 = 0 ∨ _ from .inl rfl) fun a _ => show _ ∨ ∃ b, b++ = a++ from .inr ⟨a, rfl⟩

theorem ne_succ_self : ∀ a : ω, a++ ≠ a :=
  ind succ_ne_zero fun a ih (h : a++ ++ = a++)=> ih <| show a++ = a from succ_inj h

theorem zero_em : ∀ a : ω, a = 0 ∨ a ≠ 0 :=
  ind (show 0 = 0 ∨ _ from .inl rfl) fun a _ => show _ ∨ a++ ≠ 0 from .inr succ_ne_zero

theorem eq_em : ∀ a b : ω, a = b ∨ a ≠ b :=
  -- ind (zero_em a) fun b ih => show a = b++ ∨ a ≠ b++ from
  --   ih.rec (fun h : a = b => suffices a ≠ b++ from .inr this
  --     fun e : a = b++ => suffices b++ = b from ne_succ_self b this
  --       trans e.symm h
  --   ) fun h : a ≠ b => show a = b++ ∨ a ≠ b++ from
  --     _
  ind (fun b => show 0 = b ∨ 0 ≠ b from (zero_em b).imp Eq.symm Ne.symm) fun a ih =>
    ind (show _ ∨ a++ ≠ 0 from .inr succ_ne_zero ) fun b (ih' : a++ = b ∨ a++ ≠ b) =>
      show a++ = b++ ∨ a++ ≠ b++ from
      sorry

#check Nat.decEq
example : ∀ a : ω, ∃ n, (encode n).ofNat = a :=
  ind ⟨0, rfl⟩ fun a ⟨n, (ih : (encode n).ofNat = a)⟩ =>
    suffices (encode (n+1)).ofNat = a++ from ⟨n+1, this⟩
    show (OfNat.mk (encode n).ofNat++).ofNat = (OfNat.mk a++).ofNat from
    congrArg (fun x => (OfNat.mk x++).ofNat) ih

-- instance decEq (a : ω) : ∀ b, Decidable (a = b) :=
--   ind (show Decidable (a = 0) from
--     sorry
--   ) fun b ih => show Decidable (a = b++) from
--     ih.rec (fun h : ¬a = b => show Decidable (a = b++) from _
--     ) fun h : a = b => isFalse _

end Peano
