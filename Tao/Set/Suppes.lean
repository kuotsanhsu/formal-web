import Tao.Logic

/-
# Pure Set Theory (PST)
Since PST requires objects to be sets, `2 ∪ 3` is a valid expression contrary to
Remark 3.1.13. However, Tao doesn't mandate PST, and this opens the possibility
to render `2 ∪ 3` insensible, which is more reasonable.

#### Remark 3.1.13
While the operation of union has some similarities with addition, the two operations
are not identical. For instance, `{2} ∪ {3} ≈ {2, 3}` and `2 + 3 ≈ 5`, whereas
`{2} + {3}` is meaningless (addition pertains to numbers, not sets) and `2 ∪ 3`
is also meaningless (union pertains to sets, not numbers).

NOTE: must use `≈` instead of `=`; otherwise, equality becomes trivial.

* https://math.stackexchange.com/questions/3508498/why-do-we-allow-redundant-axioms-in-zfc
* https://math.stackexchange.com/questions/2343272/minimum-number-of-axioms-for-zfc-set-theory

-/

axiom Set : Type
namespace Set

axiom Mem : Set → Set → Prop
instance : Membership Set Set where
  mem := Set.Mem

instance : Setoid Set where
  r A B := ∀ x, x ∈ A ↔ x ∈ B
  iseqv.refl _ _ := Iff.rfl
  iseqv.symm h x := (h x).symm
  iseqv.trans h₁ h₂ x := trans (h₁ x) (h₂ x)

/-
axiom extensionality {x y A : Set} : x ≈ y → (x ∈ A ↔ y ∈ A)
axiom sum (A : Set) : ∃ B : Set, ∀ x, x ∈ B ↔ ∃ a ∈ A, x ∈ a
axiom powerset (A : Set) : ∃ B : Set, ∀ a, (∀ x ∈ a, x ∈ A) → a ∈ B
axiom regularity {A : Set} (h : ∃ x, x ∈ A) : ∃ a ∈ A, ∀ x ∈ A, x ∉ a
axiom infinity : ∃ N : Set, (∃ n ∈ N, ∀ x, x ∉ n) ∧
  ∀ m ∈ N, ∃ n ∈ N, ∀ x, x ∈ n ↔ x ∈ N ∨ x ≈ m
axiom replacement {P : Set → Set → Prop} (A : Set) (h : ∀ x ∈ A, ∃? y, P x y)
  : ∃ B : Set, ∀ y, y ∈ B ↔ ∃ x ∈ A, P x y
-/

instance : Trans (· ≈ ·) (· ≈ ·) (· ≈ · : Set → Set → Prop) where
  trans := Setoid.trans
instance : Trans (· ∈ ·) (· ≈ ·) (· ∈ · : Set → Set → Prop) where
  trans {x A B} (h₁ : x ∈ A) (h₂ : A ≈ B) := show x ∈ B from (h₂ x).mp h₁

@[default_instance] instance : HasSubset Set where
  Subset A B := ∀ x ∈ A, x ∈ B
theorem subset_rfl {A : Set} : A ⊆ A := fun _ => id
theorem subset_antisymm {A B : Set} : A ⊆ B → B ⊆ A → A ≈ B := fun h₁ h₂ x => ⟨h₁ x, h₂ x⟩

/-
## Axiom of Extensionality
-/

axiom extensionality {x y A : Set} : x ≈ y → (x ∈ A ↔ y ∈ A)
instance : Trans (· ≈ ·) (· ∈ ·) (· ∈ · : Set → Set → Prop) where
  trans {a b A} (h₁ : a ≈ b) (h₂ : b ∈ A) := show a ∈ A from (extensionality h₁).mpr h₂

/-
## Axiom Schema of Replacement
-/

axiom replacement {P : Set → Set → Prop} (A : Set) (h : ∀ x ∈ A, ∃? y, P x y)
  : ∃ B : Set, ∀ y, y ∈ B ↔ ∃ x ∈ A, P x y
theorem specification {P : Set → Prop} (A : Set) : ∃ B : Set, ∀ y, y ∈ B ↔ y ∈ A ∧ P y :=
  have ⟨B, (h : ∀ y, y ∈ B ↔ ∃ x ∈ A, x ≈ y ∧ P y)⟩ :=
    replacement A <|
      show ∀ x ∈ A, ∃? y, x ≈ y ∧ P y from
      show ∀ x ∈ A, ∀ y, x ≈ y ∧ P y → ∀ z, x ≈ z ∧ P z → z ≈ y from
      fun x _ y ⟨(hy : x ≈ y), _⟩ z ⟨(hz : x ≈ z), _⟩ => trans (Setoid.symm hz) hy
  Exists.intro B fun y => show y ∈ B ↔ y ∈ A ∧ P y from
    suffices (∃ x, x ∈ A ∧ x ≈ y ∧ P y) ↔ y ∈ A ∧ P y from trans (h y) this
    Iff.intro
      fun | ⟨x, (hx : x ∈ A), (e : x ≈ y), (h : P y)⟩ => ⟨(extensionality e).mp hx, h⟩
      fun | ⟨(hy : y ∈ A), (h : P y)⟩ => ⟨y, hy, Setoid.rfl, h⟩
@[default_instance] noncomputable instance : Sep Set Set where
  sep P A := (@specification P A).choose
section
variable {P : Set → Prop} {x y A B : Set}

theorem spec_def : y ∈ {x ∈ A | P x} ↔ y ∈ A ∧ P y := (specification A).choose_spec y
theorem spec_same : {x ∈ A | P x} ⊆ A := fun _ h => (spec_def.mp h).1
theorem spec_congr : A ≈ B → {x ∈ A | P x} ≈ {x ∈ B | P x} :=
  fun h y => (iff_congr spec_def spec_def).mpr (and_congr_left' (h y))

end

noncomputable instance : Inter Set where
  inter A B := {x ∈ A | x ∈ B}
theorem inter_def {x A B : Set} : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := spec_def

/-
## Axiom of Infinity
-/

axiom infinity : ∃ N : Set, (∃ n ∈ N, ∀ x, x ∉ n) ∧
    ∀ m ∈ N, ∃ n ∈ N, ∀ x, x ∈ n ↔ x ∈ m ∨ x ≈ m
@[default_instance] noncomputable local instance : Inhabited Set where
  default := infinity.choose

@[default_instance] noncomputable instance : EmptyCollection Set where
  emptyCollection := {x ∈ default | False}
theorem not_in_empty {x : Set} : x ∉ ∅ := And.right ∘ spec_def.mp

theorem empty_subset {A : Set} : ∅ ⊆ A := fun x (h : x ∈ ∅) => (not_in_empty h).rec
theorem empty_of_subset_empty {A : Set} (h : A ⊆ ∅) : A ≈ ∅ :=
  fun x => show x ∈ A ↔ x ∈ ∅ from ⟨h x, (absurd · not_in_empty)⟩
theorem unique_empty {A} : A ≈ ∅ ↔ ∀ x, x ∉ A :=
  Iff.intro
    fun | (h : ∀ x, x ∈ A ↔ x ∈ ∅), x, (k : x ∈ A) => not_in_empty ((h x).mp k)
    fun | (h : ∀ x, x ∉ A), x => iff_of_false (h x) not_in_empty
theorem single_choice {A} (h : A ≉ ∅) : ∃ x, x ∈ A :=
  suffices ¬∀ x, x ∉ A from Classical.not_forall_not.mp this
  unique_empty.subst h

/-
## Power Set Axiom
-/

axiom powerset (A : Set) : ∃ B : Set, ∀ a, a ⊆ A ↔ a ∈ B
noncomputable instance : Powerset Set where
  powerset A := (powerset A).choose
theorem powerset_def {A B : Set} : A ⊆ B ↔ A ∈ 𝒫 B := (powerset B).choose_spec A

theorem self_in_pow_self {A : Set} : A ∈ 𝒫 A := powerset_def.mp subset_rfl
theorem empty_ne_one (h : ∅ ≈ 𝒫 ∅) : False :=
  not_in_empty <|
    calc  ∅
      _ ∈ 𝒫 ∅ := powerset_def.mp empty_subset
      _ ≈ ∅ := Setoid.symm h
theorem eq_empty_of_in_one {x} (h : x ∈ 𝒫 ∅) : x ≈ ∅ :=
  suffices x ⊆ ∅ from empty_of_subset_empty this
  powerset_def.mpr h
theorem eq_empty_or_eq_one_of_subset_one {A : Set} (h : A ⊆ 𝒫 ∅) : A ≈ ∅ ∨ A ≈ 𝒫 ∅ :=
  Classical.byCases .inl fun ne : A ≉ ∅ => show _ ∨ A ≈ 𝒫 ∅ from
    suffices 𝒫 ∅ ⊆ A from .inr (subset_antisymm h this)
    fun x (hx : x ∈ 𝒫 ∅) => show x ∈ A from
      have ⟨y, (hy : y ∈ A)⟩ := single_choice ne
      calc  x
        _ ≈ ∅ := eq_empty_of_in_one hx
        _ ≈ y := Setoid.symm <| show y ≈ ∅ from eq_empty_of_in_one (h y hy)
        _ ∈ A := hy

theorem pairing (a b : Set) : ∃ A : Set, a ∈ A ∧ b ∈ A ∧ ∀ x ∈ A, x ≈ a ∨ x ≈ b :=
  let A := 𝒫 𝒫 ∅
  have hA {x : Set} (h : x ∈ A) : x ≈ ∅ ∨ x ≈ 𝒫 ∅ :=
    suffices x ⊆ 𝒫 ∅ from eq_empty_or_eq_one_of_subset_one this
    powerset_def.mpr h
  have ⟨B, (h : ∀ y, y ∈ B ↔ ∃ x ∈ A, (x ≈ ∅ → y ≈ a) ∧ (x ≈ 𝒫 ∅ → y ≈ b))⟩ :=
    replacement A fun x (hx : x ∈ A)
        y ⟨(hya : x ≈ ∅ → y ≈ a), (hyb : x ≈ 𝒫 ∅ → y ≈ b)⟩
        z ⟨(hza : x ≈ ∅ → z ≈ a), (hzb : x ≈ 𝒫 ∅ → z ≈ b)⟩ =>
      show z ≈ y from
      match hA hx with
      | .inl (h : x ≈ ∅) =>
        calc  z
          _ ≈ a := hza h
          _ ≈ y := Setoid.symm (hya h)
      | .inr (h : x ≈ 𝒫 ∅) =>
        calc  z
          _ ≈ b := hzb h
          _ ≈ y := Setoid.symm (hyb h)
  Exists.intro B <| show a ∈ B ∧ b ∈ B ∧ ∀ y ∈ B, y ≈ a ∨ y ≈ b from
    have ha : a ∈ B :=
      suffices ∃ x ∈ A, (x ≈ ∅ → a ≈ a) ∧ (x ≈ 𝒫 ∅ → a ≈ b) from (h a).mpr this
      ⟨∅
      , show ∅ ∈ A from powerset_def.mp <| show ∅ ⊆ 𝒫 ∅ from empty_subset
      , fun _ => show a ≈ a from Setoid.rfl
      , fun h : ∅ ≈ 𝒫 ∅ => absurd h empty_ne_one⟩
    have hb : b ∈ B :=
      suffices ∃ x ∈ A, (x ≈ ∅ → b ≈ a) ∧ (x ≈ 𝒫 ∅ → b ≈ b) from (h b).mpr this
      ⟨𝒫 ∅
      , self_in_pow_self
      , fun h : 𝒫 ∅ ≈ ∅ => absurd (Setoid.symm h) empty_ne_one
      , fun _ => show b ≈ b from Setoid.rfl⟩
    suffices ∀ y ∈ B, y ≈ a ∨ y ≈ b from ⟨ha, hb, this⟩
    fun y (hy : y ∈ B) => show y ≈ a ∨ y ≈ b from
      have ⟨x, (hx : x ∈ A), (h₁ : x ≈ ∅ → y ≈ a), (h₂ : x ≈ 𝒫 ∅ → y ≈ b)⟩ := (h y).mp hy
      (hA hx).imp h₁ h₂

theorem singleton (a : Set) : ∃ A : Set, ∀ x, x ∈ A ↔ x ≈ a :=
  have ⟨A, (ha : a ∈ A), _, (h : ∀ x ∈ A, x ≈ a ∨ x ≈ a)⟩ := pairing a a
  Exists.intro A fun x => Iff.intro
    fun | (hx : x ∈ A) => show x ≈ a from or_self_iff.mp (h x hx)
    fun | (e : x ≈ a) => show x ∈ A from (extensionality (Setoid.symm e)).mp ha

@[default_instance] noncomputable instance : Singleton Set Set where
  singleton a := (Set.singleton a).choose
theorem singleton_def {x a : Set} : x ∈ {a} ↔ x ≈ a := (singleton a).choose_spec x
theorem self_in_singleton_self {a : Set} : a ∈ {a} := singleton_def.mpr Setoid.rfl

/-
## Sum Axiom
-/

axiom sum (A : Set) : ∃ B : Set, ∀ x, x ∈ B ↔ ∃ a ∈ A, x ∈ a
theorem union (A B : Set) : ∃ C : Set, ∀ x, x ∈ C ↔ x ∈ A ∨ x ∈ B :=
  have ⟨X, (hA : A ∈ X), (hB : B ∈ X), (h : ∀ Y ∈ X, Y ≈ A ∨ Y ≈ B)⟩ := pairing A B
  have ⟨C, (hC : ∀ x, x ∈ C ↔ ∃ Y ∈ X, x ∈ Y)⟩ := sum X
  Exists.intro C fun x => show x ∈ C ↔ x ∈ A ∨ x ∈ B from
    suffices (∃ Y ∈ X, x ∈ Y) ↔ x ∈ A ∨ x ∈ B from trans (hC x) this
    Iff.intro
      fun | ⟨Y, (hY : Y ∈ X), (hx : x ∈ Y)⟩ => show x ∈ A ∨ x ∈ B from
          (h Y hY).imp
            fun | (e : Y ≈ A) => show x ∈ A from trans hx e
            fun | (e : Y ≈ B) => show x ∈ B from trans hx e
      fun | .inl (hx : x ∈ A) => show ∃ A ∈ X, x ∈ A from ⟨A, hA ,hx⟩
          | .inr (hx : x ∈ B) => show ∃ B ∈ X, x ∈ B from ⟨B, hB, hx⟩
noncomputable instance : Union Set where
  union A B := (union A B).choose
theorem union_def {x A B : Set} : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := (union A B).choose_spec x

/-
## Natural Numbers
-/

theorem prod (A : Set) : ∃ B : Set, ∀ x, x ∈ B ↔ ∀ a ∈ A, x ∈ a := sorry
theorem minimal {P : Set → Prop} (h : ∃ A, P A) : ∃ M, P M ∧ ∀ A, P A → M ⊆ A :=
  sorry
theorem minimal' {P : Set → Prop} (h : ∃ A : Set, ∀ x ∈ A, P x) : ∃ A : Set, ∀ x, x ∈ A ↔ P x :=
  sorry
noncomputable def succ (A : Set) : Set := A ∪ {A}
def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ x ∈ A, x.succ ∈ A

theorem infinity' : Inductive default :=
  show ∅ ∈ default ∧ ∀ n ∈ default, n.succ ∈ default from
  have ⟨
    ⟨zero, (hz : zero ∈ default), (hz_def : ∀ x, x ∉ zero)⟩
  , (ih : ∀ m ∈ default, ∃ n ∈ default, ∀ x, x ∈ n ↔ x ∈ m ∨ x ≈ m)
  ⟩ := infinity.choose_spec
  And.intro (
    calc  ∅
      _ ≈ zero := Setoid.symm (unique_empty.mpr hz_def)
      _ ∈ default := hz
  ) fun m (hm : m ∈ default) => show m ∪ {m} ∈ default from
    have ⟨n, (hn : n ∈ default), (ih : ∀ x, x ∈ n ↔ x ∈ m ∨ x ≈ m)⟩ := ih m hm
    suffices n ≈ m ∪ {m} from trans (Setoid.symm this) hn
    suffices ∀ x, x ∈ n ↔ x ∈ m ∨ x ∈ {m}
    from fun x => show x ∈ n ↔ x ∈ m ∪ {m} from (iff_congr .rfl union_def).mpr (this x)
    fun x =>
      calc  x ∈ n
        _ ↔ x ∈ m ∨ x ≈ m := ih x
        _ ↔ _ ∨ x ∈ {m} := or_congr_right singleton_def.symm

noncomputable def ω : Set := (prod {A ∈ 𝒫 default | Inductive A}).choose
theorem ω_inductive : Inductive ω := sorry
theorem ω_minimal {A : Set} : Inductive A → ω ⊆ A := sorry

/-
## Axiom of Regularity
-/

def Disjoint (A B : Set) : Prop := ∀ x ∈ A, x ∉ B -- ¬∃ x, x ∈ A ∧ x ∈ B
axiom regularity {A : Set} (h : ∃ x, x ∈ A) : ∃ a ∈ A, Disjoint A a

end Set
