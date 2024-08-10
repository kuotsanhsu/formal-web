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
instance : Trans (α := Set) (· ≈ ·) (· ≈ ·) (· ≈ ·) where
  trans := Setoid.trans
@[default_instance] instance : HasSubset Set where
  Subset A B := ∀ x ∈ A, x ∈ B

/-- Substitutes equality on the LHS of `∈`. -/
axiom extensionality {x y A : Set} : x ≈ y → (x ∈ A ↔ y ∈ A)

axiom replacement {P : Set → Set → Prop} (A : Set) (h : ∀ x ∈ A, ∃? y, P x y)
  : ∃ B : Set, ∀ y, y ∈ B ↔ ∃ x ∈ A, P x y

theorem specification {P : Set → Prop} (A : Set)
  : ∃ B : Set, ∀ y, y ∈ B ↔ y ∈ A ∧ P y :=
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
example {x A B : Set} : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := spec_def

axiom powerset (A : Set) : ∃ B : Set, ∀ x ⊆ A, x ∈ B
class Powerset (α : Type _) where
  /-- Powerset: `𝒫 A`  -/
  powerset : α → α
@[inherit_doc] prefix:75 "𝒫" => Powerset.powerset
noncomputable instance : Powerset Set where
  powerset A := (powerset A).choose
def powerset_def {A B : Set} : A ⊆ B → A ∈ 𝒫 B := (powerset B).choose_spec A

theorem pairing (x y : Set) : ∃ A : Set, x ∈ A ∧ y ∈ A ∧ ∀ z ∈ A, z ≈ x ∨ z ≈ y :=
  sorry
theorem singleton (a : Set) : ∃ A : Set, ∀ x, x ∈ A ↔ x ≈ a :=
  have ⟨A, (ha : a ∈ A), _, (h : ∀ x ∈ A, x ≈ a ∨ x ≈ a)⟩ := pairing a a
  ⟨A, fun x => ⟨or_self_iff.mp ∘ h x, fun e => (extensionality (Setoid.symm e)).mp ha⟩⟩

@[default_instance] noncomputable instance : Singleton Set Set where
  singleton a := (Set.singleton a).choose
theorem singleton_def {x a : Set} : x ∈ {a} ↔ x ≈ a := (singleton a).choose_spec x
theorem singleton_def' {a : Set} : a ∈ {a} := singleton_def.mpr Setoid.rfl

/-- Union of all elements. -/
axiom sum (A : Set) : ∃ B : Set, ∀ x, x ∈ B ↔ ∃ a ∈ A, x ∈ a

theorem union (A B : Set) : ∃ C : Set, ∀ x, x ∈ C ↔ x ∈ A ∨ x ∈ B :=
  have ⟨X, hX⟩ := pairing A B
  have ⟨C, hC⟩ := sum X
  ⟨C, sorry⟩
noncomputable instance : Union Set where
  union A B := (union A B).choose
theorem union_def {x A B : Set} : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := (union A B).choose_spec x

noncomputable def succ (A : Set) : Set := A ∪ {A}
def Inductive (A : Set) : Prop := (∃ e ∈ A, ∀ x, x ∉ e) ∧ ∀ x ∈ A, x.succ ∈ A
axiom infinity : ∃ A : Set, Inductive A
noncomputable instance : Inhabited Set where
  default := infinity.choose

@[default_instance] noncomputable instance : EmptyCollection Set where
  emptyCollection := {x ∈ default | False}
theorem not_in_empty {x : Set} : x ∉ ∅ := And.right ∘ spec_def.mp

theorem prod (A : Set) : ∃ B : Set, ∀ x, x ∈ B ↔ ∀ a ∈ A, x ∈ a := sorry
noncomputable def N : Set := (prod {A ∈ 𝒫 default | Inductive A}).choose

def Disjoint (A B : Set) : Prop := ¬∃ x, x ∈ A ∧ x ∈ B
axiom regularity {A : Set} (h : ∃ x, x ∈ A) : ∃ B ∈ A, Disjoint A B

-- axiom choice



/-- #### Axiom 3.3 (Empty set) -/
protected axiom empty : ∃ A : Set, ∀ x, x ∉ A

variable {a b c d x y : Set} -- objects, which are sets in PST
variable {A A' B B' C D : Set} -- sets

theorem neq_of_eq_neq : A ≈ B → B ≉ C → A ≉ C := fun h₁ h₂ h => h₂ (trans (Setoid.symm h₁) h)
theorem neq_of_neq_eq : A ≉ B → B ≈ C → A ≉ C := fun h₁ h₂ h => h₁ (trans h (Setoid.symm h₂))

/-- The "is an element of" relation `∈` obeys the axiom of substitution (see Section A.7). -/
theorem equiv_congr (h₁ : A ≈ C) (h₂ : B ≈ D) : A ≈ B ↔ C ≈ D :=
  forall_congr' fun x => iff_congr (h₁ x) (h₂ x)

/-- There can only be one empty set. -/
theorem unique_empty : A ≈ ∅ ↔ ∀ x, x ∉ A :=
  Iff.intro
    fun | (h : ∀ x, x ∈ A ↔ x ∈ ∅), x, (k : x ∈ A) => not_in_empty ((h x).mp k)
    fun | (h : ∀ x, x ∉ A), x => iff_of_false (h x) not_in_empty

/-- #### Lemma 3.1.5 (Single choice) -/
theorem single_choice (h : A ≉ ∅) : ∃ x, x ∈ A :=
  suffices ¬∀ x, x ∉ A from Classical.not_forall_not.mp this
  unique_empty.subst h

theorem union_congr (h₁ : A ≈ C) (h₂ : B ≈ D) : A ∪ B ≈ C ∪ D :=
  fun x =>
    calc  x ∈ A ∪ B
      _ ↔ x ∈ A ∨ x ∈ B := union_def
      _ ↔ x ∈ C ∨ x ∈ D := or_congr (h₁ x) (h₂ x)
      _ ↔ x ∈ C ∪ D := union_def.symm

/-- #### Remark 3.1.11 -/
theorem union_congr_left {A'} (h : A ≈ A') : A ∪ B ≈ A' ∪ B :=
  union_congr h Setoid.rfl
/-- #### Remark 3.1.11 -/
theorem union_congr_right {B'} (h : B ≈ B') : A ∪ B ≈ A ∪ B' :=
  union_congr Setoid.rfl h

noncomputable instance : Insert Set Set where
  insert x A := {x} ∪ A

/-- #### Axiom 3.4 (Singleton sets and pair sets) -/
theorem pair_def : y ∈ {a, b} ↔ y ≈ a ∨ y ≈ b :=
  calc  y ∈ {a} ∪ {b}
    _ ↔ y ∈ {a} ∨ y ∈ {b} := union_def
    _ ↔ y ≈ a ∨ y ≈ b := or_congr singleton_def singleton_def

/-- #### Remarks 3.1.8
There is only one singleton set for each object `a`.
-/
theorem unique_singleton : {a} ≈ {b} ↔ a ≈ b :=
  Iff.intro (fun h : ∀ y, y ∈ {a} ↔ y ∈ {b} =>
    suffices a ∈ {b} from singleton_def.mp this
    (h a).mp singleton_def'
  ) fun (h : a ≈ b) x =>
    calc  x ∈ {a}
      _ ↔ x ≈ a := singleton_def
      _ ↔ x ≈ b := equiv_congr Setoid.rfl h
      _ ↔ x ∈ {b} := singleton_def.symm
/-- #### Remarks 3.1.8
Given any two objects `a` and `b`, there is only one pair set formed by `a` and `b`.
#### Exercise 3.1.1
-/
theorem unique_pair : {a, b} ≈ {x, y} ↔ (a ≈ x ∧ b ≈ y) ∨ (a ≈ y ∧ b ≈ x) :=
  calc  ∀ c, c ∈ {a, b} ↔ c ∈ {x, y}
    _ ↔ ∀ c, c ≈ a ∨ c ≈ b ↔ c ≈ x ∨ c ≈ y := forall_congr' fun _ => iff_congr pair_def pair_def
    _ ↔ (a ≈ x ∧ b ≈ y) ∨ (a ≈ y ∧ b ≈ x) :=
      Iff.intro (fun h : ∀ c, c ≈ a ∨ c ≈ b ↔ c ≈ x ∨ c ≈ y =>
        match Classical.propDecidable (a ≈ x), Classical.propDecidable (a ≈ y) with
        | isTrue (hx : a ≈ x), isTrue (hy : a ≈ y) =>
          have : b ≈ x ∨ b ≈ y := (h b).mp (.inr Setoid.rfl)
          this.symm.imp (⟨hx, ·⟩) (⟨hy, ·⟩)
        | isTrue (hx : a ≈ x), isFalse (hy : a ≉ y) =>
          have : y ≈ a ∨ y ≈ b := (h y).mpr (.inr Setoid.rfl)
          this.symm.imp (⟨hx, Setoid.symm ·⟩) fun h => absurd (Setoid.symm h) hy
        | isFalse (hx : a ≉ x), isTrue (hy : a ≈ y) =>
          have : x ≈ a ∨ x ≈ b := (h x).mpr (.inl Setoid.rfl)
          this.imp (fun h => absurd (Setoid.symm h) hx) (⟨hy, Setoid.symm ·⟩)
        | isFalse (hx : a ≉ x), isFalse (hy : a ≉ y) =>
          have : a ≈ x ∨ a ≈ y := (h a).mp (.inl Setoid.rfl)
          this.rec (absurd · hx) (absurd · hy)
      ) fun
        | .inl ⟨hax, hby⟩, _ => or_congr (equiv_congr Setoid.rfl hax) (equiv_congr Setoid.rfl hby)
        | .inr ⟨hay, hbx⟩, c =>
          calc  c ≈ a ∨ c ≈ b
            _ ↔ c ≈ y ∨ c ≈ x := or_congr (equiv_congr Setoid.rfl hay) (equiv_congr Setoid.rfl hbx)
            _ ↔ c ≈ x ∨ c ≈ y := or_comm
/-- #### Remarks 3.1.8 -/
theorem pair_comm : {a, b} ≈ {b, a} := unique_pair.mpr (.inr ⟨Setoid.rfl, Setoid.rfl⟩)
/-- #### Remarks 3.1.8 -/
theorem pair_same : {a, a} ≈ {a} :=
  fun x =>
    calc  x ∈ {a} ∪ {a}
      _ ↔ x ∈ {a} ∨ x ∈ {a} := union_def
      _ ↔ x ∈ {a} := or_self_iff

/-- #### Lemma 3.1.12
#### Exercise 3.1.3
-/
example : {a, b} ≈ {a} ∪ {b} := Setoid.rfl
/-- #### Lemma 3.1.12
#### Exercise 3.1.3
-/
theorem union_comm : A ∪ B ≈ B ∪ A :=
  fun x =>
    calc  x ∈ A ∪ B
      _ ↔ x ∈ A ∨ x ∈ B := union_def
      _ ↔ x ∈ B ∨ x ∈ A := or_comm
      _ ↔ x ∈ B ∪ A := union_def.symm
example : A ∪ B ≈ B ∪ A := fun _ => (iff_congr union_def union_def).mpr or_comm
/-- #### Lemma 3.1.12 -/
theorem union_assoc : (A ∪ B) ∪ C ≈ A ∪ (B ∪ C) :=
  fun x =>
    calc  x ∈ (A ∪ B) ∪ C
      _ ↔ (x ∈ A ∪ B) ∨ x ∈ C := union_def
      _ ↔ (x ∈ A ∨ x ∈ B) ∨ x ∈ C := or_congr_left union_def
      _ ↔ x ∈ A ∨ (x ∈ B ∨ x ∈ C) := or_assoc
      _ ↔ x ∈ A ∨ (x ∈ B ∪ C) := or_congr_right union_def.symm
      _ ↔ x ∈ A ∪ (B ∪ C) := union_def.symm
/-- #### Lemma 3.1.12
#### Exercise 3.1.3
-/
theorem union_same : A ∪ A ≈ A :=
  fun x =>
    calc  x ∈ A ∪ A
      _ ↔ x ∈ A ∨ x ∈ A := union_def
      _ ↔ x ∈ A := or_self_iff
/-- #### Lemma 3.1.12
#### Exercise 3.1.3
-/
theorem union_empty : A ∪ ∅ ≈ A :=
  fun x =>
    calc  x ∈ A ∪ ∅
      _ ↔ x ∈ A ∨ x ∈ ∅ := union_def
      _ ↔ x ∈ A := ⟨Or.rec id (absurd · not_in_empty), .inl⟩
/-- #### Lemma 3.1.12
#### Exercise 3.1.3
-/
theorem empty_union : ∅ ∪ A ≈ A :=
  calc  ∅ ∪ A
    _ ≈ A ∪ ∅ := union_comm
    _ ≈ A := union_empty

/-- #### Examples 3.1.9
These four sets are not equal to each other: `∅`, `{∅}`, `{{∅}}`, `{∅, {∅}}`.
#### Exercise 3.1.2
-/
example :
  ∅ ≠ {∅} ∧ ∅ ≠ {{∅}} ∧ ∅ ≠ {∅, {∅}} ∧
  {∅} ≠ {{∅}} ∧ {∅} ≠ {∅, {∅}} ∧
  {{∅}} ≠ {∅, {∅}}
:=
  sorry

/-- von Neumann ordinals -/
noncomputable def ofNat : Nat → Set
  | 0 => ∅
  | m+1 => let n := ofNat m ; n ∪ {n}
@[default_instance] noncomputable instance {n} : OfNat Set n where
  ofNat := ofNat n

example : 0 ≈ ∅ := Setoid.rfl
theorem one_def : 1 ≈ {∅} := empty_union
theorem singleton_one : {1} ≈ {{∅}} := unique_singleton.mpr empty_union
example : 2 ≈ {∅, {∅}} :=
  show 1 ∪ {1} ≈ {∅} ∪ {{∅}} from union_congr one_def singleton_one

/-- #### Examples 3.1.9
These four sets are not equal to each other: `0`, `1`, `{1}`, `2`.
#### Exercise 3.1.2
-/
example : 0 ≠ 1 ∧ 0 ≠ {1} ∧ 0 ≠ 2 ∧ 1 ≠ {1} ∧ 1 ≠ 2 ∧ {1} ≠ 2 :=
  sorry

example : {a, b, c} ≈ {a} ∪ {b} ∪ {c} :=
  show {a} ∪ ({b} ∪ {c}) ≈ {a} ∪ {b} ∪ {c} from Setoid.symm union_assoc
example : {a, b, c, d} ≈ {a} ∪ {b} ∪ {c} ∪ {d} :=
  calc  {a} ∪ ({b} ∪ ({c} ∪ {d}))
    _ ≈ {a} ∪ {b} ∪ ({c} ∪ {d}) := Setoid.symm union_assoc
    _ ≈ {a} ∪ {b} ∪ {c} ∪ {d} := Setoid.symm union_assoc

/-- #### Example 3.1.4 -/
example : {1, 2, 3, 4, 5} ≈ {3, 4, 2, 1, 5} :=
  sorry
/-- #### Example 3.1.4 -/
example : {3, 3, 1, 5, 2, 4, 2} ≈ {1, 2, 3, 4, 5} :=
  sorry
/-- #### Example 3.1.10 -/
example : {1, 2} ∪ {2, 3} ≈ {1, 2, 3} :=
  sorry

/-- #### Definition 3.1.14 (Subsets) -/
@[default_instance] instance : HasSubset Set where
  Subset A B := ∀ x ∈ A, x ∈ B
@[default_instance] instance : HasSSubset Set where
  SSubset A B := A ≉ B ∧ A ⊆ B

/-- #### Remark 3.1.15 -/
instance : Trans (· ≈ ·) Subset Subset where
  trans {A B C} (h₁ : A ≈ B) (h₂ : B ⊆ C) x (h : x ∈ A) := show x ∈ C from
    suffices x ∈ B from h₂ x this ; (h₁ x).mp h
instance : Trans Subset (· ≈ ·) Subset where
  trans {A B C} (h₁ : A ⊆ B) (h₂ : B ≈ C) x (h : x ∈ A) := show x ∈ C from
    suffices x ∈ B from (h₂ x).mp this ; h₁ x h
instance : Trans (· ≈ ·) SSubset SSubset where
  trans {A B C} := fun (h₁ : A ≈ B) ⟨(ne : B ≉ C), (h₂ : B ⊆ C)⟩ => show A ≉ C ∧ A ⊆ C from
    ⟨neq_of_eq_neq h₁ ne, trans h₁ h₂⟩
instance : Trans SSubset (· ≈ ·) SSubset where
  trans {A B C} := fun ⟨(ne : A ≉ B), (h₁ : A ⊆ B)⟩ (h₂ : B ≈ C) => show A ≉ C ∧ A ⊆ C from
    ⟨neq_of_neq_eq ne h₂, trans h₁ h₂⟩

/-- #### Examples 3.1.16 -/
example : {1, 2, 4} ⊆ {1, 2, 3, 4, 5} :=
  sorry
/-- #### Examples 3.1.16 -/
example : {1, 2, 4} ⊂ {1, 2, 3, 4, 5} :=
  sorry
/-- #### Examples 3.1.16 -/
theorem subset_rfl : A ⊆ A := fun _ => id
/-- #### Examples 3.1.16 -/
theorem empty_subset : ∅ ⊆ A := fun _ h => absurd h not_in_empty

/-- #### Proposition 3.1.17 (Sets are partially ordered by set inclusion) -/
instance : Trans Subset Subset Subset where
  trans {A B C} (h₁ : A ⊆ B) (h₂ : B ⊆ C) x (h : x ∈ A) := show x ∈ C from h₂ x (h₁ x h)
/-- #### Proposition 3.1.17 (Sets are partially ordered by set inclusion)
#### Exercise 3.1.4
-/
theorem subset_antisymm : A ⊆ B → B ⊆ A → A ≈ B := fun h₁ h₂ x => ⟨h₁ x, h₂ x⟩
theorem not_ssusbset_same : ¬A ⊂ A := fun ⟨(ne : A ≉ A), _⟩ => ne Setoid.rfl
theorem ssubset_asymm : A ⊂ B → B ⊂ A → False :=
  fun ⟨(ne₁ : A ≉ B), (h₁ : A ⊆ B)⟩ ⟨_, (h₂ : B ⊆ A)⟩ =>
    suffices A ≈ B from ne₁ this
    subset_antisymm h₁ h₂
instance : Trans Subset SSubset SSubset where
  trans {A B C} := fun (h₁ : A ⊆ B) ⟨(ne : B ≉ C), (h₂ : B ⊆ C)⟩ => show A ≉ C ∧ A ⊆ C from
    suffices A ≈ C → False from ⟨this, trans h₁ h₂⟩
    fun e : A ≈ C =>
      suffices C ⊆ B from ne (subset_antisymm h₂ this)
      trans (Setoid.symm e) h₁
instance : Trans SSubset Subset SSubset where
  trans {A B C} := fun ⟨(ne : A ≉ B), (h₁ : A ⊆ B)⟩ (h₂ : B ⊆ C) => show A ≉ C ∧ A ⊆ C from
    suffices A ≈ C → False from ⟨this, trans h₁ h₂⟩
    fun e : A ≈ C =>
      suffices B ⊆ A from ne (subset_antisymm h₁ this)
      trans h₂ (Setoid.symm e)
/-- #### Proposition 3.1.17 (Sets are partially ordered by set inclusion)
#### Exercise 3.1.4
-/
instance : Trans SSubset SSubset SSubset where
  trans {A B C} (h₁ : A ⊂ B) (h₂ : B ⊂ C) := trans h₁ h₂.2


/-- #### Examples 3.1.24 -/
example : {1, 2, 4} ∩ {2, 3, 4} ≈ {2, 4} :=
  sorry
/-- #### Examples 3.1.24 -/
example : {1, 2} ∩ {3, 4} ≈ ∅ :=
  sorry
/-- #### Examples 3.1.24 -/
example : {2, 3} ∪ ∅ ≈ {2, 3} := union_empty
/-- #### Examples 3.1.24 -/
example : {2, 3} ∩ ∅ ≈ ∅ := fun _ => ⟨(And.right ∘ spec_def.mp), (absurd · not_in_empty)⟩

/-- #### Definition 3.1.26 (Difference sets) -/
noncomputable instance : SDiff Set where
  sdiff A B := {x ∈ A | x ∉ B}
example : y ∈ {x ∈ A | x ∉ B} ↔ y ∈ A ∧ y ∉ B := spec_def

/- #### Proposition 3.1.27 (Sets form a boolean algebra)
#### Exercise 3.1.6
-/
section
variable {X : Set} (hA : A ⊆ X) (hB : B ⊆ X) (hC : C ⊆ X)

-- (d) (Commutativity)
#check (union_comm : A ∪ B ≈ B ∪ A)
theorem inter_comm : A ∩ B ≈ B ∩ A := fun _ => (iff_congr spec_def spec_def).mpr and_comm

-- (a) (Minimal element)
#check (union_empty : A ∪ ∅ ≈ A)
theorem inter_empty : A ∩ ∅ ≈ ∅ := fun _ => ⟨(And.right ∘ spec_def.mp), (absurd · not_in_empty)⟩

#check (empty_union : ∅ ∪ A ≈ A)
theorem empty_inter : ∅ ∩ A ≈ ∅ := trans inter_comm inter_empty

-- (b) (Maximal element)
theorem union_super : A ∪ X ≈ X :=
  fun x =>
    calc  x ∈ A ∪ X
      _ ↔ x ∈ A ∨ x ∈ X := union_def
      _ ↔ x ∈ X := or_iff_right_of_imp (hA x)
theorem inter_super : A ∩ X ≈ A :=
  fun x =>
    calc  x ∈ A ∩ X
      _ ↔ x ∈ A ∧ x ∈ X := spec_def
      _ ↔ x ∈ A := and_iff_left_of_imp (hA x)

theorem super_union : X ∪ A ≈ X := trans union_comm (union_super hA)
theorem super_inter : X ∩ A ≈ A := trans inter_comm (inter_super hA)

-- (c) (Identity)
theorem inter_same : A ∩ A ≈ A := sorry
#check (union_same : A ∪ A ≈ A)

-- (e) (Associativity)
#check (union_assoc : A ∪ B ∪ C ≈ A ∪ (B ∪ C))
theorem inter_assoc : A ∩ B ∩ C ≈ A ∩ (B ∩ C) := sorry

-- (f) (Distributivity)
theorem inter_union : A ∩ (B ∪ C) ≈ A ∩ B ∪ A ∩ c := sorry
theorem union_inter : A ∪ B ∩ C ≈ (A ∪ B) ∩ (A ∪ C) := sorry

theorem inter_union' : A ∩ B ∪ C ≈ (A ∪ C) ∩ (B ∪ C) := sorry
theorem union_inter' : (B ∪ C) ∩ A ≈ B ∩ A ∪ C ∩ A := sorry

-- (g) (Partition)
theorem union_compl : A ∪ (X \ A) ≈ X := sorry
theorem inter_compl : A ∩ (X \ A) ≈ ∅ := sorry

theorem compl_union' : (X \ A) ∪ A ≈ X := sorry
theorem compl_inter' : (X \ A) ∩ A ≈ ∅ := sorry

-- (h) (De Morgan laws)
theorem compl_union : X \ A ∪ B ≈ (X \ A) ∩ (X \ B) := sorry
theorem compl_inter : X \ A ∩ B ≈ (X \ A) ∪ (X \ B) := sorry

end

structure Peano {N : Type} (zero : N) (succ : N → N) : Prop where
  /-- #### Axiom 2.3 -/
  succ_ne_zero {n : N} : succ n ≠ zero
  /-- #### Axiom 2.4 -/
  succ_inj {n m : N} : succ n = succ m → n = m
  /-- #### Axiom 2.5 (Principle of mathematical induction) -/
  ind {P : N → Prop} (zero : P zero) (succ : ∀ n, P n → P (succ n)) : ∀ n, P n

/-- #### Axiom 3.8 (Infinity) -/
protected axiom infinity : ∃ N : Set, ∃ zero ∈ N, Peano zero sorry

/-- #### Exercise 3.1.5 -/
example : A ⊆ B ↔ A ∪ B ≈ B := sorry
example : A ⊆ B ↔ A ∩ B ≈ A := sorry

/-- #### Exercise 3.1.7 -/
example : A ∩ B ⊆ A := sorry
example : A ∩ B ⊆ B := sorry
example : C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B := sorry
example : A ⊆ A ∪ B := sorry
example : B ⊆ A ∪ B := sorry
example : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := sorry

/-- #### Exercise 3.1.8 -/
example : A ∩ (A ∪ B) ≈ A := sorry
example : A ∪ (A ∩ B) ≈ A := sorry

/-- #### Exercise 3.1.9 -/
example {X} : A ∪ B ≈ X → A ∩ B ≈ ∅ → A ≈ X \ B ∧ B ≈ X \ A := sorry

-- #### Exercise 3.1.11

section «Exercise 3.1.12»
variable (hA : A' ⊆ A) (hB : B' ⊆ B)

/-- #### Exercise 3.1.12 -/
example : A' ∪ B' ⊆ A ∪ B := sorry
example : A' ∩ B' ⊆ A ∩ B := sorry
example : ∃ A B : Set, ∃ A' ⊆ A, ∃ B' ⊆ B, A' \ B' ⊆ A \ B → False := sorry
example : True := trivial

end «Exercise 3.1.12»

/-- #### Exercise 3.1.13 -/
example (h : A ≉ ∅) : (¬∃ B ⊂ A, B ≉ ∅) ↔ ∃ x, A = {x} := sorry

end Set
