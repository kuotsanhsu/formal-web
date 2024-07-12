import Tao.Logic

/-!
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
-/

/-- #### Axiom 3.1 (Sets are objects) -/
axiom Set : Type
namespace Set
variable {a b c d x y : Set} -- objects, which are sets in PST
variable {A B C D : Set} -- sets

/-- #### Definition 3.1.1 -/
protected axiom mem : Set → Set → Prop
instance : Membership Set Set where
  mem := Set.mem

/-- #### Axiom 3.2 (Equality of sets) -/
instance : Setoid Set where
  r A B := ∀ x, x ∈ A ↔ x ∈ B
  iseqv.refl _ _ := Iff.rfl
  iseqv.symm h x := (h x).symm
  iseqv.trans h₁ h₂ x := trans (h₁ x) (h₂ x)

instance : Trans (α := Set) (· ≈ ·) (· ≈ ·) (· ≈ ·) where
  trans := Setoid.trans
theorem neq_of_eq_neq : A ≈ B → B ≉ C → A ≉ C :=
  fun (h₁ : A ≈ B) (h₂ : B ≉ C) (h : A ≈ C) =>
    suffices B ≈ C from h₂ this
    calc  B
      _ ≈ A := Setoid.symm h₁
      _ ≈ C := h
instance : Trans (α := Set) (· ≈ ·) (· ≉ ·) (· ≉ ·) where
  trans := neq_of_eq_neq
theorem neq_of_neq_eq : A ≉ B → B ≈ C → A ≉ C :=
  fun (h₁ : A ≉ B) (h₂ : B ≈ C) (h : A ≈ C) =>
    suffices A ≈ B from h₁ this
    calc  A
      _ ≈ C := h
      _ ≈ B := Setoid.symm h₂
instance : Trans (α := Set) (· ≉ ·) (· ≈ ·) (· ≉ ·) where
  trans := neq_of_neq_eq

#check (trans : A = B → B ≠ C → A ≠ C)
#check_failure (trans : A ≈ B → B ≉ C → A ≉ C)
#check (trans : A ≠ B → B = C → A ≠ C)
#check_failure (trans : A ≉ B → B ≈ C → A ≉ C)

/-- The "is an element of" relation `∈` obeys the axiom of substitution (see Section A.7). -/
theorem equiv_congr (h₁ : A ≈ C) (h₂ : B ≈ D) : A ≈ B ↔ C ≈ D :=
  forall_congr' fun x => iff_congr (h₁ x) (h₂ x)

/-- #### Axiom 3.3 (Empty set) -/
protected axiom empty : ∃ A : Set, ∀ x, x ∉ A
@[default_instance] noncomputable instance : EmptyCollection Set where
  emptyCollection := Set.empty.choose
theorem not_in_empty : x ∉ ∅ := Set.empty.choose_spec x

/-- There can only be one empty set. -/
theorem unique_empty : A ≈ ∅ ↔ ∀ x, x ∉ A :=
  Iff.intro
    fun | (h : ∀ x, x ∈ A ↔ x ∈ ∅), x, (k : x ∈ A) => not_in_empty ((h x).mp k)
    fun | (h : ∀ x, x ∉ A), x => iff_of_false (h x) not_in_empty

/-- #### Lemma 3.1.5 (Single choice) -/
theorem single_choice (h : A ≉ ∅) : ∃ x, x ∈ A :=
  suffices ¬∀ x, x ∉ A from Classical.not_forall_not.mp this
  unique_empty.subst h

/-- #### Axiom 3.4 (Singleton sets and pair sets) -/
protected axiom singleton (a : Set) : ∃ A : Set, ∀ y, y ∈ A ↔ y ≈ a
@[default_instance] noncomputable instance : Singleton Set Set where
  singleton a := (Set.singleton a).choose
theorem singleton_def : y ∈ {a} ↔ y ≈ a := (Set.singleton a).choose_spec y
theorem singleton_def' : a ∈ {a} := singleton_def.mpr Setoid.rfl

/-- #### Axiom 3.5 (Pairwise union) -/
protected axiom union (A B : Set) : ∃ C : Set, ∀ x, x ∈ C ↔ x ∈ A ∨ x ∈ B
noncomputable instance : Union Set where
  union A B := (Set.union A B).choose
theorem union_def : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := (Set.union A B).choose_spec x

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
-/
theorem unique_pair : {a, b} ≈ {x, y} ↔ (a ≈ x ∧ b ≈ y) ∨ (a ≈ y ∧ b ≈ x) :=
  sorry
  -- ∀ e, e ∈ {a} ∨ e ∈ {b} ↔ e ∈ {x} ∨ e ∈ {y}
  -- ∀ e, e ≈ a ∨ e ≈ b ↔ e ≈ x ∨ e ≈ y
/-- #### Remarks 3.1.8 -/
theorem pair_comm : {a, b} ≈ {b, a} := unique_pair.mpr (.inr ⟨Setoid.rfl, Setoid.rfl⟩)
/-- #### Remarks 3.1.8 -/
theorem pair_same : {a, a} ≈ {a} :=
  fun x =>
    calc  x ∈ {a} ∪ {a}
      _ ↔ x ∈ {a} ∨ x ∈ {a} := union_def
      _ ↔ x ∈ {a} := or_self_iff

/-- #### Lemma 3.1.12 -/
example : {a, b} ≈ {a} ∪ {b} := Setoid.rfl
/-- #### Lemma 3.1.12 -/
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
/-- #### Lemma 3.1.12 -/
theorem union_same : A ∪ A ≈ A :=
  fun x =>
    calc  x ∈ A ∪ A
      _ ↔ x ∈ A ∨ x ∈ A := union_def
      _ ↔ x ∈ A := or_self_iff
/-- #### Lemma 3.1.12 -/
theorem union_empty : A ∪ ∅ ≈ A :=
  fun x =>
    calc  x ∈ A ∪ ∅
      _ ↔ x ∈ A ∨ x ∈ ∅ := union_def
      _ ↔ x ∈ A := ⟨Or.rec id (absurd · not_in_empty), .inl⟩
/-- #### Lemma 3.1.12 -/
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
  Subset A B := ∀ x, x ∈ A → x ∈ B
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
example : A ⊆ A :=
  sorry
/-- #### Examples 3.1.16 -/
example : ∅ ⊆ A :=
  sorry

/-- #### Proposition 3.1.17 (Sets are partially ordered by set inclusion) -/
instance : Trans Subset Subset Subset where
  trans {A B C} (h₁ : A ⊆ B) (h₂ : B ⊆ C) x (h : x ∈ A) := show x ∈ C from h₂ x (h₁ x h)
/-- #### Proposition 3.1.17 (Sets are partially ordered by set inclusion) -/
theorem subset_antisymm : A ⊆ B → B ⊆ A → A ≈ B := fun h₁ h₂ x => ⟨h₁ x, h₂ x⟩
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
/-- #### Proposition 3.1.17 (Sets are partially ordered by set inclusion) -/
instance : Trans SSubset SSubset SSubset where
  trans {A B C} (h₁ : A ⊂ B) (h₂ : B ⊂ C) := trans h₁ h₂.2

end Set
