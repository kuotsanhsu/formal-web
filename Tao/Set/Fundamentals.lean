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
variable {A B C : Set} -- sets

/-- #### Definition 3.1.1 -/
protected axiom Mem : Set → Set → Prop
instance : Membership Set Set where
  mem := Set.Mem

/-- #### Axiom 3.2 (Equality of sets) -/
instance : Setoid Set where
  r A B := ∀ x, x ∈ A ↔ x ∈ B
  iseqv.refl _ _ := Iff.rfl
  iseqv.symm h x := (h x).symm
  iseqv.trans h₁ h₂ x := trans (h₁ x) (h₂ x)

instance : Trans (α := Set) (· ≈ ·) (· ≈ ·) (· ≈ ·) where
  trans := Setoid.trans

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

/-- #### Remark 3.1.11 -/
example {A'} : A ≈ A' → A ∪ B ≈ A' ∪ B :=
  fun (h : ∀ x, x ∈ A ↔ x ∈ A') x =>
    calc  x ∈ A ∪ B
      _ ↔ x ∈ A ∨ x ∈ B := union_def
      _ ↔ x ∈ A' ∨ x ∈ B := or_congr_left (h x)
      _ ↔ x ∈ A' ∪ B := union_def.symm
/-- #### Remark 3.1.11 -/
example {B'} : B ≈ B' → A ∪ B ≈ A ∪ B' :=
  fun (h : ∀ x, x ∈ B ↔ x ∈ B') x =>
    calc  x ∈ A ∪ B
      _ ↔ x ∈ A ∨ x ∈ B := union_def
      _ ↔ x ∈ A ∨ x ∈ B' := or_congr_right (h x)
      _ ↔ x ∈ A ∪ B' := union_def.symm

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
      _ ↔ x ≈ b := ⟨(trans · h), (trans · (Setoid.symm h))⟩ -- FIXME: simplify?
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
example : 2 ≈ {∅, {∅}} := -- show 1 ∪ {1} ≈ _ ∪ {{∅}} from congrArg (· ∪ _) one_def
  calc  1 ∪ {1}
    _ ≈ {∅} ∪ {1} := sorry
    _ ≈ {∅, {∅}} := sorry

/-- #### Examples 3.1.9
These four sets are not equal to each other: `0`, `1`, `{1}`, `2`.
#### Exercise 3.1.2
-/
example : 0 ≠ 1 ∧ 0 ≠ {1} ∧ 0 ≠ 2 ∧ 1 ≠ {1} ∧ 1 ≠ 2 ∧ {1} ≠ 2 :=
  sorry

example : {a, b, c} ≈ {a} ∪ {b} ∪ {c} :=
  sorry
example : {a, b, c, d} ≈ {a} ∪ {b} ∪ {c} ∪ {d} :=
  sorry

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
instance : HasSubset Set where
  Subset A B := ∀ x, x ∈ A → x ∈ B
instance : HasSSubset Set where
  SSubset A B := A ≠ B ∧ A ⊆ B

end Set
