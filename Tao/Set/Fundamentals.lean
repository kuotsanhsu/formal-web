/-!
# Pure Set Theory (PST)
Since PST requires objects to be sets, `2 ∪ 3` is a valid expression contrary to
Remark 3.1.13. However, Tao doesn't mandate PST, and this opens the possibility
to render `2 ∪ 3` insensible, which is more reasonable.

#### Remark 3.1.13
While the operation of union has some similarities with addition, the two operations
are not identical. For instance, `{2} ∪ {3} = {2, 3}` and `2 + 3 = 5`, whereas
`{2} + {3}` is meaningless (addition pertains to numbers, not sets) and `2 ∪ 3`
is also meaningless (union pertains to sets, not numbers).

-/

/-- #### Definition 3.1.1 -/
axiom Set : Type
namespace Set
variable {A B C a b c d x y : Set}

/-- #### Axiom 3.1 (Sets are objects) -/
protected axiom Mem : Set → Set → Prop
instance : Membership Set Set where
  mem := Set.Mem

/-- #### Axiom 3.2 (Equality of sets) -/
axiom eq : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B

protected axiom empty : Set
@[default_instance] noncomputable instance : EmptyCollection Set where
  emptyCollection := Set.empty
/-- #### Axiom 3.3 (Empty set) -/
axiom not_in_empty : x ∉ ∅

/-- There can only be one empty set. -/
theorem unique_empty : A = ∅ ↔ ∀ x, x ∉ A :=
  .intro (fun (h : A = ∅) _ => h ▸ not_in_empty) fun (h : ∀ x, x ∉ A) =>
    show A = ∅ from
    suffices ∀ x, x ∈ A ↔ x ∈ ∅ from eq.mpr this
    fun x => ⟨(absurd · (h x)), (absurd · not_in_empty)⟩

/-- #### Lemma 3.1.5 (Single choice) -/
theorem single_choice (h : A ≠ ∅) : ∃ x, x ∈ A :=
  suffices ¬∀ x, x ∉ A from Classical.not_forall_not.mp this
  unique_empty.subst h

protected axiom singleton : Set → Set
@[default_instance] noncomputable instance : Singleton Set Set where
  singleton := Set.singleton
/-- #### Axiom 3.4 (Singleton sets and pair sets) -/
axiom singleton_def : y ∈ {a} ↔ y = a
theorem singleton_def' : a ∈ {a} := singleton_def.mpr rfl

protected axiom union : Set → Set → Set
noncomputable instance : Union Set where
  union := Set.union
/-- #### Axiom 3.5 (Pairwise union) -/
axiom union_def : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

-- FIXME: must use `≈` instead of `=`; otherwise, equality becomes trivial.
/-- #### Remark 3.1.11 -/
example {A'} : A = A' → A ∪ B = A' ∪ B :=
  fun | rfl => rfl
/-- #### Remark 3.1.11 -/
example {B'} : B = B' → A ∪ B = A ∪ B' :=
  sorry

noncomputable instance : Insert Set Set where
  insert x A := {x} ∪ A
instance : LawfulSingleton Set Set where
  insert_emptyc_eq x := show {x} ∪ ∅ = {x} from
    suffices ∀ y, y ∈ {x} ∪ ∅ ↔ y ∈ {x} from eq.mpr this
    fun y => .intro (fun h : y ∈ {x} ∪ ∅ =>
      have : y ∈ {x} ∨ y ∈ ∅ := union_def.mp h
      show y ∈ {x} from this.rec id (absurd · not_in_empty)
    ) fun h : y ∈ {x} =>
      have : y ∈ {x} ∨ y ∈ ∅ := .inl h
      show y ∈ {x} ∪ ∅ from union_def.mpr this

/-- #### Axiom 3.4 (Singleton sets and pair sets) -/
theorem pair_def : y ∈ {a, b} ↔ y = a ∨ y = b :=
  .intro (fun h : y ∈ {a} ∪ {b} => show y = a ∨ y = b from
    have : y ∈ {a} ∨ y ∈ {b} := union_def.mp h
    match this with
    | .inl h => .inl (singleton_def.mp h)
    | .inr h => .inr (singleton_def.mp h)
  ) fun h : y = a ∨ y = b => show y ∈ {a} ∪ {b} from
    suffices y ∈ {a} ∨ y ∈ {b} from union_def.mpr this
    match h with
    | .inl rfl => .inl singleton_def'
    | .inr rfl => .inr singleton_def'

/-- #### Remarks 3.1.8
There is only one singleton set for each object `a`.
-/
theorem unique_singleton : {a} = {b} ↔ a = b :=
  sorry
/-- #### Remarks 3.1.8
Given any two objects `a` and `b`, there is only one pair set formed by `a` and `b`.
-/
theorem unique_pair : {a, b} = {x, y} ↔ (a = x ∧ b = y) ∨ (a = y ∧ b = x) :=
  sorry
/-- #### Remarks 3.1.8 -/
theorem pair_comm : {a, b} = {b, a} :=
  sorry
/-- #### Remarks 3.1.8 -/
theorem pair_same : {a, a} = {a} :=
  sorry

/-- #### Lemma 3.1.12 -/
example : {a, b} = {a} ∪ {b} := rfl
/-- #### Lemma 3.1.12 -/
theorem union_comm : A ∪ B = B ∪ A :=
  sorry
/-- #### Lemma 3.1.12 -/
theorem union_assoc : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
  sorry
/-- #### Lemma 3.1.12 -/
theorem union_same : A ∪ A = A :=
  sorry
/-- #### Lemma 3.1.12 -/
theorem union_empty : A ∪ ∅ = A :=
  sorry
/-- #### Lemma 3.1.12 -/
theorem empty_union : ∅ ∪ A = A :=
  sorry

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

example : 0 = ∅ := rfl
theorem one_def : 1 = {∅} := empty_union
theorem singleton_one : {1} = {{∅}} := unique_singleton.mpr empty_union
example : 2 = {∅, {∅}} := show 1 ∪ {1} = _ ∪ {{∅}} from congrArg (· ∪ _) one_def
/-- #### Examples 3.1.9
These four sets are not equal to each other: `0`, `1`, `{1}`, `2`.
#### Exercise 3.1.2
-/
example : 0 ≠ 1 ∧ 0 ≠ {1} ∧ 0 ≠ 2 ∧ 1 ≠ {1} ∧ 1 ≠ 2 ∧ {1} ≠ 2 :=
  sorry

example : {a, b, c} = {a} ∪ {b} ∪ {c} :=
  sorry
example : {a, b, c, d} = {a} ∪ {b} ∪ {c} ∪ {d} :=
  sorry

/-- #### Example 3.1.4 -/
example : {1, 2, 3, 4, 5} = {3, 4, 2, 1, 5} :=
  sorry
/-- #### Example 3.1.4 -/
example : {3, 3, 1, 5, 2, 4, 2} = {1, 2, 3, 4, 5} :=
  sorry
/-- #### Example 3.1.10 -/
example : {1, 2} ∪ {2, 3} = {1, 2, 3} :=
  sorry

/-- #### Definition 3.1.14 (Subsets) -/
instance : HasSubset Set where
  Subset A B := ∀ x, x ∈ A → x ∈ B
instance : HasSSubset Set where
  SSubset A B := A ≠ B ∧ A ⊆ B

end Set
