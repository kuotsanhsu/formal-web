universe u

/-- https://en.wikipedia.org/wiki/Regular_language#Formal_definition
`α` is the type of alphabet allowed in the regular language. We make it universe-polymorphic. -/
inductive RegExp (α: Type u)
  /-- Matches nothing. -/
  | nothing
  /-- Empty string matcher. -/
  | empty
  | single (a: α)
  /-- `/ab/` -/
  | append (r₁ r₂: RegExp α)
  /-- `/a|b/`-/
  | union (r₁ r₂: RegExp α)
  | star (r: RegExp α)

namespace RegExp
variable {α : Type u}

/-
Define convenient notations for `RegExp`.
-/

instance : EmptyCollection (RegExp α) where
  emptyCollection := empty

instance : Singleton α (RegExp α) where
  singleton := single

/-- Write `r ++ r'` for `RegExp.append r r'`. -/
instance : Append (RegExp α) where
  append := append

/-- Write `r ∪ r'` for `RegExp.union r r'`. -/
instance : Union (RegExp α) where
  union := union

/-- Write `r*` for `RegExp.star r`. This postfix operator `*` binds tighter
than function application. -/
postfix:arg "*" => star

/-- Denoted by the Haskell operator `=~` to avoid overloading `∈` as done in
theoretical computer science; really, `∈` is way too overloaded in math. We
depart slightly from standard practice in that we do not require the type `α`
to be finite. This results in a somewhat different theory of regular
expressions, but the difference doesn't concern us here. -/
inductive Accept: List α → RegExp α → Prop
  | empty: Accept [] {}
  | single {a: α}: Accept [a] {a}
  | append {s₁ r₁ s₂ r₂}
    : Accept s₁ r₁ → Accept s₂ r₂ → Accept (s₁ ++ s₂) (r₁ ++ r₂)
  | unionL {s₁ r₁ r₂}: Accept s₁ r₁ → Accept s₁ (r₁ ∪ r₂)
  | unionR {r₁ s₂ r₂}: Accept s₂ r₂ → Accept s₂ (r₁ ∪ r₂)
  | starEmpty {r}: Accept [] r*
  | starAppend {s₁ s₂ r}: Accept s₁ r → Accept s₂ r* → Accept (s₁ ++ s₂) r*

@[inherit_doc] infix:50 " =~ " => Accept

namespace Accept
variable {a : α} {s : List α} {r r₁ r₂ : RegExp α}

theorem nothing_def : ¬ s =~ nothing :=  (nomatch ·)

theorem empty_def : s =~ {} → s = []
  | empty => rfl

theorem single_def : s =~ {a} → s = [a]
  | single => rfl

theorem append_def : s =~ r₁ ++ r₂ → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s₁ =~ r₁ ∧ s₂ =~ r₂
  | append h₁ h₂ => ⟨_, _, rfl, h₁, h₂⟩

theorem union_def : s =~ r₁ ∪ r₂ → s =~ r₁ ∨ s =~ r₂
  | unionL h => .inl h
  | unionR h => .inr h

theorem cons_append (h : a::s =~ r₁ ++ r₂)
  : (∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r₁ ∧ s₂ =~ r₂) ∨ ([] =~ r₁ ∧ a::s =~ r₂)
:=
  match h.append_def with
  | ⟨[], _, rfl, h⟩ => .inr h
  | ⟨_::s₁, s₂, e, _⟩ => match e.symm with | rfl => .inl ⟨s₁, s₂, rfl, ‹_›⟩

theorem starRec {motive : ∀ {s}, s =~ r* → Prop}
  (base : motive starEmpty)
  (ind : ∀ {s₁ s₂}, (h₁ : s₁ =~ r) → (h₂ : s₂ =~ r*) → motive h₂ → motive (starAppend h₁ h₂))
  {s} (h : s =~ r*) : motive h
:= by
  generalize e : r* = r' ; rw [e] at h
  induction h
  case empty | single | append | unionL | unionR => exact nomatch e
  case starEmpty => exact base
  case starAppend s₁ s₂ r' h₁ h₂ _ ih =>
    cases e ; cases s₁
    . case nil => exact ih h rfl
    . case cons => exact ind h₁ h₂ (ih h₂ rfl)

theorem cons_star : a::s =~ r* → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r ∧ s₂ =~ r* := by
  generalize e : a::s = t
  intros h
  induction h using starRec
  case base => exact nomatch e
  case ind s₁ s₂ h₁ h₂ ih =>
    cases s₁
    . case nil => exact ih e
    . case cons => cases e ; exact ⟨_, _, rfl, h₁, h₂⟩

end Accept

protected instance match_empty : (r : RegExp α) → Decidable ([] =~ r)
  | nothing => isFalse Accept.nothing_def
  | empty => isTrue .empty
  | single _ => isFalse fun h => nomatch h.single_def
  | append r₁ r₂ =>
    match r₁.match_empty, r₂.match_empty with
    | isTrue h₁, isTrue h₂ => isTrue (h₁.append h₂)
    | isFalse hn, _ => isFalse fun h => match h.append_def with | ⟨[], _, rfl, h, _⟩ => hn h
    | _, isFalse hn => isFalse fun h => match h.append_def with | ⟨[], _, rfl, _, h⟩ => hn h
  | union r₁ r₂ =>
    match r₁.match_empty, r₂.match_empty with
    | isFalse hn₁, isFalse hn₂ => isFalse fun h => h.union_def.rec hn₁ hn₂
    | isTrue h, _ => isTrue h.unionL
    | _, isTrue h => isTrue h.unionR
  | _* => isTrue .starEmpty

section «Brzozowski derivative»
variable [DecidableEq α]

/--
- [Brzozowski derivative](https://en.wikipedia.org/wiki/Brzozowski_derivative)
- [Myhill–Nerode theorem](https://en.wikipedia.org/wiki/Myhill%E2%80%93Nerode_theorem)
-/
def derive (a : α) : RegExp α → RegExp α
  | nothing | empty => nothing
  | single b => if a = b then {} else nothing
  | append r₁ r₂ =>
    if [] =~ r₁ then (derive a r₁ ++ r₂) ∪ derive a r₂ else derive a r₁ ++ r₂
  | union r₁ r₂ => derive a r₁ ∪ derive a r₂
  | r* => derive a r ++ r*

theorem Accept.cons_derive {a s} : {r : RegExp α} → a::s =~ r → s =~ derive a r
  | nothing, h => h.nothing_def.rec
  | .empty, h => nomatch h.empty_def
  | .single _, h => match h.single_def.symm with | rfl => trans empty (if_pos rfl).symm
  | .append .., h =>
    h.cons_append.rec
    fun | ⟨_, _, h, h₁, h₂⟩ =>
          have := h ▸ h₁.cons_derive.append h₂
          iteInduction (fun _ => this.unionL) fun _ => this
    fun ⟨e, h₂⟩ => trans h₂.cons_derive.unionR (if_pos e).symm
  | union .., h => h.union_def.rec (unionL ∘ cons_derive) (unionR ∘ cons_derive)
  | _*, h => have ⟨_, _, h, h₁, h₂⟩ := h.cons_star ; h ▸ h₁.cons_derive.append h₂

theorem Accept.derive_cons {a s} : {r : RegExp α} → s =~ derive a r → a::s =~ r
  | .single b, h => if e : a = b
    then match trans h (if_pos e) with | empty => e ▸ single
    else nomatch trans h (if_neg e)
  | .append r _, h => if e : [] =~ r
    then match trans h (if_pos e) with
      | unionL (append h₁ h₂) => h₁.derive_cons.append h₂
      | unionR h => e.append h.derive_cons
    else match trans h (if_neg e) with
      | append h₁ h₂ => h₁.derive_cons.append h₂
  | union .., unionL h => h.derive_cons.unionL
  | union .., unionR h => h.derive_cons.unionR
  | _*, append h₁ h₂ => h₁.derive_cons.starAppend h₂

instance decAccept (r : RegExp α) : (s : List α) → Decidable (s =~ r)
  | [] => r.match_empty
  | a::s =>
    match decAccept (derive a r) s with
    | isTrue h => isTrue h.derive_cons
    | isFalse hn => isFalse fun h => hn h.cons_derive

end «Brzozowski derivative»

end RegExp
