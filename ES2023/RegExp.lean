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
variable {a b : α} {s : List α} {r r₁ r₂ : RegExp α}

theorem nothing_def : ¬ s =~ nothing :=  (nomatch ·)

theorem empty_def : s =~ {} → s = []
  | empty => rfl

theorem single_def : s =~ {a} → s = [a]
  | single => rfl

theorem app_exists : s =~ r₁ ++ r₂ → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s₁ =~ r₁ ∧ s₂ =~ r₂
  | append h₁ h₂ => ⟨_, _, rfl, h₁, h₂⟩

theorem union_disj : s =~ r₁ ∪ r₂ → s =~ r₁ ∨ s =~ r₂
  | unionL h => .inl h
  | unionR h => .inr h

theorem cons_append
  : a::s =~ r₁ ++ r₂
  → (∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r₁ ∧ s₂ =~ r₂) ∨
    ([] =~ r₁ ∧ a::s =~ r₂)
:= by
  generalize et : a::s = t
  intro
  | .append (s₁ := []) h₁ h₂ => exact .inr ⟨h₁, h₂⟩
  | .append (s₁ := b::s₁) h₁ h₂ =>
    cases et; exact .inl ⟨_, _, rfl, h₁, h₂⟩

theorem starRec {motive : ∀ {s}, s =~ r* → Prop}
  (base : motive .starEmpty)
  (ind : ∀ {s₁ s₂}, (h₁ : s₁ =~ r) → (h₂ : s₂ =~ r*)
    → motive h₂ → motive (h₁.starAppend h₂))
  {s} (h : s =~ r*) : motive h
:= by
  generalize er : r* = r; rw [er] at h
  induction h
  case empty | single | append | unionL | unionR => exact nomatch er
  case starEmpty => exact base
  case starAppend s₁ s₂ _ h₁ h₂ _ ih =>
    cases er; cases s₁
    . case nil => exact ih h rfl
    . case cons => exact ind h₁ h₂ (ih h₂ rfl)

theorem cons_star
  : a::s =~ r* → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r ∧ s₂ =~ r*
:= by
  generalize et : a::s = t
  intros h
  induction h using starRec
  case base => exact nomatch et
  case ind s₁ s₂ h₁ h₂ ih =>
    cases s₁
    . case nil => exact ih et
    . case cons => cases et; exact ⟨_, _, rfl, h₁, h₂⟩

end Accept

instance match_empty : (r : RegExp α) → Decidable ([] =~ r)
  | nothing => isFalse Accept.nothing_def
  | empty => isTrue .empty
  | single _ => isFalse (nomatch Accept.single_def ·)
  | append r₁ r₂ =>
    match match_empty r₁, match_empty r₂ with
    | isTrue h₁, isTrue h₂ => isTrue (h₁.append h₂)
    | isFalse hn, _ => isFalse fun h =>
      have ⟨_, _, e, h, _⟩ := h.app_exists
      hn <| (List.append_eq_nil.mp e.symm).1 ▸ h
    | _, isFalse hn => isFalse fun h =>
      have ⟨_, _, e, _, h⟩ := h.app_exists
      hn <| (List.append_eq_nil.mp e.symm).2 ▸ h
  | union r₁ r₂ =>
    match match_empty r₁, match_empty r₂ with
    | isFalse hn₁, isFalse hn₂ => isFalse fun h => h.union_disj.rec hn₁ hn₂
    | isTrue h, _ => isTrue h.unionL
    | _, isTrue h => isTrue h.unionR
  | _* => isTrue .starEmpty

section
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

theorem Accept.cons_derive {a} {s : List α} : {r : RegExp α} → a::s =~ r → s =~ derive a r
  | nothing, h => h.nothing_def.rec
  | .empty, h => nomatch h.empty_def
  | .single _, h => match h.single_def.symm with | rfl => trans empty (if_pos rfl).symm
  | .append .., h =>
    h.cons_append.rec
    fun | ⟨_, _, h, h₁, h₂⟩ =>
          have := h ▸ h₁.cons_derive.append h₂
          iteInduction (fun _ => this.unionL) fun _ => this
    fun ⟨e, h₂⟩ => trans h₂.cons_derive.unionR (if_pos e).symm
  | union .., h => h.union_disj.rec (unionL ∘ cons_derive) (unionR ∘ cons_derive)
  | _*, h => have ⟨_, _, h, h₁, h₂⟩ := h.cons_star ; h ▸ h₁.cons_derive.append h₂

theorem Accept.derive_cons {a} {s : List α} : {r : RegExp α} → s =~ derive a r → a::s =~ r
  | .single b, h => if e : a = b
    then match trans h (if_pos e) with | empty => e ▸ single
    else nomatch trans h (if_neg e)
  | .append r _, h => if e : [] =~ r
    then match trans h (if_pos e) with
      | unionL (append h₁ h₂) => h₁.derive_cons.append h₂
      | unionR h₂ => e.append h₂.derive_cons
    else match trans h (if_neg e) with
      | append h₁ h₂ => h₁.derive_cons.append h₂
  | union .., unionL h => h.derive_cons.unionL
  | union .., unionR h => h.derive_cons.unionR
  | _*, append h₁ h₂ => h₁.derive_cons.starAppend h₂

instance decAccept (s : List α) (r : RegExp α) : Decidable (s =~ r) :=
  match s with
  | [] => r.match_empty
  | a::s =>
    match decAccept s (derive a r) with
    | isTrue h => isTrue h.derive_cons
    | isFalse hn => isFalse fun h => hn h.cons_derive
end

end RegExp
