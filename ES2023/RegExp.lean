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

theorem single_def : s =~ {a} → s = [a]
  | single => rfl

theorem append_def : s =~ r₁ ++ r₂ → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s₁ =~ r₁ ∧ s₂ =~ r₂
  | append h₁ h₂ => ⟨_, _, rfl, h₁, h₂⟩

theorem union_def : s =~ r₁ ∪ r₂ → s =~ r₁ ∨ s =~ r₂
  | unionL h => .inl h
  | unionR h => .inr h

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
  | append r₁ r₂ => if [] =~ r₁ then (derive a r₁ ++ r₂) ∪ derive a r₂ else derive a r₁ ++ r₂
  | union r₁ r₂ => derive a r₁ ∪ derive a r₂
  | r* => derive a r ++ r*

theorem Accept.cons_derive {a s t} (e : t = a::s) : {r : RegExp α} → t =~ r → s =~ derive a r
  | .empty, empty => nomatch e
  | .single b, single => match e with | rfl => trans empty (if_pos rfl).symm
  | .append r₁ r₂, append (s₁ := []) h₁ h₂ => trans (h₂.cons_derive e).unionR (if_pos h₁).symm
  | .append r₁ r₂, append (s₁ := b::s₁) h₁ h₂ =>
    match e with | rfl => have := (h₁.cons_derive rfl).append h₂
      iteInduction (fun _ => this.unionL) fun _ => this
  | union r₁ r₂, unionL h => (h.cons_derive e).unionL
  | union r₁ r₂, unionR h => (h.cons_derive e).unionR
  | r*, starAppend (s₁ := []) h₁ h₂ => sorry -- h₂.cons_derive e
  | r*, starAppend (s₁ := b::s₁) h₁ h₂ => match e with | rfl => (h₁.cons_derive rfl).append h₂

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
    | isFalse hn => isFalse fun h => hn (h.cons_derive rfl)

end «Brzozowski derivative»

end RegExp
