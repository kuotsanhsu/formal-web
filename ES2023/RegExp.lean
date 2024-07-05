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
  | empty: Accept [] empty
  | single {a: α}: Accept [a] (single a)
  | append {s₁ r₁ s₂ r₂}
    : Accept s₁ r₁ → Accept s₂ r₂ → Accept (s₁ ++ s₂) (r₁ ++ r₂)
  | unionL {s₁ r₁ r₂}: Accept s₁ r₁ → Accept s₁ (r₁ ∪ r₂)
  | unionR {r₁ s₂ r₂}: Accept s₂ r₂ → Accept s₂ (r₁ ∪ r₂)
  | starEmpty {r}: Accept [] r*
  | starAppend {s₁ s₂ r}: Accept s₁ r → Accept s₂ r* → Accept (s₁ ++ s₂) r*

@[inherit_doc] infix:50 " =~ " => Accept

instance (r : RegExp α) : Decidable ([] =~ r) :=
  accept_nil rfl r
where accept_nil {s} : [] = s → (r : RegExp α) → Decidable (s =~ r)
  | _, nothing => isFalse nofun
  | rfl, empty => isTrue .empty
  | e, single _ => isFalse fun | .single => nomatch e
  | e, append r₁ r₂ =>
    match e, accept_nil rfl r₁, accept_nil rfl r₂ with
    | rfl, isTrue h₁, isTrue h₂ => isTrue (h₁.append h₂)
    | e, isFalse hn, _ => isFalse fun | .append h _ => hn ((List.nil_eq_append.mp e).1 ▸ h)
    | e, _, isFalse hn => isFalse fun | .append _ h => hn ((List.nil_eq_append.mp e).2 ▸ h)
  | e, union r₁ r₂ =>
    match e, accept_nil rfl r₁, accept_nil rfl r₂ with
    | e, isFalse hn₁, isFalse hn₂ => isFalse fun | .unionL h => hn₁ (e ▸ h) | .unionR h => hn₂ (e ▸ h)
    | rfl, isTrue h, _ => isTrue h.unionL
    | rfl, _, isTrue h => isTrue h.unionR
  | rfl, _* => isTrue .starEmpty

section «Brzozowski derivative»
variable [DecidableEq α]

/--
- [Brzozowski derivative](https://en.wikipedia.org/wiki/Brzozowski_derivative)
- [Myhill–Nerode theorem](https://en.wikipedia.org/wiki/Myhill%E2%80%93Nerode_theorem)
-/
def derive (a : α) : RegExp α → RegExp α
  | nothing | empty => nothing
  | single b => if a = b then empty else nothing
  | append r₁ r₂ => if [] =~ r₁ then (derive a r₁ ++ r₂) ∪ derive a r₂ else derive a r₁ ++ r₂
  | union r₁ r₂ => derive a r₁ ∪ derive a r₂
  | r* => derive a r ++ r*

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

instance decAccept (r : RegExp α) : (s : List α) → Decidable (s =~ r)
  | [] => inferInstance
  | a::s =>
    match decAccept (derive a r) s with
    | isTrue h => isTrue h.derive_cons
    | isFalse hn => isFalse fun h => hn (h.cons_derive rfl)

end «Brzozowski derivative»

end RegExp
