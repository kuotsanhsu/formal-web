/-- https://en.wikipedia.org/wiki/Regular_language#Formal_definition
`α` is the type of alphabet allowed in the regular language. We make it universe-polymorphic. -/
inductive RegExp.{u} (α: Type u)
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
universe u
variable {α : Type u}

/-!
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
inductive accept: List α → RegExp α → Prop
  | empty: accept [] {}
  | single {a: α}: accept [a] {a}
  | append {s₁ r₁ s₂ r₂}
    : accept s₁ r₁ → accept s₂ r₂ → accept (s₁ ++ s₂) (r₁ ++ r₂)
  | unionL {s₁ r₁ r₂}: accept s₁ r₁ → accept s₁ (r₁ ∪ r₂)
  | unionR {r₁ s₂ r₂}: accept s₂ r₂ → accept s₂ (r₁ ∪ r₂)
  | starEmpty {r}: accept [] r*
  | starAppend {s₁ s₂ r}: accept s₁ r → accept s₂ r* → accept (s₁ ++ s₂) r*

@[inherit_doc] infix:50 " =~ " => accept

end RegExp
