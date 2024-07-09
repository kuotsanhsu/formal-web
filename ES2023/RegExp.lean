universe u

/-- https://en.wikipedia.org/wiki/Regular_language#Formal_definition
`α` is the type of alphabet allowed in the regular language. We make it universe-polymorphic. -/
inductive RegExp (α : Type u)
  /-- Matches nothing. -/
  | nothing
  /-- Empty string matcher. -/
  | empty
  | single (a : α)
  /-- `/ab/` -/
  | append (r₁ r₂ : RegExp α)
  /-- `/a|b/`-/
  | union (r₁ r₂ : RegExp α)
  | star (r : RegExp α)

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
inductive Accept : List α → RegExp α → Prop
  | empty : Accept [] empty
  | single {a: α} : Accept [a] (single a)
  | append {s₁ r₁ s₂ r₂} : Accept s₁ r₁ → Accept s₂ r₂ → Accept (s₁ ++ s₂) (r₁ ++ r₂)
  | unionL {s₁ r₁ r₂} : Accept s₁ r₁ → Accept s₁ (r₁ ∪ r₂)
  | unionR {r₁ s₂ r₂} : Accept s₂ r₂ → Accept s₂ (r₁ ∪ r₂)
  | starEmpty {r} : Accept [] r*
  | starAppend {s₁ s₂ r} : Accept s₁ r → Accept s₂ r* → Accept (s₁ ++ s₂) r*

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
    match e.symm, accept_nil rfl r₁, accept_nil rfl r₂ with
    | rfl, isFalse hn₁, isFalse hn₂ => isFalse fun | .unionL h => hn₁ h | .unionR h => hn₂ h
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
  | append r₁ r₂ => (derive a r₁ ++ r₂) ∪ if [] =~ r₁ then derive a r₂ else nothing
  | union r₁ r₂ => derive a r₁ ∪ derive a r₂
  | r* => derive a r ++ r*

theorem Accept.derive_cons {a s} : {r : RegExp α} → s =~ derive a r → a::s =~ r
  | .single b, h => if e : a = b
    then match trans h (if_pos e) with | empty => e ▸ single
    else nomatch trans h (if_neg e)
  | .append _ _, unionL (append h₁ h₂) => h₁.derive_cons.append h₂
  | .append r _, unionR h => if e : [] =~ r
    then e.append (trans h (if_pos e)).derive_cons
    else nomatch trans h (if_neg e)
  | union .., unionL h => h.derive_cons.unionL
  | union .., unionR h => h.derive_cons.unionR
  | _*, append h₁ h₂ => h₁.derive_cons.starAppend h₂

theorem Accept.starRec {r : RegExp α} {motive : ∀ {s}, s =~ r* → Prop}
  (base : motive starEmpty)
  (ind : ∀ {s₁ s₂}, (h₁ : s₁ =~ r) → (h₂ : s₂ =~ r*) → motive h₂ → motive (starAppend h₁ h₂))
  {s} (h : s =~ r*) : motive h
:= by
  generalize e : r* = r' ; rw [e] at h
  induction h with
  | empty | single | append | unionL | unionR => nomatch e
  | starEmpty => exact base
  | starAppend h₁ h₂ _ ih => cases e ; exact ind h₁ h₂ (ih h₂ rfl)

theorem Accept.cons_star {a s} {r : RegExp α} (h : a::s =~ r*)
  : ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r ∧ s₂ =~ r*
:=
  h.starRec trivial (motive := fun {s} _ =>
    s.casesOn True fun a s => ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a :: s₁ =~ r ∧ s₂ =~ r*
  ) fun {s₁ _} h₁ h₂ ih => match s₁ with | [] => ih | _::_ => ⟨_, _, rfl, h₁, h₂⟩

example {a s} {r : RegExp α} (h : a::s =~ r*)
  : ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r ∧ s₂ =~ r*
:= by
  generalize e : a::s = t at h
  induction h using Accept.starRec with
  | base => nomatch e
  | @ind s₁ s₂ h₁ h₂ ih =>
    exact match s₁, e.symm with | [], _ => ih e | _::_, rfl => ⟨_, _, rfl, h₁, h₂⟩

/-
List.rec {motive : List α → Sort _}
  (nil : motive [])
  (cons : (a : α) → (s : List α) → motive s → motive (a::s))
  (s) : motive s
-/
#check List.rec
def List.appendRec {motive : List α → Sort _}
  (ind : (left right : List α) → motive left → motive right → motive (left ++ right))
  (s) : motive s
:= sorry


theorem Accept.cons_derive {a s t} {r : RegExp α} (e : t = a::s) : t =~ r → s =~ derive a r
  | empty => nomatch e
  | single => match e with | rfl => trans empty (if_pos rfl).symm
  | append (s₁ := []) h₁ h₂ => unionR <| trans (h₂.cons_derive e) (if_pos h₁).symm
  | append (s₁ := _::_) h₁ h₂ => match e with | rfl => unionL <| (h₁.cons_derive rfl).append h₂
  | unionL h => (h.cons_derive e).unionL
  | unionR h => (h.cons_derive e).unionR
  | h@(starAppend _ _) =>
    -- e : s₁✝ ++ s₂✝ = a :: s
    -- ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a :: s₁ =~ r✝ ∧ s₂ =~ r✝*
    match s, (e ▸ h).cons_star with
    /-
    w✝¹ w✝ : List α
    e : s₁✝ ++ s₂✝ = a :: (w✝¹ ++ w✝)
    ⊢ w✝¹ ++ w✝ =~ derive a r✝*
    -/
    | _, ⟨_, _, rfl, h₁, h₂⟩ => _ -- (h₁.cons_derive rfl).append h₂
    /-
    x✝ w✝¹ w✝ : List α
    e : x✝ = w✝¹ ++ w✝
    e✝ : s₁✝ ++ s₂✝ = a :: x✝
    ⊢ x✝ =~ derive a r✝*
    -/

instance decAccept (r : RegExp α) : (s : List α) → Decidable (s =~ r)
  | [] => inferInstance
  | a::s =>
    match decAccept (derive a r) s with
    | isTrue h => isTrue h.derive_cons
    | isFalse hn => isFalse fun h => hn (h.cons_derive rfl)

end «Brzozowski derivative»

end RegExp
