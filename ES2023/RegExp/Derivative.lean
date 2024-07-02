import ES2023.RegExp.Def

namespace RegExp
universe u
variable {α : Type u}

section
variable {a b : α} {s : List α} {r r₁ r₂ : RegExp α}

theorem accept.nothing_def : ¬ s =~ nothing :=  (nomatch ·)

theorem accept.empty_def : s =~ {} → s = []
  | empty => rfl

theorem accept.single_def : s =~ {a} → s = [a]
  | single => rfl

example : a::s =~ {b} → a = b
  | h => match h.single_def with | rfl => rfl

example : a::s =~ {b} → s = []
  | h => match h.single_def with | rfl => rfl

example : s =~ nothing* → s = []
  | .starEmpty => rfl

example : s =~ r → s =~ r*
  | h => s.append_nil ▸ h.starAppend .starEmpty

theorem accept.app_exists : s =~ r₁ ++ r₂ → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ s₁ =~ r₁ ∧ s₂ =~ r₂
  | append h₁ h₂ => ⟨_, _, rfl, h₁, h₂⟩

theorem accept.union_disj : s =~ r₁ ∪ r₂ → s =~ r₁ ∨ s =~ r₂
  | unionL h => .inl h
  | unionR h => .inr h

theorem accept.cons_append
  : a::s =~ r₁ ++ r₂
  → (∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r₁ ∧ s₂ =~ r₂) ∨
    ([] =~ r₁ ∧ a::s =~ r₂)
:= by
  generalize et : a::s = t
  intro
  | .append (s₁ := []) h₁ h₂ => exact .inr ⟨h₁, h₂⟩
  | .append (s₁ := b::s₁) h₁ h₂ =>
    cases et; exact .inl ⟨_, _, rfl, h₁, h₂⟩

instance match_empty : (r : RegExp α) → Decidable ([] =~ r)
  | nothing => isFalse accept.nothing_def
  | empty => isTrue .empty
  | single _ => isFalse (nomatch accept.single_def ·)
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

theorem accept.starRec {motive : ∀ {s}, s =~ r* → Prop}
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

theorem accept.cons_star
  : a::s =~ r* → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r ∧ s₂ =~ r*
:= by
  generalize et : a::s = t
  intros h
  induction h using accept.starRec
  case base => exact nomatch et
  case ind s₁ s₂ h₁ h₂ ih =>
    cases s₁
    . case nil => exact ih et
    . case cons => cases et; exact ⟨_, _, rfl, h₁, h₂⟩

end

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

theorem accept.cons_derive {a} {s : List α} : {r : RegExp α} → a::s =~ r → s =~ derive a r
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

theorem accept.derive_cons {a} {s : List α} : {r : RegExp α} → s =~ derive a r → a::s =~ r
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
