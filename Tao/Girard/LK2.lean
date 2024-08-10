inductive Perm {α} : List α → List α → Prop
  | nil : Perm [] []
  | cons {a xs ys} : Perm xs ys → Perm (a::xs) (a::ys)
  | swap {x y xs ys} : Perm xs ys → Perm (x::y::ys) (y::x::xs)

inductive Formula
  -- | not (A : Formula)
  | and (A B : Formula)
  -- | or (A B : Formula)

inductive LK : List Formula → List Formula → Prop
  /- Identity rules -/
  -- | identity {A} : LK [A] [A]
  | cut {A Γ Δ Γ' Δ'} : LK (A::Γ) Δ → LK Γ' (A::Δ') → LK (Γ++Γ') (Δ'++Δ)
  /- Structural rules -/
  -- | exchange {Γ Δ Γ' Δ'} : LK Γ Δ → Perm Γ Γ' → Perm Δ Δ' → LK Γ' Δ'
  -- | weakening {Γ Δ A} : LK Γ Δ → LK Γ (A::Δ)
  -- | weakening' {A Γ Δ} : LK Γ Δ → LK (A::Γ) Δ
  -- | contraction {Γ Δ A} : LK Γ (A::A::Δ) → LK Γ (A::Δ)
  -- | contraction' {A Γ Δ} : LK (A::A::Γ) Δ → LK (A::Γ) Δ
  /- Logical rules -/
  -- | negation {A Γ Δ} : LK (A::Γ) Δ → LK Γ (.not A::Δ)
  -- | negation' {Γ Δ A} : LK Γ (A::Δ) → LK (.not A::Γ) Δ
  | conjunction {Γ Δ A B} : LK Γ (A::Δ) → LK Γ (B::Δ) → LK Γ (.and A B::Δ)
  | conjunction'l {A B Γ Δ} : LK (A::Γ) Δ → LK (.and A B::Γ) Δ
  | conjunction'r {A B Γ Δ} : LK (B::Γ) Δ → LK (.and A B::Γ) Δ
  -- | disjunctionl {Γ Δ A B} : LK Γ (A::Δ) → LK Γ (.or A B::Δ)
  -- | disjunctionr {Γ Δ A B} : LK Γ (B::Δ) → LK Γ (.or A B::Δ)
  -- | disjunction' {A B Γ Δ} : LK (A::Γ) Δ → LK (B::Γ) Δ → LK (.or A B::Γ) Δ


inductive LK' : List Formula → List Formula → Prop
  /- Identity rules -/
  -- | identity {A} : LK' [A] [A]
  /- Structural rules -/
  -- | exchange {Γ Δ Γ' Δ'} : LK' Γ Δ → Perm Γ Γ' → Perm Δ Δ' → LK' Γ' Δ'
  -- | weakening {Γ Δ A} : LK' Γ Δ → LK' Γ (A::Δ)
  -- | weakening' {A Γ Δ} : LK' Γ Δ → LK' (A::Γ) Δ
  -- | contraction {Γ Δ A} : LK' Γ (A::A::Δ) → LK' Γ (A::Δ)
  -- | contraction' {A Γ Δ} : LK' (A::A::Γ) Δ → LK' (A::Γ) Δ
  /- Logical rules -/
  -- | negation {A Γ Δ} : LK' (A::Γ) Δ → LK' Γ (.not A::Δ)
  -- | negation' {Γ Δ A} : LK' Γ (A::Δ) → LK' (.not A::Γ) Δ
  | conjunction {Γ Δ A B} : LK' Γ (A::Δ) → LK' Γ (B::Δ) → LK' Γ (.and A B::Δ)
  | conjunction'l {A B Γ Δ} : LK' (A::Γ) Δ → LK' (.and A B::Γ) Δ
  | conjunction'r {A B Γ Δ} : LK' (B::Γ) Δ → LK' (.and A B::Γ) Δ
  -- | disjunctionl {Γ Δ A B} : LK' Γ (A::Δ) → LK' Γ (.or A B::Δ)
  -- | disjunctionr {Γ Δ A B} : LK' Γ (B::Δ) → LK' Γ (.or A B::Δ)
  -- | disjunction' {A B Γ Δ} : LK' (A::Γ) Δ → LK' (B::Γ) Δ → LK' (.or A B::Γ) Δ

theorem LK.Hauptsatz {Γ Δ} : LK Γ Δ → LK' Γ Δ
  -- | @cut Γ Δ (.and A B) Γ' Δ' (@cut [] [] _ _ _ h h') _ => _
  -- | @cut Γ Δ (.and A B) Γ' Δ' (@cut [] (_::[]) _ _ _ h h') _ => _
  | @cut (.and A B) Γ Δ Γ' Δ' (conjunction'l h') (conjunction h₁ h₂) => _
  | @cut (.and A B) Γ Δ Γ' Δ' (conjunction'r h') (conjunction h₁ h₂) => _
  | @cut _ _ _ _ _ (@cut _ [] _ _ _ h h') (@cut _ _ _ _ [] g g') => _
    -- match h with
    -- | conjunction h₁ h₂ => _
  -- | @cut Γ Δ A Γ' Δ' h h' => sorry
  | _ => sorry

#check List.append
