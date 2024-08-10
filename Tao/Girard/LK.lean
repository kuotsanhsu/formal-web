inductive Perm {α} : List α → List α → Prop
  -- | refl {xs} : Perm xs xs
  -- | trans {xs ys zs} : Perm xs ys → Perm ys zs → Perm xs zs
  | nil : Perm [] []
  | cons {a xs ys} : Perm xs ys → Perm (a::xs) (a::ys)
  | swap {x y xs ys} : Perm xs ys → Perm (x::y::ys) (y::x::xs)

inductive Formula
  -- | verum
  -- | falsum
  | var (deBruijn : Nat)
  | not (A : Formula)
  | and (A B : Formula)
  | or (A B : Formula)
  -- | forall (A : Formula)
  -- | exists (A : Formula)

-- structure Sequent where
--   hypothesis : List Formula
--   consequence : List Formula

inductive LK : List Formula → List Formula → Prop
  /- Identity rules -/
  | identity {A} : LK [A] [A]
  | cut {Γ Δ A Γ' Δ'} : LK Γ (Δ++[A]) → LK (A::Γ') Δ' → LK (Γ++Γ') (Δ++Δ')
  /- Structural rules -/
  | exchange {Γ Δ Γ' Δ'} : LK Γ Δ → Perm Γ Γ' → Perm Δ Δ' → LK Γ' Δ'
  | weakening {Γ Δ A} : LK Γ Δ → LK Γ (Δ++[A])
  | weakening' {A Γ Δ} : LK Γ Δ → LK (A::Γ) Δ
  | contraction {Γ Δ A} : LK Γ (Δ++[A, A]) → LK Γ (Δ++[A])
  | contraction' {A Γ Δ} : LK (A::A::Γ) Δ → LK (A::Γ) Δ
  /- Logical rules -/
  | negation {A Γ Δ} : LK (A::Γ) Δ → LK Γ (Δ++[A.not])
  | negation' {Γ Δ A} : LK Γ (Δ++[A]) → LK (A.not::Γ) Δ
  | conjunction {Γ Δ A B} : LK Γ (Δ++[A]) → LK Γ (Δ++[B]) → LK Γ (Δ++[A.and B])
  | conjunction'l {A B Γ Δ} : LK (A::Γ) Δ → LK (.and A B::Γ) Δ
  | conjunction'r {A B Γ Δ} : LK (B::Γ) Δ → LK (.and A B::Γ) Δ
  | disjunctionl {Γ Δ A B} : LK Γ (Δ++[A]) → LK Γ (Δ++[.or A B])
  | disjunctionr {Γ Δ A B} : LK Γ (Δ++[B]) → LK Γ (Δ++[.or A B])
  | disjunction' {A B Γ Δ} : LK (A::Γ) Δ → LK (B::Γ) Δ → LK (.or A B::Γ) Δ
  -- | forall {Γ Δ A} : LK Γ (Δ++[A]) → LK Γ (Δ++[.forall A])
  -- | forall' {A Γ Δ} : LK (A::Γ) Δ → LK (.forall A::Γ) Δ
  -- | exists {Γ Δ A} : LK Γ (Δ++[A]) → LK Γ (Δ++[.exists A])
  -- | exists' {A Γ Δ} : LK (A::Γ) Δ → LK (.exists A::Γ) Δ

inductive Subformula : Formula → Formula → Prop
  | not {A} : Subformula A A.not
  | andl {A B} : Subformula A (.and A B)
  | andr {A B} : Subformula B (.and A B)
  | orl {A B} : Subformula A (.or A B)
  | orr {A B} : Subformula B (.or A B)
  -- | forall {A} : Subformula A (.forall A)
  -- | exits {A} : Subformula A (.exists A)

namespace LK
variable {A B C : Formula}

def modus_ponens : LK [] [A] → LK [A] [B] → LK [] [B] := @cut [] [] A [] [B]
def transitivity : LK [A] [B] → LK [B] [C] → LK [A] [C] := @cut [A] [] B [] [C]

end LK

inductive LK' : List Formula → List Formula → Prop
  /- Identity rules -/
  | identity {A} : LK' [A] [A]
  /- Structural rules -/
  | exchange {Γ Δ Γ' Δ'} : LK' Γ Δ → Perm Γ Γ' → Perm Δ Δ' → LK' Γ' Δ'
  | weakening {Γ Δ A} : LK' Γ Δ → LK' Γ (Δ++[A])
  | weakening' {A Γ Δ} : LK' Γ Δ → LK' (A::Γ) Δ
  | contraction {Γ Δ A} : LK' Γ (Δ++[A, A]) → LK' Γ (Δ++[A])
  | contraction' {A Γ Δ} : LK' (A::A::Γ) Δ → LK' (A::Γ) Δ
  /- Logical rules -/
  | negation {A Γ Δ} : LK' (A::Γ) Δ → LK' Γ (Δ++[A.not])
  | negation' {Γ Δ A} : LK' Γ (Δ++[A]) → LK' (A.not::Γ) Δ
  | conjunction {Γ Δ A B} : LK' Γ (Δ++[A]) → LK' Γ (Δ++[B]) → LK' Γ (Δ++[A.and B])
  | conjunction'l {A B Γ Δ} : LK' (A::Γ) Δ → LK' (.and A B::Γ) Δ
  | conjunction'r {A B Γ Δ} : LK' (B::Γ) Δ → LK' (.and A B::Γ) Δ
  | disjunctionl {Γ Δ A B} : LK' Γ (Δ++[A]) → LK' Γ (Δ++[.or A B])
  | disjunctionr {Γ Δ A B} : LK' Γ (Δ++[B]) → LK' Γ (Δ++[.or A B])
  | disjunction' {A B Γ Δ} : LK' (A::Γ) Δ → LK' (B::Γ) Δ → LK' (.or A B::Γ) Δ
  -- | forall {Γ Δ A} : LK' Γ (Δ++[A]) → LK' Γ (Δ++[.forall A])
  -- | forall' {A Γ Δ} : LK' (A::Γ) Δ → LK' (.forall A::Γ) Δ
  -- | exists {Γ Δ A} : LK' Γ (Δ++[A]) → LK' Γ (Δ++[.exists A])
  -- | exists' {A Γ Δ} : LK' (A::Γ) Δ → LK' (.exists A::Γ) Δ

theorem LK.Hauptsatz : ∀ {Γ Δ}, LK Γ Δ → LK' Γ Δ
  -- | @cut Γ Δ (.and A B) Γ' Δ' (@conjunction _ _ _ _ h h') (conjunction'l ..) => _
  | _, _, cut (conjunction h₁ h₁') (conjunction'l h₂) => _
  -- | @cut Γ Δ A Γ' Δ' h h' => sorry
  -- cut {Γ Δ A Γ' Δ'} : LK Γ (Δ++[A]) → LK (A::Γ') Δ' → LK (Γ++Γ') (Δ++Δ')
  | _, _, _ => sorry
