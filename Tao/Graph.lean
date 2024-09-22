/-
* https://leanprover-community.github.io/undergrad.html
-/

class Graph.{u} where
  V : Sort u
  E : V → V → Prop

structure MatGraph (n : Nat) where
  adj : Array (Array Bool)
  rows : n = adj.size
  cols : (h : 0 < n) → n = (adj.get ⟨0, trans h rows⟩).size

structure AdjGraph (n : Nat) where
  adj : Array (Array (Fin n))
  len : n = adj.size
  -- E := fun u v => v ∈ adj.get (congrArg Fin sizeDef ▸ u)

instance FinGraph.toGraph {n} (g : AdjGraph n) : Graph where
  V := Fin n
  E u v := v ∈ g.adj.get (cast (congrArg Fin g.len) u)
#check Array.Mem

/-
structure AdjGraph (n : Nat) where
  adj : Array (Array (Fin n))
  sizeDef : adj.size = n

namespace AdjGraph
variable {n : Nat} (g : AdjGraph n)

def V (_ : AdjGraph n) := Fin n
theorem defV : g.V = Fin g.adj.size :=
  show Fin n = Fin g.adj.size from congrArg Fin g.sizeDef.symm
def E (u v : g.V) : Prop := v ∈ g.adj.get (g.defV ▸ u)

end AdjGraph
-/

class Matrix.{u} (m n : Nat) (α : Sort u) where
  get : Fin m → Fin n → α

class Zero (α) where
  zero : α
instance {α} [self : Zero α] : OfNat α 0 where
  ofNat := self.zero

class One (α) where
  one : α
instance {α} [self : One α] : OfNat α 1 where
  ofNat := self.one

class Inv (α) where
  inv : α → α
postfix:arg "⁻¹" => Inv.inv

abbrev Nonzero (α) [Zero α] := {a : α // a ≠ 0}
postfix:arg "ˣ" => Nonzero

namespace Try1

class Field (α) extends Add α, Zero α, Neg α, Mul α, One α, Inv αˣ where
  zero_ne_one : (0 : α) ≠ 1
  mul_add {a b c : α} : a * (b + c) = a * b + a * c
  add_assoc {a b c : α} : a + b + c = a + (b + c)
  add_comm {a b : α} : a + b = b + a
  add_zero {a : α} : a + 0 = a
  add_neg {a : α} : a + (-a) = 0
  mul_assoc {a b c : α} : a * b * c = a * (b * c)
  mul_comm {a b : α} : a * b = b * a
  mul_one {a : α} : a * 1 = a
  mul_inv {a : αˣ} : (a : α) * a⁻¹ = 1

class Lin.{u, v} (β : Type v) extends Add β, Zero β, Neg β where
  add_assoc {x y z : β} : x + y + z = x + (y + z)
  add_comm {x y : β} : x + y = y + x
  add_zero {x : β} : x + 0 = x
  add_neg {x : β} : x + (-x) = 0
  α : Type u
  [scalar : Field α]
  [mul : HMul α β β]
  mul_assoc {a b : α} {x : β} : a * b * x = a * (b * x)
  one_mul {x : β} : (1 : α) * x = x
  mul_add {a : α} {x y : β} : a * (x + y) = a * x + a * y
  add_mul {a b : α} {x : β} : (a + b) * x = a * x + b * x

end Try1

namespace Try2

class AddGrp (α) extends Add α, Zero α, Neg α where
  add_assoc {a b c : α} : a + b + c = a + (b + c)
  add_neg {a : α} : a + (-a) = 0
  add_zero {a : α} : a + 0 = a

class AddAb (α) extends AddGrp α where
  add_comm {a b : α} : a + b = b + a

class MulMonoid (α) extends Mul α, One α where
  mul_assoc {a b c : α} : a * b * c = a * (b * c)
  mul_one {a : α} : a * 1 = a
  one_mul {a : α} : 1 * a = a

class MulCommMonoid (α) extends MulMonoid α where
  mul_comm {a b : α} : a * b = b * a
  one_mul := trans mul_comm mul_one

class Ring (α) extends AddAb α, MulMonoid α where
  mul_add {a b c : α} : a * (b + c) = a * b + a * c
  add_mul {a b c : α} : (a + b) * c = a * c + b * c

class Module (α β) [Ring α] [AddAb β] extends HMul α β β where
  mul_assoc {a b : α} {x : β} : a * b * x = a * (b * x)
  one_mul {x : β} : (1 : α) * x = x
  mul_add {a : α} {x y : β} : a * (x + y) = a * x + a * y
  add_mul {a b : α} {x : β} : (a + b) * x = a * x + b * x

class Field (α) extends AddAb α, MulCommMonoid α, Inv αˣ where
  zero_ne_one : (0 : α) ≠ 1
  mul_add {a b c : α} : a * (b + c) = a * b + a * c
  mul_inv {a : αˣ} : (a : α) * a⁻¹ = 1

class Lin (α β) [Field α] [AddAb β] extends HMul α β β where
  mul_assoc {a b : α} {x : β} : a * b * x = a * (b * x)
  one_mul {x : β} : (1 : α) * x = x
  mul_add {a : α} {x y : β} : a * (x + y) = a * x + a * y
  add_mul {a b : α} {x : β} : (a + b) * x = a * x + b * x

namespace Lin
variable {F V} [Field F] [AddAb V] [Lin F V]

inductive Comb : List (F × V) → V → Prop
  | nil : Comb [] 0
  | cons {a x u s} : Comb s u → Comb ((a, x)::s) (u + a * x)

def Indep (xs : List V) : Prop :=
  ∀ as : List F, Comb (as.zip xs) 0 → ∀ a ∈ as, a = 0

-- structure IsBasis (xs : List V) : Prop where
--   indep : Indep xs

-- def Indep (xs : List V) : Prop :=
--   ∀ as : List F, (as.zip xs).foldr (fun (a, x) u => a * x + u) 0 = 0 → ∀ a ∈ as, a = 0

-- inductive Indep : List V → Prop
--   | nil : Indep []
--   | cons {x xs} : Indep xs
--     → (∀ as : List F, (as.zip xs).foldr (fun (a, x) u => a * x + u) 0 ≠ x)
--     → Indep (x::xs)



section
variable (F) [Field F]
variable (U) [AddAb U] [Lin F U]
variable (V) [AddAb V] [Lin F V]
variable (W) [wAdd : AddAb W] [wMul : Lin F W]

structure Hom where
  f : V → W
  addVec {x y : V} : f (x + y) = f x + f y
  scale {a : F} {x : V} : f (a * x) = a * f x

namespace Hom
instance : CoeFun (Hom F V W) (fun _ => V → W) where
  coe h := h.f

-- instance : CoeFun (Hom F V W) (fun _ => Hom F U V → U → W) where
--   coe A B x := A (B x)

def add (A B : Hom F V W) : Hom F V W where
  f x := A x + B x
  addVec {x y} :=
    calc  A (x + y)  + B (x + y)
      _ = A x +  A y +      _      := congrArg (· + _) A.addVec
      _ =     _      + (B x + B y) := congrArg _ B.addVec
      _ = ( _ +  A y + B x) + _  := wAdd.add_assoc.symm
      _ =   _ + (A y + B x) + _  := congrArg (· + _) wAdd.add_assoc
      _ =   _ + (B x + A y) + _  := congrArg (_ + · + _) wAdd.add_comm
      _ = ( _ +   _  +  _ ) + _  := congrArg (· + _) wAdd.add_assoc.symm
      _ =   _ +   _ + ( _   + _) := wAdd.add_assoc
  scale {a x} :=
    calc  A (a * x) + B (a * x)
      _ = a * A x   + _       := congrArg (· + _) A.scale
      _ =     _     + a * B x := congrArg _ B.scale
      _ = a * (A x + B x)     := wMul.mul_add.symm
-- instance : Add (Hom F V W) where
--   add := add

def mul (A : Hom F V W) (B : Hom F U V) : Hom F U W where
  f x := A (B x)
  addVec {x y} :=
    calc  A (B (x + y))
      _ = A (B x + B y) := congrArg _ B.addVec
      _ = A (B x) + A (B y) := A.addVec
  scale {a x} :=
    calc  A (B (a * x))
      _ = A (a * B x) := congrArg _ B.scale
      _ = a * A (B x) := A.scale

end Hom

end

end Lin

end Try2

namespace Try3

#check Std.Commutative

-- structure Magma {α} (op : α → α → α) : Prop where

class Semigroup {α} (op : α → α → α) : Prop where
  assoc {a b c : α} : op (op a b) c = op a (op b c)

structure Monoid {α} (op : α → α → α) (id : α)
extends Semigroup op : Prop where
  idl {a : α} : op id a = a
  idr {a : α} : op a id = a

structure Group {α} (op : α → α → α) (id : α) (inv : α → α)
extends Monoid op id : Prop where
  invl {a : α} : op (inv a) a = id
  invr {a : α} : op a (inv a) = id

structure Comm {α} (op : α → α → α) : Prop where
  comm {a b : α} : op a b = op b a

structure CommMonoid {α} (op : α → α → α) (id : α)
extends Comm op, Monoid op id where
  idr := trans comm idl

structure CommGroup {α} (op : α → α → α) (id : α) (inv : α → α)
extends Comm op, Group op id inv : Prop where
  idr := trans comm idl
  invr := trans comm invl

class RingLike (α) extends Add α, Zero α, Neg α, Mul α, One α

structure Ring (α) [skel : RingLike α] : Prop where
  add : CommGroup skel.add 0 skel.neg
  mul : Monoid skel.mul 1
  mul_add {a b c : α} : a * (b + c) = a * b + a * c
  add_mul {a b c : α} : (a + b) * c = a * c + b * c

-- structure CommRing (α) [skel : RingLike α] extends Ring α : Prop where
--   comm : CommMonoid skel.mul 1

class FieldLike (α) extends RingLike α, Inv αˣ

structure Field (α) [FieldLike α] extends Ring α : Prop where
  zero_ne_one : (0 : α) ≠ 1
  mul_comm {a b : α} : a * b = b * a
  add_mul {a b c} :=
    calc  (a + b) * c
      _ = c * (a + b) := mul_comm
      _ = c * a + c * b := mul_add
      _ = a * c +   _   := congrArg (· + _) mul_comm
      _ =   _   + b * c := congrArg _ mul_comm
  mul_inv {a : αˣ} : (a : α) * a⁻¹ = 1

end Try3

namespace Try4

structure CommMonoid {α} (op : α → α → α) (id : α) : Prop where
  assoc {a b c : α} : op (op a b) c = op a (op b c)
  comm {a b : α} : op a b = op b a
  id_op {a : α} : op id a = a

structure Ab {α} (op : α → α → α) (id : α) (inv : α → α)
extends CommMonoid op id : Prop where
  inv_op {a : α} : op (inv a) a = id

class GroupLike (α) extends Add α, Zero α, Neg α
class FieldLike (α) extends GroupLike α, Mul α, One α, Inv αˣ

structure Field (α) [skel : FieldLike α] : Prop where
  zero_ne_one : (0 : α) ≠ 1
  add : Ab skel.add 0 skel.neg
  mul : CommMonoid skel.mul 1
  mul_add {a b c : α} : a * (b + c) = a * b + a * c
  mul_inv {a : αˣ} : (a : α) * a⁻¹ = 1

-- class LinLike (α β) extends FieldLike α, GroupLike β, HMul α β β

class Lin (α β) [FieldLike α] [skel : GroupLike β] [HMul α β β] : Prop where
  scalar : Field α
  add : Ab skel.add skel.zero skel.neg
  mul_assoc {a b : α} {x : β} : a * b * x = a * (b * x)
  one_mul {x : β} : (1 : α) * x = x
  mul_add {a : α} {x y : β} : a * (x + y) = a * x + a * y
  add_mul {a b : α} {x : β} : (a + b) * x = a * x + b * x

namespace Lin
variable {F V} [FieldLike F] [GroupLike V] [HMul F V V] [Lin F V]

inductive Comb : List (F × V) → V → Prop
  | nil : Comb [] 0
  | cons {a x u s} : Comb s u → Comb ((a, x)::s) (u + a * x)

def Indep (xs : List V) : Prop :=
  ∀ as : List F, Comb (as.zip xs) 0 → ∀ a ∈ as, a = 0

end Lin

end Try4

namespace Try5

/-- https://ncatlab.org/nlab/show/category+of+monoids -/
structure CMon {α} (op : α → α → α) (id : α) : Prop where
  assoc {a b c : α} : op (op a b) c = op a (op b c)
  comm {a b : α} : op a b = op b a
  op_id {a : α} : op a id = a

namespace CMon
variable {α} {op : α → α → α} {id : α} (self : CMon op id)
variable {a : α}

theorem id_op : op id a = a := trans self.comm self.op_id

end CMon

/--
* https://ncatlab.org/nlab/show/abelian+group
* https://ncatlab.org/nlab/show/Ab
-/
class Ab (α) extends Add α, Zero α, CMon add 0, Neg α where
  add_neg {a : α} : a + -a = 0

namespace Ab
variable {α} [Ab α] {a b c : α}

instance toSub : Sub α where
  sub a b := a + -b

theorem add_assoc : a + b + c = a + (b + c) := toCMon.assoc
theorem add_comm : a + b = b + a := toCMon.comm
theorem add_zero : a + 0 = a := toCMon.op_id

theorem zero_add : 0 + a = a := trans add_comm add_zero
theorem neg_add : -a + a = 0 := trans add_comm add_neg

theorem sub_of_add (h : a + b = c) : a = c - b :=
  suffices _ from this.symm
  calc  c - b
    _ = a + b - b := congrArg (· - b) h.symm
    _ = a + (b - b) := add_assoc
    _ = a + 0 := congrArg _ add_neg
    _ = a := add_zero

theorem neg_uniq (h : a + b = 0) : a = -b := trans (sub_of_add h) zero_add
theorem uniq_neg (h : a + b = 0) : b = -a := neg_uniq (trans add_comm h)

theorem zero_uniq (h : a + b = b) : a = 0 := trans (sub_of_add h) add_neg
theorem uniq_zero (h : a + b = a) : b = 0 := zero_uniq (trans add_comm h)

theorem neg_neg_zero : -(0 : α) = 0 := (neg_uniq add_zero).symm

end Ab

/-- https://ncatlab.org/nlab/show/field#category -/
class Field (α) extends Ab α, Mul α, One α, Inv αˣ where
  zero_ne_one : (0 : α) ≠ 1
  cmon : CMon mul 1
  mul_add {a b c : α} : a * (b + c) = a * b + a * c
  mul_inv {a : αˣ} : (a : α) * a⁻¹ = 1

/-!
namespace Field
variable {α} [Field α]

instance : Coe Nat α where
  coe n := n.rec 0 fun _ a => a + 1

instance (n) : OfNat α n where
  ofNat := n

end Field
-/

/-- https://ncatlab.org/nlab/show/Vect -/
class Vect (F V) [Field F] [Ab V] extends HMul F V V where
  mul_assoc {a b : F} {x : V} : a * b * x = a * (b * x)
  one_mul {x : V} : (1 : F) * x = x
  mul_add {a : F} {x y : V} : a * (x + y) = a * x + a * y
  add_mul {a b : F} {x : V} : (a + b) * x = a * x + b * x

/-!
namespace Vect
variable {V} [Ab V]

inductive Comb {F} [Field F] [Vect F V] : List (F × V) → V → Prop
  | nil : Comb [] 0
  | cons {a x u s} : Comb s u → Comb ((a, x)::s) (u + a * x)

def IsIndep (F) [Field F] [Vect F V] (xs : List V) : Prop :=
  ∀ as : List F, Comb (as.zip xs) 0 → ∀ a ∈ as, a = 0

def IsSpan (F) [Field F] [Vect F V] (xs : List V) : Prop :=
  ∀ x : V, ∃ as : List F, Comb (as.zip xs) x

-- structure IsBasis (F) [Field F] [Vect F V] (xs : List V) : Prop where
--   indep : ∀ as : List F, Comb (as.zip xs) 0 → ∀ a ∈ as, a = 0
--   span : ∀ x : V, ∃ as : List F, Comb (as.zip xs) x

def IsBasis (F) [Field F] [Vect F V] (xs : List V) : Prop :=
  IsIndep F xs ∧ IsSpan F xs

theorem dim (F) [Field F] [Vect F V] {xs ys : List V}
  : IsBasis F xs → IsBasis F ys → xs.length = ys.length :=
  sorry

end Vect
-/

namespace Vect
variable {F V} [Field F] [Ab V] [Vect F V]

theorem zero_mul {x : V} : (0 : F) * x = 0 :=
  let z := (0 : F) * x
  suffices z + z = z from Ab.zero_uniq this
  calc  z + z
    _ = (0 + 0 : F) * x := add_mul.symm
    _ = z := congrArg (· * x) Ab.add_zero

theorem neg_mul {a : F} {x : V} : -a * x = -(a * x) :=
  suffices a * x + -a * x = 0 from Ab.uniq_neg this
  calc
    _ = (a - a) * x := add_mul.symm
    _ = 0 * x := congrArg (· * x) Ab.add_neg
    _ = 0 := zero_mul

end Vect

namespace Vect
variable (F) {V} [Field F] [Ab V] [Vect F V]

def Span (x : V) := {y : V // ∃ a : F, a * x = y}
namespace Span

instance ab (x : V) : Ab (Span F x) where
  zero := ⟨0, 0, zero_mul⟩
  neg u := suffices _ from ⟨-u.val, this⟩
    have ⟨u, a, (hu : a * x = u)⟩ := u
    suffices -a * x = -u from ⟨-a, this⟩
    hu ▸ neg_mul
  add u v := suffices _ from ⟨u.val + v.val, this⟩
    have ⟨u, a, (hu : a * x = u)⟩ := u
    have ⟨v, b, (hv : b * x = v)⟩ := v
    suffices (a + b) * x = u + v from ⟨a + b, this⟩
    hu ▸ hv ▸ add_mul
  assoc   := Subtype.eq Ab.add_assoc
  comm    := Subtype.eq Ab.add_comm
  op_id   := Subtype.eq Ab.add_zero
  add_neg := Subtype.eq Ab.add_neg

instance span (x : V) : Vect F (Span F x) where
  hMul a u := suffices _ from ⟨a * u.val, this⟩
    have ⟨u, b, (hu : b * x = u)⟩ := u
    suffices a * b * x = a * u from ⟨a * b, this⟩
    hu ▸ mul_assoc
  mul_assoc := Subtype.eq mul_assoc
  one_mul   := Subtype.eq one_mul
  mul_add   := Subtype.eq mul_add
  add_mul   := Subtype.eq add_mul

end Span

end Vect

end Try5

/-
* https://leanprover-community.github.io/mathlib4_docs/Batteries/Data/List/Basic.html#List.Perm
* https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html#Finset
* https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Nodup.html
* https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.Nodup
* https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Nodup.html
* https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.Pairwise
* https://ncatlab.org/nlab/show/determinant
* https://math.stackexchange.com/a/3639158
-/

inductive List.Perm {α} : List α → List α → Prop
  | nil : Perm [] []
  | cons {x as bs} : Perm as bs → Perm %[x|as] %[x|bs]
  | swap {x y as} : Perm %[x,y|as] %[y,x|as]
  | trans {as bs cs} : Perm as bs → Perm bs cs → Perm as cs

def List.Perm.setoid {α} : Setoid (List α) where
  r := Perm
  iseqv.refl as := as.rec nil fun _ _ => cons
  iseqv.symm h := h.rec nil (fun _ => cons) swap fun _ _ => flip trans
  iseqv.trans := trans

def Multiset (α) := Quotient (@List.Perm.setoid α)

inductive List.Pairwise {α} (p : α → α → Prop) : List α → Prop
  | nil : Pairwise p []
  | cons {x as} : (∀ a ∈ as, p x a) → Pairwise p as → Pairwise p %[x|as]

def List.Nodup {α} (as : List α) : Prop := as.Pairwise (· ≠ ·)

inductive List.Uniq {α} : List α → List α → Prop
  | ofPerm {as bs} : Perm as bs → Uniq as bs
  | dup {x as} : Uniq %[x|as] %[x,x|as]
  | dedup {x as} : Uniq %[x,x|as] %[x|as]

theorem List.Perm.sameLength {α} {as bs : List α} (h : Perm as bs) : as.length = bs.length :=
  h.rec rfl (fun _ => congrArg Nat.succ) (congrArg (Nat.succ ∘ .succ) rfl) fun _ _ => .trans

theorem List.Uniq.rfl {α} {as : List α} : Uniq as as := ofPerm (Perm.setoid.refl as)
theorem List.Uniq.trans {α} {as bs cs : List α} : Uniq as bs → Uniq bs cs → Uniq as cs
  | ofPerm h, ofPerm h' => ofPerm (Perm.trans h h')
  | ofPerm h, dup => sorry
  | dup, dedup => .rfl
  | dedup, dup => .rfl
  | _, _ => sorry

def List.Uniq.setoid (α) : Setoid (List α) where
  r := Uniq
  iseqv.refl as := ofPerm (Perm.setoid.refl as)
  iseqv.symm h := h.rec (ofPerm ∘ Perm.setoid.symm) dedup dup
  iseqv.trans
    | ofPerm h, ofPerm h' => ofPerm (Perm.trans h h')
    | _, _ => sorry
