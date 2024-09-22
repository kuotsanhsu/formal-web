inductive List.Perm {α} : List α → List α → Prop
  | refl as : Perm as as
  | swap {x y} {as bs cs} : Perm (as++x::bs++y::cs) (as++y::bs++x::cs)
  | trans {as bs cs} : Perm as bs → Perm bs cs → Perm as cs

theorem List.Perm.symm {α} {as bs : List α} : Perm as bs → Perm bs as
  | refl _ => refl _
  | trans h h' => trans h'.symm h.symm
  | swap => swap
