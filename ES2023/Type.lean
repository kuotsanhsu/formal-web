namespace ES2023

/-
[6.2.4 The Completion Record Specification Type](https://262.ecma-international.org/14.0/#sec-completion-record-specification-type)
-/

/-
inductive CompletionType
  | normal
  | break
  | continue
  | return
  | throw

structure Completion (type : CompletionType) (Value) where
  value : Value
  target : Option String --:= default

abbrev NormalCompletion := Completion .normal
abbrev BreakCompletion := Completion .break
abbrev ContinueCompletion := Completion .continue
abbrev ReturnCompletion := Completion .return
abbrev ThrowCompletion := Completion .throw
abbrev AbruptCompletion {type : CompletionType} (h : type ≠ .normal) := Completion type
-/

inductive ThrowCompletion (Value : Type u)
  | normal (value : Value)
  | throw

/-
[6.1 ECMAScript Language Types](https://262.ecma-international.org/14.0/#sec-ecmascript-language-types)
-/

inductive Undefined
  | undefined
open Undefined (undefined)

inductive Null
  | null
open Null (null)

inductive Symbol

inductive Number

inductive BigInt

axiom Number.unaryMinus : Number → Number
axiom BigInt.unaryMinus : BigInt → BigInt
axiom Number.bitwiseNot : Number → Number
axiom BigInt.bitwiseNot : BigInt → BigInt
axiom Number.exponentiate : Number → Number → Number
axiom BigInt.exponentiate : BigInt → Number → ThrowCompletion BigInt
axiom Number.multiply : Number → Number → Number
axiom BigInt.multiply : BigInt → Number → BigInt
axiom Number.divide : Number → Number → Number
axiom BigInt.divide : BigInt → Number → ThrowCompletion BigInt
axiom Number.remainder : Number → Number → Number
axiom BigInt.remainder : BigInt → Number → ThrowCompletion BigInt
axiom Number.add : Number → Number → Number
axiom BigInt.add : BigInt → Number → BigInt
axiom Number.subtract : Number → Number → Number
axiom BigInt.subtract : BigInt → Number → BigInt
axiom Number.leftShift : Number → Number → Number
axiom BigInt.leftShift : BigInt → Number → BigInt
axiom Number.signedRightShift : Number → Number → Number
axiom BigInt.signedRightShift : BigInt → Number → BigInt
axiom Number.unsignedRightShift : Number → Number → Number
-- axiom BigInt.unsignedRightShift : BigInt → Number → BigInt -- Always throws
axiom Number.lessThan : Number → Number → Bool -- `Undefined` as well
axiom BigInt.lessThan : BigInt → Number → Bool
axiom Number.equal : Number → Number → Bool
axiom BigInt.equal : BigInt → Number → Bool
axiom Number.sameValue : Number → Number → Bool
axiom Number.sameValueZero : Number → Number → Bool
axiom Number.bitwiseAND : Number → Number → Number
axiom BigInt.bitwiseAND : BigInt → BigInt → BigInt
axiom Number.bitwiseXOR : Number → Number → Number
axiom BigInt.bitwiseXOR : BigInt → BigInt → BigInt
axiom Number.bitwiseOR : Number → Number → Number
axiom BigInt.bitwiseOR : BigInt → BigInt → BigInt
axiom Number.toString : Number → String
axiom BigInt.toString : BigInt → String

/-
[6.1.7.4 Well-Known Intrinsic Objects](https://262.ecma-international.org/14.0/#sec-well-known-intrinsic-objects)
-/

/-
[11.1 Source Text](https://262.ecma-international.org/14.0/#sec-source-text)
-/
#check String.fromUTF8

end ES2023
