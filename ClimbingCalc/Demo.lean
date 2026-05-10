import ClimbingCalc.Object
import ClimbingCalc.Schemas
import ClimbingCalc.Climb

namespace ClimbingCalc

/-! ## The climb, scene by scene

This file walks the climb from level 0 (only `structural` admitted, no
operators) through level 2 (`lex2` admitted, Ackermann admissible). Each
theory is a value, each operator is built with Lean's recursion machinery
under an admitted schema. -/

/-! ### Scene 1 — Level 0: nothing admitted -/

/-- Bare theory: no schemas, no operators. -/
def T_bare : Theory := Theory.empty

/-! ### Scene 2 — Install the structural schema -/

/-- Level 0 (the conventional starting point of the keynote demo):
`structural` admitted, no operators yet. -/
def T₀ : Theory := T_bare.installSchema structuralSchema

/-! ### Scene 3 — Climb under structural: add, mul, exp

Each operator is defined by Lean primitive recursion on its first
argument; Lean's type checker accepts these directly. The `schema`
field declares that they were admitted under `structural`. -/

private def addImpl : Nat → Nat → Nat
  | 0,     m => m
  | n + 1, m => (addImpl n m) + 1

private def mulImpl : Nat → Nat → Nat
  | 0,     _ => 0
  | n + 1, m => addImpl m (mulImpl n m)

private def expImpl : Nat → Nat → Nat
  | _, 0     => 1
  | b, e + 1 => mulImpl b (expImpl b e)

def addOp : Operator where
  name   := "add"
  arity  := 2
  schema := "structural"
  fn args := match args with
    | [n, m] => addImpl n m
    | _      => 0

def mulOp : Operator where
  name   := "mul"
  arity  := 2
  schema := "structural"
  fn args := match args with
    | [n, m] => mulImpl n m
    | _      => 0

def expOp : Operator where
  name   := "exp"
  arity  := 2
  schema := "structural"
  fn args := match args with
    | [b, e] => expImpl b e
    | _      => 0

/-- Theory after structural-schema climb: PR operators admitted. -/
def T₁ : Theory := T₀.installOps [addOp, mulOp, expOp]

/-! ### Scene 4 — Install the lex2 schema

Ackermann's recursion can't be expressed under `structural` alone: the
third clause `A(n+1, m+1) = A(n, A(n+1, m))` has a recursive call with
the *same* first argument. To admit it, we need lexicographic order. -/

/-- Level 2: structural + lex2, but no new operators yet. -/
def T₂ : Theory := T₁.installSchema lex2Schema

/-! ### Scene 5 — Climb under lex2: Ackermann

Lean's elaborator infers the default lex termination measure on
positional arguments, which matches `lex2`'s relation. The function is
total; Lean type-checks it. -/

private def ackImpl : Nat → Nat → Nat
  | 0,     m     => m + 1
  | n + 1, 0     => ackImpl n 1
  | n + 1, m + 1 => ackImpl n (ackImpl (n + 1) m)

def ackermannOp : Operator where
  name   := "ackermann"
  arity  := 2
  schema := "lex2"
  fn args := match args with
    | [n, m] => ackImpl n m
    | _      => 0

/-- Climbed theory: structural + lex2; add, mul, exp, ackermann. -/
def T_climbed : Theory := T₂.installOp ackermannOp

/-! ### Scene 6 — Compute -/

example : T_climbed.apply "add" [2, 3] = some 5         := by native_decide
example : T_climbed.apply "mul" [3, 4] = some 12        := by native_decide
example : T_climbed.apply "exp" [2, 5] = some 32        := by native_decide
example : T_climbed.apply "ackermann" [0, 5] = some 6   := by native_decide
example : T_climbed.apply "ackermann" [1, 5] = some 7   := by native_decide
example : T_climbed.apply "ackermann" [2, 2] = some 7   := by native_decide
example : T_climbed.apply "ackermann" [3, 3] = some 61  := by native_decide

/-! ### Scene 7 — Refusal: bad arity gets rejected -/

example : T_climbed.apply "ackermann" [1] = none        := by native_decide
example : T_climbed.apply "nonexistent" [0] = none      := by native_decide

end ClimbingCalc
