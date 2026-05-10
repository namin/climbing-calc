import ClimbingCalc.Object
import ClimbingCalc.Schemas
import ClimbingCalc.Climb

namespace ClimbingCalc

/-! ## The climb, scene by scene

This file walks the climb from level 0 (only `structural` admitted, no
operators) through level 2 (`structural` + `lex2`), with operators
admitted at each rung. Each operator's `step` function uses its
schema's relation in the type signature; Lean's type checker rejects
mismatched recursion at admission time. -/

/-! ### Scene 1 — Level 0: nothing admitted -/

def T_bare : Theory := Theory.empty

/-! ### Scene 2 — Install the structural schema -/

def T₀ : Theory := T_bare.installSchema structuralSchema ⟨by decide⟩

/-! ### Scene 3 — Operators admitted under `structural`

Each step function's type carries `structuralSchema.rel y x` as the
recursion-handle constraint. Recursive calls supply accessibility
witnesses built from `structuralSchema.dec_first`. -/

def predStep : (x : List Nat) → ((y : List Nat) → structuralSchema.rel y x → Nat) → Nat
  | [0],   _ => 0
  | [n+1], _ => n
  | _,     _ => 0

def doubleStep : (x : List Nat) → ((y : List Nat) → structuralSchema.rel y x → Nat) → Nat
  | [n], _ => 2 * n
  | _,   _ => 0

def addStep : (x : List Nat) → ((y : List Nat) → structuralSchema.rel y x → Nat) → Nat
  | [0, m],   _   => m
  | [n+1, m], rec =>
    rec [n, m] (structuralSchema.dec_first [m] [m] (by omega)) + 1
  | _,        _   => 0

def mulStep : (x : List Nat) → ((y : List Nat) → structuralSchema.rel y x → Nat) → Nat
  | [0, _],   _   => 0
  | [n+1, m], rec =>
    m + rec [n, m] (structuralSchema.dec_first [m] [m] (by omega))
  | _,        _   => 0

def factStep : (x : List Nat) → ((y : List Nat) → structuralSchema.rel y x → Nat) → Nat
  | [0],   _   => 1
  | [n+1], rec =>
    (n + 1) * rec [n] (structuralSchema.dec_first [] [] (by omega))
  | _,     _   => 0

def fibStep : (x : List Nat) → ((y : List Nat) → structuralSchema.rel y x → Nat) → Nat
  | [0],   _   => 0
  | [1],   _   => 1
  | [n+2], rec =>
    rec [n+1] (structuralSchema.dec_first [] [] (by omega)) +
    rec [n]   (structuralSchema.dec_first [] [] (by omega))
  | _,     _   => 0

def predOp     : AdmittedOperator := ⟨structuralSchema,
  { name := "pred",   arity := 1, step := predStep }⟩
def doubleOp   : AdmittedOperator := ⟨structuralSchema,
  { name := "double", arity := 1, step := doubleStep }⟩
def addOp      : AdmittedOperator := ⟨structuralSchema,
  { name := "add",    arity := 2, step := addStep }⟩
def mulOp      : AdmittedOperator := ⟨structuralSchema,
  { name := "mul",    arity := 2, step := mulStep }⟩
def factOp     : AdmittedOperator := ⟨structuralSchema,
  { name := "fact",   arity := 1, step := factStep }⟩
def fibOp      : AdmittedOperator := ⟨structuralSchema,
  { name := "fib",    arity := 1, step := fibStep }⟩

/-- The climb under `structural`: install operators one at a time.
`schema_present` is `.head _` because each install leaves
`T.schemas` with `structuralSchema` at the head. -/
def T_pred   : Theory := T₀.installOp       predOp   ⟨.head _, by decide⟩
def T_double : Theory := T_pred.installOp   doubleOp ⟨.head _, by decide⟩
def T_add    : Theory := T_double.installOp addOp    ⟨.head _, by decide⟩
def T_mul    : Theory := T_add.installOp    mulOp    ⟨.head _, by decide⟩
def T_fact   : Theory := T_mul.installOp    factOp   ⟨.head _, by decide⟩
def T_fib    : Theory := T_fact.installOp   fibOp    ⟨.head _, by decide⟩
abbrev T₁ : Theory := T_fib

/-! ### Scene 4 — Install the lex2 schema

Ackermann's and Sudan's recursions have a recursive call with the
*same* first argument; no single coordinate decreases. Lex order on
the first two arguments is the new well-foundedness we need. -/

def T₂ : Theory := T₁.installSchema lex2Schema ⟨by decide⟩

/-! ### Scene 5 — Operators admitted under `lex2`

The step function types now mention `lex2Schema.rel`. Recursive
accessibility witnesses come from `lex2Schema.dec_left` (first arg
strictly decreases) and `lex2Schema.dec_right` (first arg equal,
second strictly decreases). -/

def ackStep : (x : List Nat) → ((y : List Nat) → lex2Schema.rel y x → Nat) → Nat
  | [0, m],     _   => m + 1
  | [n+1, 0],   rec =>
    rec [n, 1] (lex2Schema.dec_left [] [] (by omega))
  | [n+1, m+1], rec =>
    let inner := rec [n+1, m] (lex2Schema.dec_right [] [] (by omega))
    rec [n, inner] (lex2Schema.dec_left [] [] (by omega))
  | _,          _   => 0

/-- Sudan's function. Args are presented as `[n, y, x]` so that the
lex2 measure on the first two list elements aligns with the
mathematical measure on `(n, y)`. The trailing `x` is the static
parameter. Mathematically: `F_n(x, y)`. -/
def sudanStep : (x : List Nat) → ((y : List Nat) → lex2Schema.rel y x → Nat) → Nat
  | [0,   y,   x], _   => x + y
  | [_+1, 0,   x], _   => x
  | [n+1, y+1, x], rec =>
    let v := rec [n+1, y, x] (lex2Schema.dec_right [x] [x] (by omega))
    rec [n, v + y + 1, v] (lex2Schema.dec_left [v] [x] (by omega))
  | _,             _   => 0

def ackermannOp : AdmittedOperator := ⟨lex2Schema,
  { name := "ackermann", arity := 2, step := ackStep }⟩
def sudanOp     : AdmittedOperator := ⟨lex2Schema,
  { name := "sudan",     arity := 3, step := sudanStep }⟩

def T_ack   : Theory := T₂.installOp    ackermannOp ⟨.head _, by decide⟩
def T_sudan : Theory := T_ack.installOp sudanOp     ⟨.head _, by decide⟩
abbrev T_climbed : Theory := T_sudan

/-! ### Scene 6 — Compute -/

example : T_climbed.apply "pred" [7] = some 6                 := by native_decide
example : T_climbed.apply "double" [7] = some 14              := by native_decide
example : T_climbed.apply "add" [2, 3] = some 5               := by native_decide
example : T_climbed.apply "mul" [3, 4] = some 12              := by native_decide
example : T_climbed.apply "fact" [5] = some 120               := by native_decide
example : T_climbed.apply "fib" [10] = some 55                := by native_decide
example : T_climbed.apply "ackermann" [0, 5] = some 6         := by native_decide
example : T_climbed.apply "ackermann" [1, 5] = some 7         := by native_decide
example : T_climbed.apply "ackermann" [2, 2] = some 7         := by native_decide
example : T_climbed.apply "ackermann" [3, 3] = some 61        := by native_decide
example : T_climbed.apply "sudan" [0, 5, 3] = some 8          := by native_decide
example : T_climbed.apply "sudan" [1, 1, 1] = some 3          := by native_decide
example : T_climbed.apply "sudan" [1, 2, 1] = some 8          := by native_decide

/-! ### Scene 7 — Refusal: bad arity / unknown -/

example : T_climbed.apply "ackermann" [1] = none              := by native_decide
example : T_climbed.apply "sudan" [1, 1] = none               := by native_decide
example : T_climbed.apply "nonexistent" [0] = none            := by native_decide

/-! ### Scene 5b — refusal witnesses (commented)

Each of the following would compile under v1's gate (which only
checked schema-name presence and operator-name freshness). v2's gate
rejects them at the type level:

```lean
-- (1) Operator declares structuralSchema but its step references
--     lex2Schema's relation. The type doesn't unify; doesn't compile.
def mislabeled : AdmittedOperator := ⟨structuralSchema,
  { name := "mislabeled", arity := 2, step := ackStep }⟩
-- type error: ackStep expects lex2Schema.rel, structuralSchema's
-- rel is different
```

```lean
-- (2) Step function whose recursive call doesn't actually decrease.
def badAck : (x : List Nat) → ((y : List Nat) → structuralSchema.rel y x → Nat) → Nat
  | [n+1, m+1], rec =>
    rec [n+1, m] (structuralSchema.dec_first ...)
    -- type error: can't prove first arg decreases (both are n+1)
  | _, _ => 0
```

The kernel refuses these at admission because the step's type *is*
the decrease constraint. There is no separate certificate that could
be wrong; the type system is the gate. -/

/-! ### Per-rung well-formedness -/

theorem T₀_wellFormed       : T₀.WellFormed       :=
  installSchema_wellFormed empty_wellFormed       ⟨by decide⟩
theorem T_pred_wellFormed   : T_pred.WellFormed   :=
  installOp_wellFormed     T₀_wellFormed          ⟨.head _, by decide⟩
theorem T_double_wellFormed : T_double.WellFormed :=
  installOp_wellFormed     T_pred_wellFormed      ⟨.head _, by decide⟩
theorem T_add_wellFormed    : T_add.WellFormed    :=
  installOp_wellFormed     T_double_wellFormed    ⟨.head _, by decide⟩
theorem T_mul_wellFormed    : T_mul.WellFormed    :=
  installOp_wellFormed     T_add_wellFormed       ⟨.head _, by decide⟩
theorem T_fact_wellFormed   : T_fact.WellFormed   :=
  installOp_wellFormed     T_mul_wellFormed       ⟨.head _, by decide⟩
theorem T_fib_wellFormed    : T_fib.WellFormed    :=
  installOp_wellFormed     T_fact_wellFormed      ⟨.head _, by decide⟩
theorem T₁_wellFormed       : T₁.WellFormed       := T_fib_wellFormed
theorem T₂_wellFormed       : T₂.WellFormed       :=
  installSchema_wellFormed T₁_wellFormed          ⟨by decide⟩
theorem T_ack_wellFormed    : T_ack.WellFormed    :=
  installOp_wellFormed     T₂_wellFormed          ⟨.head _, by decide⟩
theorem T_sudan_wellFormed  : T_sudan.WellFormed  :=
  installOp_wellFormed     T_ack_wellFormed       ⟨.head _, by decide⟩
theorem T_climbed_wellFormed : T_climbed.WellFormed := T_sudan_wellFormed

end ClimbingCalc
