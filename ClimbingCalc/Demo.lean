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

/-! ### Scene 2 — Install the structural schema

Each `installSchema` call requires a `SchemaAdmissible` proof witnessing
name freshness. We supply it with `by decide`; the build fails if any
admission precondition is violated. -/

/-- Level 0 (the conventional starting point of the keynote demo):
`structural` admitted, no operators yet. -/
def T₀ : Theory := T_bare.installSchema structuralSchema ⟨by decide⟩

/-! ### Scene 3 — Climb under structural: add, mul, exp

Each operator is defined by Lean primitive recursion on its first
argument; Lean's type checker accepts these directly. The `schema`
field declares that they were admitted under `structural`. -/

/-
The implementations below use Lean's builtin `Nat` operations for
runtime efficiency. The *specification* of each operator is still
primitive-recursive — Lean's `Nat.add` is itself defined by recursion
on one argument — so admission under `structural` is unchanged. We
just don't pay for naive linear-time addition at runtime, which would
make `fact 10` stack-overflow when added through `mulImpl 10 _`.

The naive PR definitions (for reference; what the climb's pedagogy
claims is admissible):

    addImpl 0     m = m
    addImpl (n+1) m = succ (addImpl n m)

    mulImpl 0     _ = 0
    mulImpl (n+1) m = addImpl m (mulImpl n m)

    expImpl _ 0     = 1
    expImpl b (e+1) = mulImpl b (expImpl b e)

Each of these compiles to runtime that's quadratic-or-worse on Lean's
unary `Nat`; we use the compiled `Nat.add`, `Nat.mul`, `Nat.pow`
instead.
-/

private def addImpl (n m : Nat) : Nat := n + m
private def mulImpl (n m : Nat) : Nat := n * m
private def expImpl (b e : Nat) : Nat := b ^ e

private def factImpl : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factImpl n

private def fibImpl : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibImpl (n + 1) + fibImpl n

private def doubleImpl (n : Nat) : Nat := 2 * n

private def predImpl : Nat → Nat
  | 0     => 0
  | n + 1 => n

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

def factOp : Operator where
  name   := "fact"
  arity  := 1
  schema := "structural"
  fn args := match args with
    | [n] => factImpl n
    | _   => 0

def fibOp : Operator where
  name   := "fib"
  arity  := 1
  schema := "structural"
  fn args := match args with
    | [n] => fibImpl n
    | _   => 0

def doubleOp : Operator where
  name   := "double"
  arity  := 1
  schema := "structural"
  fn args := match args with
    | [n] => doubleImpl n
    | _   => 0

def predOp : Operator where
  name   := "pred"
  arity  := 1
  schema := "structural"
  fn args := match args with
    | [n] => predImpl n
    | _   => 0

/-- Theory after structural-schema climb: PR operators admitted, one
per `installOp` call with an `OperatorAdmissible` proof. Each `by
decide` checks: declared schema is in the theory, name is fresh. -/
def T_pred   : Theory := T₀.installOp       predOp   ⟨by decide, by decide⟩
def T_double : Theory := T_pred.installOp   doubleOp ⟨by decide, by decide⟩
def T_add    : Theory := T_double.installOp addOp    ⟨by decide, by decide⟩
def T_mul    : Theory := T_add.installOp    mulOp    ⟨by decide, by decide⟩
def T_exp    : Theory := T_mul.installOp    expOp    ⟨by decide, by decide⟩
def T_fact   : Theory := T_exp.installOp    factOp   ⟨by decide, by decide⟩
def T_fib    : Theory := T_fact.installOp   fibOp    ⟨by decide, by decide⟩
abbrev T₁ : Theory := T_fib

/-! ### Scene 4 — Install the lex2 schema

Ackermann's recursion can't be expressed under `structural` alone: the
third clause `A(n+1, m+1) = A(n, A(n+1, m))` has a recursive call with
the *same* first argument. To admit it, we need lexicographic order. -/

/-- Level 2: structural + lex2, but no new operators yet. -/
def T₂ : Theory := T₁.installSchema lex2Schema ⟨by decide⟩

/-! ### Scene 5 — Climb under lex2: Ackermann

Lean's elaborator infers the default lex termination measure on
positional arguments, which matches `lex2`'s relation. The function is
total; Lean type-checks it. -/

private def ackImpl : Nat → Nat → Nat
  | 0,     m     => m + 1
  | n + 1, 0     => ackImpl n 1
  | n + 1, m + 1 => ackImpl n (ackImpl (n + 1) m)

/--
**Sudan's function** — the *other* canonical non-PR function. Like
Ackermann, it's defined by simultaneous double recursion on two
arguments:

    F_0(x, y)     = x + y
    F_{n+1}(x, 0) = x
    F_{n+1}(x, y+1) = F_n(F_{n+1}(x, y), F_{n+1}(x, y) + y + 1)

Termination is lexicographic on `(n, y)`: at `(n+1, y+1)`, one
recursive call drops to `(n+1, y)` (second decreases) and the other to
`(n, _)` (first decreases). The parameter `x` is irrelevant to the
measure but participates in computation. Like Ackermann, Sudan's
function isn't admissible under `structural` alone; with `lex2`
installed, Lean's elaborator accepts the definition.
-/
private def sudanImpl : Nat → Nat → Nat → Nat   -- args ordered (n, y, x) for lex measure
  | 0,     y,     x => x + y
  | _ + 1, 0,     x => x
  | n + 1, y + 1, x =>
    let v := sudanImpl (n + 1) y x
    sudanImpl n (v + y + 1) v

def ackermannOp : Operator where
  name   := "ackermann"
  arity  := 2
  schema := "lex2"
  fn args := match args with
    | [n, m] => ackImpl n m
    | _      => 0

def sudanOp : Operator where
  name   := "sudan"
  arity  := 3
  schema := "lex2"
  fn args := match args with
    | [n, x, y] => sudanImpl n y x   -- present as F_n(x, y), measure on (n, y)
    | _         => 0

/-- Climbed theory: structural + lex2; PR operators + ackermann + sudan. -/
def T_ack   : Theory := T₂.installOp    ackermannOp ⟨by decide, by decide⟩
def T_sudan : Theory := T_ack.installOp sudanOp     ⟨by decide, by decide⟩
abbrev T_climbed : Theory := T_sudan

/-! ### `T_climbed` is well-formed

Every intermediate theory in the climb is well-formed because each
admission step preserves the invariant. The chain of
`installSchema_wellFormed` and `installOp_wellFormed` applications
discharges it without any computation. -/

theorem T_climbed_wellFormed : T_climbed.WellFormed :=
  installOp_wellFormed
    (installOp_wellFormed
      (installSchema_wellFormed
        (installOp_wellFormed
          (installOp_wellFormed
            (installOp_wellFormed
              (installOp_wellFormed
                (installOp_wellFormed
                  (installOp_wellFormed
                    (installOp_wellFormed
                      (installSchema_wellFormed empty_wellFormed _) _) _) _) _) _) _) _) _) _) _

/-! ### Scene 5b — the refusal witness

The following definition is *exactly the shape* of Ackermann's
recursion, but if you ask Lean to accept it under the single-argument
structural measure (default for a `Nat → Nat → Nat` function), the
elaborator refuses. Uncomment to verify; the build will fail with
something like `fail to show termination`.

```lean
def badAckImpl : Nat → Nat → Nat
  | 0,     m     => m + 1
  | n + 1, 0     => badAckImpl n 1
  | n + 1, m + 1 => badAckImpl n (badAckImpl (n + 1) m)
termination_by n _ => n   -- structural on first arg — Lean refuses
```

The recursive call `badAckImpl (n + 1) m` has the *same* first
argument, so a structural measure on `n` alone doesn't decrease.
Installing `lex2` (which `ackImpl` and `sudanImpl` use implicitly via
Lean's default lex measure) is what closes the gap. -/

/-! ### Scene 5c — admission-gate refusals

Each of the following would fit the shape of an admissible declaration
*on its face*, but the admissibility precondition refuses it. Uncomment
any one to verify; the build fails with a `decide` failure on the
relevant `OperatorAdmissible` field.

```lean
-- (1) Operator referencing a schema that hasn't been installed:
def bogusSchemaRef : Operator where
  name := "weird"; arity := 1; schema := "made-up"
  fn := fun _ => 0
def T_bogus1 : Theory :=
  T_climbed.installOp bogusSchemaRef ⟨by decide, by decide⟩
-- decide fails: T_climbed.hasSchema "made-up" = false ≠ true

-- (2) Operator shadowing an existing name:
def shadowAck : Operator where
  name := "ackermann"; arity := 2; schema := "lex2"
  fn := fun _ => 0
def T_bogus2 : Theory :=
  T_climbed.installOp shadowAck ⟨by decide, by decide⟩
-- decide fails: T_climbed.hasOperator "ackermann" = true ≠ false

-- (3) Schema with a name that's already taken (a valid duplicate —
-- same name, same well-foundedness proof, freshness is the only
-- failing condition):
def dupSchema : Schema where
  name    := "structural"
  Carrier := Nat
  rel     := (· < ·)
  wf      := Nat.lt_wfRel.wf
def T_bogus3 : Theory :=
  T_climbed.installSchema dupSchema ⟨by decide⟩
-- decide fails: T_climbed.hasSchema "structural" = true ≠ false
```
-/

/-! ### Scene 6 — Compute -/

example : T_climbed.apply "pred" [7] = some 6           := by native_decide
example : T_climbed.apply "double" [7] = some 14        := by native_decide
example : T_climbed.apply "add" [2, 3] = some 5         := by native_decide
example : T_climbed.apply "mul" [3, 4] = some 12        := by native_decide
example : T_climbed.apply "exp" [2, 5] = some 32        := by native_decide
example : T_climbed.apply "fact" [5] = some 120         := by native_decide
example : T_climbed.apply "fib" [10] = some 55          := by native_decide
example : T_climbed.apply "ackermann" [0, 5] = some 6   := by native_decide
example : T_climbed.apply "ackermann" [1, 5] = some 7   := by native_decide
example : T_climbed.apply "ackermann" [2, 2] = some 7   := by native_decide
example : T_climbed.apply "ackermann" [3, 3] = some 61  := by native_decide
example : T_climbed.apply "sudan" [0, 5, 3] = some 8    := by native_decide
example : T_climbed.apply "sudan" [1, 1, 1] = some 3    := by native_decide
example : T_climbed.apply "sudan" [1, 1, 2] = some 8    := by native_decide

/-! ### Scene 7 — Refusal: bad arity gets rejected -/

example : T_climbed.apply "ackermann" [1] = none        := by native_decide
example : T_climbed.apply "sudan" [1, 1] = none         := by native_decide
example : T_climbed.apply "nonexistent" [0] = none      := by native_decide

end ClimbingCalc
