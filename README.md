# climbing-calc

A calculator whose class of admissible total functions grows under
**type-level proof-bearing admission**. Each climb admits either:

1. a **schema** — a well-founded relation on `List Nat` with a Lean
   `WellFounded` proof; or
2. an **operator** — typed against an admitted schema, carrying a
   `step` function whose signature literally mentions the schema's
   relation as the recursion-handle constraint.

You cannot construct an `Operator S` whose recursion doesn't go
through `S.rel` — the type checker won't let you. The kernel's
admission gate is *Lean's type checker*; there is no separate
termination certificate that could drift from the schema.

Climber re-rendered with computation as the substrate. Same kernel
discipline (LCF-style admission of typed certificates), different
substrate (total `List Nat → Nat` functions instead of formal
derivations).

See [`DESIGN.md`](DESIGN.md) for the design rationale and
[`AvsB.md`](AvsB.md) for the v2-A-vs-B decision record.

## Status

Builds clean on `leanprover/lean4:v4.29.1`. Zero `sorry`s. The smoke
executable walks the climb scene by scene.

```bash
$ lake build
Build completed successfully (8 jobs).

$ lake exe smoke
================================================================
climbing-calc v2 — the calculator that climbs
================================================================

Scene 1: T_bare — empty theory
  schemas: []
  operators: []

Scene 2: T₀ — install structural schema
  schemas: [structural]
  operators: []

Scene 3: T₁ — admit PR operators under structural
  operators: [fib, fact, mul, add, double, pred]
  pred([7]): (some 6)
  double([7]): (some 14)
  add([2, 3]): (some 5)
  mul([3, 4]): (some 12)
  fact([5]): (some 120)
  fib([10]): (some 55)

Scene 4: T₂ — install lex2 schema
  schemas: [lex2, structural]

Scene 5: T_climbed — admit ackermann and sudan under lex2
  operators: [sudan, ackermann, fib, fact, mul, add, double, pred]
  ackermann([0, 5]): (some 6)
  ackermann([1, 5]): (some 7)
  ackermann([2, 2]): (some 7)
  ackermann([3, 3]): (some 61)

  sudan([0, 5, 3]): (some 8)
  sudan([1, 1, 1]): (some 3)
  sudan([1, 2, 1]): (some 8)

Scene 6: refusal — wrong arity / unknown operator
  ackermann([1]): none
  sudan([1, 1]): none
  nonexistent([0]): none

Scene 7: the line crossed
  ackermann([3, 8]): (some 2045)
  fact([10]): (some 3628800)
```

## The pattern

| Role | Instance |
|---|---|
| Substrate | Theory `T = (schemas, operators)`; operators are `WellFounded.fix step` over their schema's WF proof |
| Proposer | Human or LLM offering a schema (with WF proof) or an operator (with a step function typed against a declared schema) |
| Gate | Lean's type checker: `Schema` requires `WellFounded`; `Operator S` requires a step function with `S.rel` in its type. Plus admission preconditions (schema present, names fresh). |

The operator carries:

```lean
structure Operator (S : Schema) where
  name  : String
  arity : Nat
  step  : (x : List Nat) → ((y : List Nat) → S.rel y x → Nat) → Nat
```

`step` takes the current argument list `x` and a recursion handle
`rec` that demands an accessibility witness in `S.rel`. The
operator's runtime function is `S.wf.fix step`. Lean's elaborator
accepts an `Operator S` value iff every recursive call site supplies
a valid `S.rel`-witness.

**There is no separate termination certificate.** The step's *type*
is the certificate. A mislabeled operator (e.g. trying to use lex2
recursion under structural) fails type-checking, not a downstream
proof.

## The climb

| Theory | Schemas admitted | Operators admitted |
|---|---|---|
| `T_bare`    | —                | —                                              |
| `T₀`        | structural       | —                                              |
| `T₁`        | structural       | pred, double, add, mul, fact, fib              |
| `T₂`        | structural, lex2 | pred, double, add, mul, fact, fib              |
| `T_climbed` | structural, lex2 | pred, double, add, mul, fact, fib, ackermann, sudan |

Each transition is one `installSchema` or `installOp` call with an
admissibility proof (`by decide` for name freshness; `.head _` for
schema-presence). Per-rung well-formedness theorems
(`T₀_wellFormed`, …, `T_climbed_wellFormed`) witness that the climb
preserves `Theory.WellFormed`: distinct schema names, distinct
operator names, every operator's schema present.

**The headline.** Ackermann's step function has type:
```
(x : List Nat) → ((y : List Nat) → lex2Schema.rel y x → Nat) → Nat
```
You cannot place an `Operator structuralSchema` carrying this step,
because `structuralSchema.rel ≠ lex2Schema.rel`. The schema-operator
binding is enforced at admission by Lean's unifier.

## Files

| File | Purpose |
|---|---|
| `ClimbingCalc/Object.lean`   | `Schema`, `Operator S`, `AdmittedOperator`, `Theory`, `apply`, `SchemaAdmissible`, `OperatorAdmissible` |
| `ClimbingCalc/Schemas.lean`  | `structuralSchema`, `lex2Schema`, decrease helpers |
| `ClimbingCalc/Climb.lean`    | `installSchema`, `installOp`, `Theory.WellFormed` + preservation theorems |
| `ClimbingCalc/Demo.lean`     | Step functions for all operators; the climb sequence; per-rung WF theorems |
| `ClimbingCalc/Counter.lean`  | "Line crossed" witness: `ack(3,8) = 2045` |
| `Smoke.lean`                 | `lake exe smoke` |

## What's in scope (v2) vs out

**In scope (this version):**
- Two schemas with WF proofs: `structural`, `lex2`.
- Six structural operators: `pred`, `double`, `add`, `mul`, `fact`, `fib`.
- Two lex2 operators: `ackermann`, `sudan`.
- Type-level binding of operator to schema via `Operator (S : Schema)`.
- Admission preconditions and `Theory.WellFormed` preservation.

**Out of scope (potential v3):**
- LLM proposer cascade (step functions are Lean terms, not data; an
  LLM proposer would have to generate Lean source — feasible via
  `lake env lean --run` like climber, but not done here).
- Additional schemas (sum-measure, lex3, ε₀-recursion).
- Embedded-language *bodies* as data (option A in `AvsB.md`).

## Comparison to v1

v1 represented operators as opaque `fn : List Nat → Nat` with a
`schema : String` field that was checked only for presence in the
theory. The schema-operator binding lived at the level of "code
review" — a mislabeled operator was admissible. v2 lifts that
binding to the Lean type system: `Operator S` and `Operator S'`
are different types whenever `S ≠ S'`. The v1 invariants
(`SchemaAdmissible`, `OperatorAdmissible`, `Theory.WellFormed`) all
carry over; the type-level constraint is the new addition.
