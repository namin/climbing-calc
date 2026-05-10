# climbing-calc

A calculator whose class of admissible total functions **grows under
proof-bearing admission**. Each climb admits either a new operator
(represented by a Lean-total function, admitted only if it names an
already-installed schema and has a fresh name) or a new schema (a
well-founded relation, certified well-founded by a Lean `WellFounded`
proof). The class of admissible operators grows monotonically across
the climb.

**What v1 establishes** is the *architecture* of proof-gated extension:
schemas can't enter the theory without a `WellFounded` proof; operators
can't enter without referencing an installed schema; nothing shadows.

**What v1 does NOT yet certify** is that an operator's recursion
actually decreases under its declared schema's relation. The
`schema` field is informational at this layer — it's checked at
admission for *presence in the theory* but not for *structural
binding to the function's recursion*. Closing that gap is the v2
embedded-language plan described in [`DESIGN.md`](DESIGN.md).

Climber re-rendered with computation as the substrate. Same kernel
discipline, different substrate, headline crosses a *computational*
unreachable line: Ackermann is not admissible under structural
recursion alone, but admits after the `lex2` schema is installed.

See [`DESIGN.md`](DESIGN.md) for the design rationale and decisions.

## Status

Builds clean on `leanprover/lean4:v4.29.1`. Zero `sorry`s. Smoke
executable demonstrates the climb scene by scene.

```bash
$ lake build
Build completed successfully (8 jobs).

$ lake exe smoke
================================================================
climbing-calc — the calculator that climbs
================================================================

Scene 1: T_bare — empty theory
  schemas: []
  operators: []

Scene 2: T₀ — install structural schema
  schemas: [structural]
  operators: []

Scene 3: T₁ — admit PR operators under structural
  operators: [fib, fact, exp, mul, add, double, pred]
  pred([7]): (some 6)
  double([7]): (some 14)
  add([2, 3]): (some 5)
  mul([3, 4]): (some 12)
  exp([2, 5]): (some 32)
  fact([5]): (some 120)
  fib([10]): (some 55)

Scene 4: T₂ — install lex2 schema
  schemas: [lex2, structural]

Scene 5: T_climbed — admit ackermann and sudan under lex2
  operators: [sudan, ackermann, fib, fact, exp, mul, add, double, pred]
  ackermann([0, 5]): (some 6)
  ackermann([1, 5]): (some 7)
  ackermann([2, 2]): (some 7)
  ackermann([3, 3]): (some 61)

  sudan([0, 5, 3]): (some 8)
  sudan([1, 1, 1]): (some 3)
  sudan([1, 1, 2]): (some 8)
  sudan([2, 1, 1]): (some 8)

Scene 6: refusal — wrong arity / unknown operator
  ackermann([1]): none
  sudan([1, 1]): none
  nonexistent([0]): none

Scene 7: the line crossed
  ackermann([3, 8]): (some 2045)
  exp([2, 10]): (some 1024)
  fact([10]): (some 3628800)
  A(3, 8) = 2045 > 1024 = exp(2, 10);
  Ackermann outgrows any fixed exponential; lex2 admits the shape.
```

## The pattern

| Role | Instance |
|---|---|
| Substrate | A theory `T = (schemas, operators)`; operators are total `List Nat → Nat` functions |
| Proposer | Human or LLM offering an operator or schema with its certificate |
| Gate | Lean's kernel: `Schema` requires `WellFounded`; `Operator` requires a total `fn` |

The kernel-checked invariants live in the Lean types themselves. A
`Schema` value cannot exist without a constructive `WellFounded` proof;
an `Operator` value cannot exist without a Lean-typed total function.
`Theory.installSchema` requires a `SchemaAdmissible` proof (name
fresh); `Theory.installOp` requires `OperatorAdmissible` (declared
schema present *and* operator name fresh). Bogus admissions — claiming
a schema that hasn't been installed, or shadowing an existing operator
— are rejected at admission time. `Theory.WellFormed` is preserved by
the climb API: every theory built through `installSchema`/`installOp`
has distinct schema names, distinct operator names, and every
operator's declared schema is present.

**The remaining gap.** None of the above certifies that an operator's
`fn` *actually decreases* under its declared schema's relation. An
`Operator` carries `fn : List Nat → Nat` as opaque Lean data; Lean's
type checker accepts any total function, regardless of which schema
name appears on the record. So a v1 operator could in principle name
`"structural"` while internally using Ackermann's recursion — the
gate would admit it. Closing that gap is v2: an embedded operator
language with a structural termination certificate per recursive
call. See [`DESIGN.md`](DESIGN.md), *v2 plan*.

## The climb

| Theory | Schemas admitted | Operators admitted |
|---|---|---|
| `T_bare`    | —                | —                                                       |
| `T₀`        | structural       | —                                                       |
| `T₁`        | structural       | pred, double, add, mul, exp, fact, fib                  |
| `T₂`        | structural, lex2 | pred, double, add, mul, exp, fact, fib                  |
| `T_climbed` | structural, lex2 | pred, double, add, mul, exp, fact, fib, ackermann, sudan |

Each transition is one `installSchema` or `installOp` call. The
recursions `A(n+1, m+1) = A(n, A(n+1, m))` and Sudan's
`F_{n+1}(x, y+1) = F_n(F_{n+1}(x, y), F_{n+1}(x, y) + y + 1)` call back
into themselves with the *same* first argument — no single coordinate
decreases. The `lex2` schema (lexicographic order on `Nat × Nat`) is
the new well-foundedness needed to admit them; once `lex2` is in the
theory, Lean's elaborator accepts both via the standard `termination_by`
machinery.

**The refusal witness.** `Demo.lean` carries a commented-out
`badAckImpl` that's exactly Ackermann's shape but asks Lean to admit
it under a structural measure on the first argument alone. The build
fails on uncommenting; this is the "without the gate" world made
visible at compile time.

## Files

| File | Purpose |
|---|---|
| `ClimbingCalc/Object.lean`   | `Schema`, `Operator`, `Theory`, `Theory.apply`, `SchemaAdmissible`, `OperatorAdmissible` |
| `ClimbingCalc/Schemas.lean`  | `structuralSchema`, `lex2Schema` |
| `ClimbingCalc/Climb.lean`    | `installSchema`, `installOp`, `Theory.WellFormed` + preservation theorems |
| `ClimbingCalc/Demo.lean`     | The scenes; `addImpl`, `mulImpl`, `expImpl`, `factImpl`, `fibImpl`, `ackImpl`, `sudanImpl`; refusal witnesses |
| `ClimbingCalc/Counter.lean`  | The "line crossed" witness: `ack(3,8) = 2045 > 1024 = exp(2,10)` |
| `Smoke.lean`                 | `lake exe smoke` |

## What's in scope (v1) vs out

**In scope (this version):**
- Two schemas: `structural`, `lex2`.
- Seven operators under `structural`: `pred`, `double`, `add`, `mul`,
  `exp`, `fact`, `fib`.
- Two operators under `lex2`: `ackermann`, `sudan`.
- Admission preconditions (`SchemaAdmissible`, `OperatorAdmissible`)
  enforced at install time via `by decide`.
- `Theory.WellFormed` invariant and preservation theorems for the
  climb API.
- Refusal witnesses (commented examples in `Demo.lean`).
- Static demos via `lake exe smoke`.

**Out of scope (deferred to v2):**
- Embedded operator language with per-call structural termination
  certificates — the deeper coupling of `fn` to its declared schema.
- Goodstein's function (ε₀ recursion, crosses the PA-provable-totality line).
- LLM proposer cascade (Bedrock-mediated, climber-style).
- Mechanical proof that operators under `structural` form a proper
  subclass of total functions (Ackermann-not-PR as a Lean theorem).
- Higher-arity schemas, dependent recursion.

## Why this is the keynote example

The original Smith/Black tower's `(em (set! base-apply ...))` modifies
the evaluator; the headline is "checking caught up with reflection."
`climbing-calc`'s analogue: the proposer modifies the *theory of
admissible functions*; the kernel checks via Lean's typing discipline;
the climb crosses a line the starting theory cannot reach. The
"impossible before" use case is a calculator that genuinely extends
what it can compute in place, with a kernel-checked totality invariant
preserved across every rung.
