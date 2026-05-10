# climbing-calc

A calculator whose class of admissible total functions **grows
verifiably** under proposer/gate control. Each climb admits either a
new operator (certified to terminate under an admitted schema) or a
new schema (a well-founded relation, certified well-founded). The
class of admissible operators strictly grows across the climb.

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

Scene 3: T₁ — admit add, mul, exp under structural
  operators: [exp, mul, add]
  add([2, 3]): (some 5)
  mul([3, 4]): (some 12)
  exp([2, 5]): (some 32)

Scene 4: T₂ — install lex2 schema
  schemas: [lex2, structural]

Scene 5: T_climbed — admit ackermann under lex2
  operators: [ackermann, exp, mul, add]
  ackermann([0, 5]): (some 6)
  ackermann([1, 5]): (some 7)
  ackermann([2, 2]): (some 7)
  ackermann([3, 3]): (some 61)

Scene 6: refusal — wrong arity / unknown operator
  ackermann([1]): none
  nonexistent([0]): none

Scene 7: the line crossed
  ackermann([3, 7]): (some 1021)
  exp([2, 10]): (some 1024)
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
**The "without check" world is not even expressible without `sorry`.**

## The climb

| Theory | Schemas admitted | Operators admitted |
|---|---|---|
| `T_bare`    | —                       | —                          |
| `T₀`        | structural              | —                          |
| `T₁`        | structural              | add, mul, exp              |
| `T₂`        | structural, lex2        | add, mul, exp              |
| `T_climbed` | structural, lex2        | add, mul, exp, ackermann   |

Each transition is one `installSchema` or `installOp` call. The
recursion `A(n+1, m+1) = A(n, A(n+1, m))` calls back into itself with
the *same* first argument — no single coordinate decreases. The `lex2`
schema (lexicographic order on `Nat × Nat`) is the new well-foundedness
needed to admit it; once `lex2` is in the theory, Lean's elaborator
accepts `ackImpl` via the standard `termination_by` machinery.

## Files

| File | Purpose |
|---|---|
| `ClimbingCalc/Object.lean`   | `Schema`, `Operator`, `Theory`, `Theory.apply` |
| `ClimbingCalc/Schemas.lean`  | `structuralSchema`, `lex2Schema` |
| `ClimbingCalc/Climb.lean`    | `installSchema`, `installOp`, structural theorems |
| `ClimbingCalc/Demo.lean`     | The seven scenes; `addImpl`, `mulImpl`, `expImpl`, `ackImpl` |
| `ClimbingCalc/Counter.lean`  | The "line crossed" witness: `ack(3,7) > exp(2,10) − 3` |
| `Smoke.lean`                 | `lake exe smoke` |

## What's in scope (v1) vs out

**In scope (this version):**
- Two schemas: structural and lex2.
- Four operators: add, mul, exp, ackermann.
- Static demos via `lake exe smoke`.

**Out of scope (future):**
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
