# climbing-calc — design (v2)

A calculator whose class of admissible total functions grows under
**type-level proof-bearing admission**. The keynote's running
example: climber re-rendered with computation as the substrate.

For v1's design (now superseded), see the git history.

## Goal

Same kernel discipline as climber, with the substrate swapped from a
Hilbert-style derivation calculus to a small total functional
language. Each climb admits either:

1. a new **schema** — a well-founded relation on `List Nat` with a
   Lean `WellFounded` proof, and with a fresh name
   (`SchemaAdmissible`).
2. a new **operator** — typed against an admitted schema. The
   operator's `step` function carries the schema's relation in its
   type signature; Lean's type checker rejects any step whose
   recursive calls don't supply schema-relative accessibility
   witnesses. Plus admission preconditions: the declared schema is
   present in the theory, the operator's name is fresh
   (`OperatorAdmissible`).

In v2, the schema-operator binding is **at the Lean type level**.
There is no separate termination certificate to maintain; the step
function's type *is* the certificate.

## The pattern, instantiated

| Role | Instance |
|---|---|
| Substrate | Theory `T = (schemas, operators)`; operators are `WellFounded.fix step` over schema's WF proof |
| Proposer | Human (in this artifact) offering a schema with WF proof, or an operator with a step function typed against a declared schema |
| Gate | Lean's type checker: `Schema` requires `WellFounded`; `Operator S` requires step with `S.rel` in its type. Plus `SchemaAdmissible` / `OperatorAdmissible` admission preconditions. |

## Core types

```lean
structure Schema where
  name : String
  rel  : List Nat → List Nat → Prop
  wf   : WellFounded rel

structure Operator (S : Schema) where
  name  : String
  arity : Nat
  step  : (x : List Nat) → ((y : List Nat) → S.rel y x → Nat) → Nat

structure AdmittedOperator where
  schema : Schema
  op     : Operator schema

structure Theory where
  schemas   : List Schema
  operators : List AdmittedOperator
```

The operator's runtime function is `S.wf.fix op.step`. Lean's
`WellFounded.fix` is computable; `Theory.apply T name args` evaluates
to the operator's value.

## Schemas

Schemas are well-founded relations on `List Nat`, expressed via a
measure pulled from the argument list and `InvImage.wf`:

- `structuralSchema`: measure = head of list (or 0 for empty);
  relation lifted from `Nat.lt`. Admits operators that recurse by
  decreasing the first argument.
- `lex2Schema`: measure = first two elements (padded with 0);
  relation lifted from `Prod.Lex Nat.lt Nat.lt`. Admits operators
  with lex-recursion on the first two args — Ackermann, Sudan.

Schemas come with small "decrease helpers" (`structuralSchema.dec_first`,
`lex2Schema.dec_left`, `lex2Schema.dec_right`) so step functions can
build accessibility witnesses readably.

## Admission API

```lean
def Theory.installSchema (T : Theory) (s : Schema)
    (_ : SchemaAdmissible T s) : Theory

def Theory.installOp (T : Theory) (ao : AdmittedOperator)
    (_ : OperatorAdmissible T ao) : Theory
```

`SchemaAdmissible T s` requires `T.hasSchema s.name = false`
(provable by `by decide`).

`OperatorAdmissible T ao` requires:
- `ao.schema ∈ T.schemas` (propositional list membership, provable
  by `.head _` since each newly-installed schema is at the list head);
- `T.hasOperator ao.op.name = false` (by `by decide`).

## Well-formed theories

```lean
def Theory.WellFormed (T : Theory) : Prop :=
  (T.schemas.map (·.name)).Nodup ∧
  (T.operators.map (fun ao => ao.op.name)).Nodup ∧
  ∀ ao ∈ T.operators, ao.schema ∈ T.schemas
```

`installSchema_wellFormed` and `installOp_wellFormed` prove the
preservation: every theory built through the climb API is well-formed.
Per-rung WF theorems witness this concretely:
`T₀_wellFormed`, `T_pred_wellFormed`, …, `T_climbed_wellFormed`.

## Operators in the v2 zoo

Under `structuralSchema`:
- `pred`, `double` — no recursion, just direct computation.
- `add`, `mul`, `fact`, `fib` — recurse decreasing the first argument.
  Each step function uses `structuralSchema.dec_first` to supply the
  accessibility witness.

Under `lex2Schema`:
- `ackermann` — three-clause double recursion. The
  `A(n+1, m+1) = A(n, A(n+1, m))` case has two recursive calls; the
  outer call drops in the first argument (`dec_left`), the inner call
  drops in the second (`dec_right`).
- `sudan` — three-argument lex2 recursion. The third argument is a
  parameter (not part of the measure); args are presented as
  `[n, y, x]` so the first two list elements align with the
  `(n, y)` measure.

## What v2 closes that v1 didn't

v1's `Operator` was:
```lean
structure Operator where
  name   : String
  arity  : Nat
  schema : String
  fn     : List Nat → Nat
```
The `schema` field was a free-floating string. The kernel checked at
admission that the name was in the theory, but nothing bound `fn`'s
internal recursion shape to the schema named.

v2's `Operator (S : Schema)`:
- Parameterized by a *Schema value*, not a name.
- The step function's type contains `S.rel`.
- The "gate" is Lean's type checker: an `Operator structuralSchema`
  whose step uses lex2-accessibility won't unify.

This closes the reviewer's main concern: in v1, a mislabeled
operator could be admitted (claim `schema := "structural"`, internally
use lex2 recursion); v2 makes that unconstructible.

## Architecture (as shipped)

```
climbing-calc/
├── lakefile.lean
├── lean-toolchain                  # leanprover/lean4:v4.29.1
├── ClimbingCalc.lean               # top-level imports
├── ClimbingCalc/
│   ├── Object.lean                 # Schema, Operator S, AdmittedOperator,
│   │                               # Theory, apply, SchemaAdmissible,
│   │                               # OperatorAdmissible
│   ├── Schemas.lean                # structuralSchema, lex2Schema,
│   │                               # decrease helpers
│   ├── Climb.lean                  # installSchema, installOp, WellFormed,
│   │                               # empty_wellFormed,
│   │                               # installSchema_wellFormed,
│   │                               # installOp_wellFormed
│   ├── Demo.lean                   # step functions for all operators,
│   │                               # climb sequence, per-rung WF theorems
│   └── Counter.lean                # "line crossed" witness
├── Smoke.lean                      # lake exe smoke
├── README.md
└── DESIGN.md                       # this file
```

## What v2 doesn't include

- **LLM proposer cascade.** Operator step functions are Lean terms,
  not data. An LLM proposer would have to generate Lean source and
  elaborate it via `lake env lean --run` (climber's pattern). Not
  implemented here.
- **Goodstein / ε₀ recursion.** Would require a transfinite-ordinal
  schema. Out of scope.
- **Embedded operator *bodies* as data** (the rejected v2-A path).
  Operator bodies are Lean closures, not inspectable ASTs.

## The remaining gap

v2 makes the schema-operator binding type-level. What it does *not*
do:

- **Compute soundness across the climb as a single theorem.** We
  don't prove "every operator in any climbed theory is total" — we
  rely on the type-level construction guaranteeing this per operator,
  plus `WellFormed` for the structural invariants. A single
  `climb_sound` theorem in the climber style would require induction
  over the climb sequence with a richer invariant.
- **Inspect operator bodies.** A v3 with embedded `Expr` bodies
  (the A path) would allow this. v2's operator bodies are Lean
  closures.

These are not gaps in v2's *correctness story* — they're features
that v2 doesn't deliver but doesn't claim to.
