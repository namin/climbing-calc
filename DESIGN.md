# climbing-calc — design

A calculator whose class of **admissible total functions grows
verifiably** under proposer/gate control. The keynote's running
example: climber re-rendered with computation as the substrate.

This file proposes design decisions and flags the ones that need
explicit input before implementation.

## Goal

Same kernel discipline as climber, with the substrate swapped from a
Hilbert-style derivation calculus to a small total functional language.
Each climb admits either:

1. a new **Lean-total** operator, with admission preconditions proving
   that its declared schema is installed and its name is fresh
   (`OperatorAdmissible`), or
2. a new **schema** (well-founded relation), certified well-founded
   by a Lean `WellFounded` proof, and with a fresh name
   (`SchemaAdmissible`).

In v1, every theory built through the climb API is well-formed:
distinct schema names, distinct operator names, every operator
references an installed schema. `Theory.WellFormed` is proved
preserved by `installSchema_wellFormed` and `installOp_wellFormed`,
and the climb's instantiation is witnessed by per-rung theorems
(`T₀_wellFormed`, `T_pred_wellFormed`, …, `T_climbed_wellFormed`).

**v1 limitation.** The `schema` field on an operator is informational:
checked at admission for *presence in the theory*, but not for
*structural binding to the operator's recursion*. An operator
declaring `schema := "structural"` could in principle have its `fn`
implemented by lex2-style recursion; v1 would admit it.

**v2 target.** Operator admission additionally certifies that the
operator's recursive calls in its body decrease under the admitted
schema's relation. This requires an embedded operator language; see
*v2 plan* below. With v2 in place, the climb would cross *structurally*
unreachable lines on the computational side, analogous to climber's
crossing of Peirce and Con(T₀): Ackermann is not admissible under
structural recursion alone; Goodstein's function is not admissible
without transfinite recursion; etc.

## The pattern, instantiated

| Role | Instance |
|---|---|
| Substrate | A small total functional language; theory `T = (schemas, operators)` |
| Proposer | Human or LLM offering an operator or a schema, with its certificate |
| Gate (v1, shipped) | Kernel checks: schema's `WellFounded` proof type-checks; operator's `fn` is Lean-typed total; admission preconditions hold (schema present, names fresh) |
| Gate (v2, target) | Additionally: operator's recursive calls in its body decrease under the admitted schema's relation (requires embedded-language substrate) |

## Design decisions: v1 shipped vs v2 target

Each subsection records the decision made, the v1 outcome, and (where
relevant) what was deferred to v2. The subsections originally framed
these as forks to choose between; that framing is preserved for
historical context.

### D1. Level 0: bare or PR built-in?

Options considered: (A) bare — only `zero`/`succ`, no schemas; first
climb must install `structural`. (B) PR built-in — level 0 starts with
the `structural` schema admitted.

**v1 shipped: (B), with a small twist.** Level 0 (`T₀`) explicitly
installs the `structural` schema as its first climb step, but no
operators come for free. The intermediate climbs (`T_pred`, …,
`T_fib`) admit PR operators one at a time. The pedagogy gains the
visible install of `structural` while avoiding the (A)-style trivial
opener.

### D2. Operator definition: embedded syntax or Lean function?

Options considered: (A) `Expr` body interpreted by `eval`; substrate
is a language. (B) Lean function; `apply` just dispatches.

**v1 shipped: (B), with the gap acknowledged.** Operators carry
`fn : List Nat → Nat`. The kernel accepts any Lean-total function;
the `schema` field on the operator records *which schema the operator
was admitted under* but does not constrain the function's recursion
shape. Admission preconditions check only schema presence and name
freshness.

**v2 target: (A)**, exactly as originally argued. The substrate
becomes an embedded `Expr` type; operators carry bodies; the
certificate is structural decrease per recursive call. The substrate
stops being "any Lean total function" and becomes "expressions in our
small language whose recursive calls are decreasing under the declared
schema's relation." This is the open structural fix; see *v2 plan*.

### D3. `eval` strategy: fuel-bounded or Lean-WF?

This decision is moot in v1 (no `eval`, since operators are Lean
functions). **For v2:** fuel-bounded `eval` remains the recommendation,
matching climber's style.

### D4. Termination certificate format

This decision is moot in v1 (operators carry their function directly).
**For v2:** direct Lean `WellFounded` proofs to start; a schema-
instantiation DSL is later ergonomics.

### D5. The disaster demo (without check)

Options considered: (A) bogus termination cert on an operator —
without check, `eval` loops. (B) bogus schema — without check,
operators under it admit and can loop.

**v1 shipped: neither directly.** `Schema` requires a `WellFounded`
proof in Lean, so a bogus schema cannot be constructed without
`sorry`. `Operator.fn` is a total Lean function, so a non-terminating
function cannot be constructed without `partial`. The "without check"
world is closed at the Lean type level, not via an external switch.

What *is* demonstrated: the admission gate refuses (1) operators
referencing absent schemas, (2) operator-name shadowing, and
(3) schema-name shadowing. Commented refusal witnesses in `Demo.lean`
each fail `by decide` at compile time on uncommenting.

### D6. Reflective depth

**v1 shipped: partial.** The kernel admits both operators (against
admitted schemas) and schemas (via direct WF proofs), and both go
through the same `WellFormed`-preserving admission API. So the gate's
admission criteria *can* be extended — `installSchema` adds a new
schema, which then governs subsequent operator admissions — but
schemas don't yet refer to each other's WF proofs (no transfinite
schema using a lex schema in its WF proof).

**v2 target:** make schemas compositional, e.g. an `epsilon0` schema
whose WF proof uses lex schemas internally; climber's `installPolicy`
analogue at the schema layer.

### D7. Headline pedagogical scenes

**v1 shipped: 7 scenes** in `Smoke.lean`, anchored by the climb
sequence in `Demo.lean`. The "kernel refuses Ackermann under
structural" scene from the original proposal isn't a real gate
firing in v1 — it's Lean's elaborator refusing a structural
termination measure for Ackermann's body, with the refusal recorded
as a commented `badAckImpl` in `Demo.lean`. In v2, the refusal would
become a true gate-level event.

### D8. Headline theorems

**v1 shipped:**
- **`empty_wellFormed`** — the empty theory is well-formed.
- **`installSchema_wellFormed`** / **`installOp_wellFormed`** —
  the climb API preserves well-formedness.
- **Per-rung theorems** — `T₀_wellFormed`, `T_pred_wellFormed`, …,
  `T_climbed_wellFormed`.

**v2 target:**
- **`climb_sound`** — every operator in any climbed theory is total
  *by structural decrease under its declared schema*. Requires
  embedded bodies.
- **`ackermann_not_admissible_in_T₀`** — countermodel showing the
  class admitted under `structural` alone is a proper subset of total
  functions. Requires syntactic characterization of structural-
  admissible bodies.

### D9. LLM proposer

**v1 shipped: not included.** Static demos only. v2 will follow the
climber/lean-sage Bedrock-cascade pattern.

## Architecture (v1, as shipped)

```
climbing-calc/
├── lakefile.lean
├── lean-toolchain                  # leanprover/lean4:v4.29.1
├── ClimbingCalc.lean               # top-level imports
├── ClimbingCalc/
│   ├── Object.lean                 # Schema, Operator, Theory, apply,
│   │                               # SchemaAdmissible, OperatorAdmissible
│   ├── Schemas.lean                # structuralSchema, lex2Schema
│   ├── Climb.lean                  # installSchema, installOp, WellFormed,
│   │                               # empty_wellFormed, installSchema_wellFormed,
│   │                               # installOp_wellFormed
│   ├── Demo.lean                   # the climb scenes, all operators, per-rung
│   │                               # WF theorems, commented refusal witnesses
│   └── Counter.lean                # "line crossed" witness (A(3,8) = 2045)
├── Smoke.lean                      # lake exe smoke
├── README.md
└── DESIGN.md                       # this file
```

v2 will add (or restore from this design's earlier sketch):
`Reflection.lean` (ε₀ rung), `Bedrock.lean`, `Elab.lean`,
`Runner.lean`, `RunnerMain.lean`.

## LOC (v1 actual)

| File | LOC |
|---|---|
| `Object.lean`   |  83 |
| `Schemas.lean`  |  30 |
| `Climb.lean`    | 150 |
| `Demo.lean`     | 325 |
| `Counter.lean`  |  56 |
| `Smoke.lean`    |  66 |
| (top-level)     |   5 |
| **total**       | **715** |

In line with the original ~700 LOC budget.

## Scope

**In scope (v1, shipped):**
- Levels 0 (structural) and 2 (structural + lex2).
- Two schemas (`structural`, `lex2`) with WF proofs.
- Operators: pred, double, add, mul, exp, fact, fib (structural);
  ackermann, sudan (lex2).
- Admission preconditions: `SchemaAdmissible` (name fresh),
  `OperatorAdmissible` (declared schema present, name fresh).
- Refusal witnesses: commented bogus-admission examples that the
  `by decide` proof obligation rejects at compile time.

**Known limitation of v1 (deferred to v2):**
- The bind between an operator's `fn` and its declared schema's
  relation is **informal**. An `Operator` carries `fn : List Nat → Nat`
  as opaque Lean data; the kernel accepts any total Lean function
  regardless of which schema name appears on the record. The current
  artifact illustrates the *architecture* of proof-bearing admission
  (and the most obvious abuses are blocked by `OperatorAdmissible`),
  but does not formally certify that the operator's recursive calls
  decrease under its declared schema. Closing this gap requires an
  embedded operator language; see below.

**Out of scope (deferred to v2 / v3):**
- Embedded operator language with structural termination certificates.
- Full Veblen hierarchy / ordinal notations.
- Higher-order operators.
- Polymorphic types.
- A general-purpose programming surface.
- LLM proposer cascade.
- Goodstein / ε₀ rung.

## v2 plan: embedded operator language

The structural fix for the v1 limitation is to stop representing
operators as opaque Lean functions. Give the calculator a small
expression language:

```lean
inductive Expr (arity : Nat) where
  | lit  : Nat → Expr arity
  | arg  : Fin arity → Expr arity
  | succ : Expr arity → Expr arity
  | pred : Expr arity → Expr arity
  | ifZero : Expr arity → Expr arity → Expr arity → Expr arity
  | call : (name : String) → (es : List (Expr arity)) → Expr arity
```

Then an `Operator` carries `body : Expr arity` together with a
termination certificate of the form:

> For every syntactic recursive call `call self [e₁, …, eₖ]` in
> `body`, evaluating `e₁, …, eₖ` under any input argument vector `v`
> produces a vector `v'` with `schema.rel v' v`.

The certificate is checked by the kernel before admission. The
calculator can then inspect proposed operator bodies *as data*,
verify their schema-relative termination, and only then extend its
own accepted operator set. That turns the artifact from:

> Lean proves these functions total, and the calculator records a
> schema label.

into:

> The calculator receives an operator description, checks its
> schema-relative termination certificate, and only then extends
> itself.

The latter is much closer to "reasonable reflection."

### v2 sub-suggestion: arity-indexed schemas

In v1, every `Schema` carries an arbitrary `Carrier : Type` and a
relation on it, while every operator's `fn` is `List Nat → Nat`. The
schema's relation is therefore not even type-aligned with the
operator's argument space. For v2, the cleaner shape is to
arity-index the schema:

```lean
structure Schema (arity : Nat) where
  name : String
  rel  : Vector Nat arity → Vector Nat arity → Prop
  wf   : WellFounded rel
```

Operators then declare their arity statically and pair with a
schema of matching arity. The embedded-language termination certificate
becomes "for every recursive call in `body`, the call's argument
vector is `rel`-less than the input argument vector" — both quantities
typed as `Vector Nat arity`, no list-length sanity-check needed at
runtime.

## Risks

- **`eval`'s fuel parameterization is awkward when operators recurse
  deeply.** Mitigation: choose fuel generously in demos; reserve
  totality theorem for the static proof.
- **`ackermann_not_admissible_in_T₀` may be more painful to formalize
  than expected.** The "class of operators admissible under
  `structural`" needs a precise characterization. Mitigation: define
  PR syntactically (one structural-decreasing arg per recursive call),
  show Ackermann's body can't be syntactically cast that way.
- **Embedded-syntax operators slow demos.** Mitigation: keep `Expr`
  minimal — no lambdas, no quote, just operator application and
  numerals.

## Open questions (for resolution before coding)

- D1 through D6 above each have a recommendation; please confirm or
  redirect.
- Naming: `ClimbingCalc` or shorter? (`Calc`, `Climb`.)
- Lean toolchain: match climber (`v4.29.1`) or lean-sage (`v4.20.0`)?
- Should `Counter.lean` produce a *concrete* separating witness
  (specific PR function f with f ≠ Ackermann on some input) or just
  prove the non-inclusion of classes? (Cleaner: concrete witness for a
  demoable proof; harder: class-level non-inclusion.)
