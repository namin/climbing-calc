# climbing-calc — tutorial

## What is climbing-calc?

A small Lean artifact: a calculator that computes total functions on
the natural numbers — `add`, `mul`, `factorial`, `fibonacci`,
`ackermann`, Sudan's function — and whose collection of available
operators **grows over time through a sequence of admission steps**.

By the end of the shipped demo, the calculator can answer:

```
add(2, 3)        = 5
factorial(5)     = 120
fibonacci(10)    = 55
ackermann(3, 3)  = 61
ackermann(3, 8)  = 2045
```

There are many ways to write such a calculator. What's distinctive
here is the *architecture*: **Lean's type checker is the admission
gate.** Each operator is admitted into the theory only if its
termination structure type-checks against the relation of an
already-installed *schema* (a well-founded relation, with a Lean
`WellFounded` proof). An operator declaring "I recurse on a single
argument decreasing structurally" cannot have a step function that
internally does lexicographic recursion on two arguments — the types
don't unify, and Lean refuses to construct it.

## The "climb"

The pattern: start with an empty theory; install a schema (e.g.
`structural` — recursion decreasing the first argument); admit
operators under that schema (`add`, `mul`, `factorial`); install a
stronger schema when needed (e.g. `lex2` — lexicographic order on
two arguments); admit operators that need it (`ackermann`, `sudan`).
Each step is one Lean line with an admissibility proof. The theory
grows monotonically.

The smoke executable walks this climb scene by scene from `T_bare`
(empty) through `T_climbed` (two schemas, eight operators).

The "climb" terminology comes from the reflection-principle
literature (Feferman 1962, Beklemishev 2005): a sequence of
admissions that strictly grows what the system can express.
climbing-calc is the *computational* analogue of climber (which
climbs through proof systems instead of through total functions).

## Why this exists

climbing-calc is the keynote artifact for *reasonable reflection*:
the thesis that arbitrary self-extension of a system is sound when
each extension passes through a kernel-checked gate. Climbing-calc
makes the gate concrete and minimal: it's the Lean type checker, and
the gate's "certificate" is the type signature of the operator's
step function.

## What this tutorial covers

Nine sections walking through the architecture (Schema, Operator,
Theory), the two shipped schemas, two example operators in detail
(`add` and `ackermann`), the admission API, the climb sequence,
computation, refusal at the type level, and the `WellFormed`
invariant. The goal is to be **honest about what's proved**: which
claims are kernel-checked theorems, which are properties of the type
system, which are pedagogical narrative.

---

## What's shown — the honest list

**Kernel-checked, no `sorry`:**

1. Every `Schema` value carries a constructive `WellFounded` proof.
   This is a structural invariant: you cannot have a `Schema` in the
   system without Lean's type checker having accepted its WF
   certificate.
2. Every `Operator S` value carries a `step` function whose Lean type
   mentions `S.rel`. The recursion-handle's type is the binding: a
   step for one schema cannot be re-used under a different schema
   without a type error.
3. The admission API (`installSchema`, `installOp`) requires
   propositional preconditions: schema-name fresh, operator-name
   fresh, declared schema present in the theory.
4. `Theory.WellFormed` is preserved by both admission steps
   (`installSchema_wellFormed`, `installOp_wellFormed`).
5. Per-rung well-formedness: `T₀_wellFormed` through
   `T_climbed_wellFormed`, one theorem per admission, each by a
   one-liner.
6. All ten admitted operators compute via `WellFounded.fix`; the
   numerical examples (`add(2,3) = 5`, `ackermann(3,8) = 2045`, etc.)
   discharge by `native_decide`.

**Pedagogical, not separately proved as theorems:**

7. "The class of admissible operators grows under the climb." This
   follows from the type system rather than a single Lean theorem: an
   operator added at rung *n* remains in `T.operators` at all later
   rungs (witnessed by `installOp_preserves`).
8. "Mislabeled operators are unconstructible." This is a fact about
   what type-checks, demonstrated by commented refusal witnesses in
   `Demo.lean`. Not a Lean theorem.

**Not in this artifact:**

9. A `climb_sound` theorem in climber's style ("every operator in any
   climbed theory is total by structural decrease under its declared
   schema"). v2 relies on per-operator type-level construction to
   establish this per operator; a single quantified theorem would
   require induction over the climb with a richer invariant.
10. LLM proposer cascade. Operator step functions are Lean terms, not
    inspectable data.
11. Goodstein-style ε₀ recursion or other transfinite schemas.

---

## 1. Schemas

A schema is a named well-founded relation on argument lists:

```lean
structure Schema where
  name : String
  rel  : List Nat → List Nat → Prop
  wf   : WellFounded rel
```

The `wf` field is the kernel-checked certificate. Lean refuses to
construct a `Schema` value without it.

Two schemas are shipped (see `ClimbingCalc/Schemas.lean`):

```lean
def structuralSchema : Schema where
  name := "structural"
  rel  := fun y x => listHead0 y < listHead0 x
  wf   := InvImage.wf listHead0 Nat.lt_wfRel.wf
```

`structuralSchema`'s relation says "y is smaller than x iff y's head
is `Nat`-less than x's head." `InvImage.wf` lifts well-foundedness of
`Nat.lt` to this list-headed relation.

```lean
def lex2Schema : Schema where
  name := "lex2"
  rel  := fun y x => Prod.Lex (· < ·) (· < ·) (listLex2 y) (listLex2 x)
  wf   := InvImage.wf listLex2 (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
```

`lex2Schema`'s measure (`listLex2`) returns the first two list
elements as a pair; the relation is `Prod.Lex` on those pairs. The WF
proof composes `InvImage.wf` with the lex product of `Nat.lt`.

---

## 2. Operators are typed against a specific schema

This is the v2 headline. The structure:

```lean
structure Operator (S : Schema) where
  name  : String
  arity : Nat
  step  : (x : List Nat) → ((y : List Nat) → S.rel y x → Nat) → Nat
```

`Operator` is parameterized by a `Schema` value `S` — not by a name,
not by a free string, but by the actual `Schema` term. The `step`
field's type *mentions `S.rel`* in the recursion handle's signature.
You cannot supply a step whose recursive calls produce accessibility
witnesses in a *different* relation: the types don't unify.

The computable function is built via `WellFounded.fix`:

```lean
def Operator.fn {S : Schema} (op : Operator S) (args : List Nat) : Nat :=
  S.wf.fix op.step args
```

Lean's `WellFounded.fix` is computable, so `op.fn args` reduces to a
`Nat`. There is no fuel parameter — totality is structural.

---

## 3. Writing a simple operator: `add`

`add` under `structuralSchema` recurses on the first argument:

```lean
def addStep : (x : List Nat) → ((y : List Nat) → structuralSchema.rel y x → Nat) → Nat
  | [0, m],   _   => m
  | [n+1, m], rec =>
    rec [n, m] (structuralSchema.dec_first [m] [m] (by omega)) + 1
  | _,        _   => 0
```

Three clauses:

- `[0, m]` — base case; return `m`; ignore `rec`.
- `[n+1, m]` — recursive case; call `rec` with `[n, m]`, providing
  the accessibility witness via `structuralSchema.dec_first` (a small
  lemma that says "list with head `n` is `structuralSchema.rel`-less
  than list with head `n+1`"). The `by omega` discharges `n < n+1`.
- `_` — non-arity-2 catch-all; return 0.

The step's *type* enforces that any recursive call comes with a
witness in `structuralSchema.rel`. The pattern-matched `rec` only
accepts arguments paired with such a witness.

To install `add`, wrap it in an `AdmittedOperator`:

```lean
def addOp : AdmittedOperator := ⟨structuralSchema,
  { name := "add", arity := 2, step := addStep }⟩
```

The `AdmittedOperator` structure pairs the schema with the operator
typed against it. This is how theories carry heterogeneously-schema'd
operators in a single list.

---

## 4. Writing Ackermann

Ackermann under `lex2Schema`. The step function has type
`(x : List Nat) → ((y : List Nat) → lex2Schema.rel y x → Nat) → Nat`.
Three recursive clauses:

```lean
def ackStep : (x : List Nat) → ((y : List Nat) → lex2Schema.rel y x → Nat) → Nat
  | [0, m],     _   => m + 1
  | [n+1, 0],   rec =>
    rec [n, 1] (lex2Schema.dec_left [] [] (by omega))
  | [n+1, m+1], rec =>
    let inner := rec [n+1, m] (lex2Schema.dec_right [] [] (by omega))
    rec [n, inner] (lex2Schema.dec_left [] [] (by omega))
  | _,          _   => 0
```

The third clause has two recursive calls:

- `rec [n+1, m] ...` — same first arg, smaller second arg.
  Accessibility witness via `lex2Schema.dec_right` (lex prefers right
  decrease when first arg is equal).
- `rec [n, inner] ...` — smaller first arg, second arg is the inner
  result. Accessibility witness via `lex2Schema.dec_left` (lex prefers
  left decrease regardless of right).

**This is the headline.** Ackermann's step has type referring to
`lex2Schema.rel`. You cannot place this step inside an
`Operator structuralSchema` — `structuralSchema.rel` and
`lex2Schema.rel` are different relations, and the recursion handle's
type wouldn't unify. The kernel refuses the misplacement at the level
of type-checking, not via a downstream proof.

---

## 5. The admission API

Two functions install into a theory:

```lean
def Theory.installSchema (T : Theory) (s : Schema)
    (_ : SchemaAdmissible T s) : Theory :=
  { T with schemas := s :: T.schemas }

def Theory.installOp (T : Theory) (ao : AdmittedOperator)
    (_ : OperatorAdmissible T ao) : Theory :=
  { T with operators := ao :: T.operators }
```

The admissibility proofs are structures:

```lean
structure SchemaAdmissible (T : Theory) (s : Schema) : Prop where
  name_fresh : T.hasSchema s.name = false

structure OperatorAdmissible (T : Theory) (ao : AdmittedOperator) : Prop where
  schema_present : ao.schema ∈ T.schemas
  name_fresh     : T.hasOperator ao.op.name = false
```

`name_fresh` is a Boolean equation, discharged by `by decide`.
`schema_present` is propositional list membership. In every case in
the demo, the schema we're installing the operator under was just
installed (or is at the head of the schema list since the climb
hasn't intervened), so the witness is `.head _`.

---

## 6. Building the climb

The climb is a sequence of admissions. From `T_bare` (empty) to
`T_climbed` (everything):

```lean
def T_bare : Theory := Theory.empty

def T₀ : Theory := T_bare.installSchema structuralSchema ⟨by decide⟩

def T_pred   : Theory := T₀.installOp       predOp   ⟨.head _, by decide⟩
def T_double : Theory := T_pred.installOp   doubleOp ⟨.head _, by decide⟩
def T_add    : Theory := T_double.installOp addOp    ⟨.head _, by decide⟩
def T_mul    : Theory := T_add.installOp    mulOp    ⟨.head _, by decide⟩
def T_fact   : Theory := T_mul.installOp    factOp   ⟨.head _, by decide⟩
def T_fib    : Theory := T_fact.installOp   fibOp    ⟨.head _, by decide⟩
abbrev T₁ : Theory := T_fib

def T₂ : Theory := T₁.installSchema lex2Schema ⟨by decide⟩

def T_ack   : Theory := T₂.installOp    ackermannOp ⟨.head _, by decide⟩
def T_sudan : Theory := T_ack.installOp sudanOp     ⟨.head _, by decide⟩
abbrev T_climbed : Theory := T_sudan
```

Eleven explicit admissions, each requiring a proof. If you delete one
or change a schema name, the corresponding `by decide` or `.head _`
fails and the build breaks. **The climb is the sequence of admission
events, and each event is gated.**

---

## 7. Computing

`Theory.apply` looks up an operator by name, checks the arity, and
runs `S.wf.fix step`:

```lean
def Theory.apply (T : Theory) (name : String) (args : List Nat) : Option Nat :=
  match T.operators.find? (fun ao => ao.op.name == name) with
  | none    => none
  | some ao =>
    if ao.op.arity == args.length then some (ao.op.fn args) else none
```

Examples (each line `by native_decide` in `Demo.lean`):

```
T_climbed.apply "add"       [2, 3]    = some 5
T_climbed.apply "mul"       [3, 4]    = some 12
T_climbed.apply "fact"      [5]       = some 120
T_climbed.apply "fib"       [10]      = some 55
T_climbed.apply "ackermann" [3, 3]    = some 61
T_climbed.apply "ackermann" [3, 8]    = some 2045
T_climbed.apply "sudan"     [1, 2, 1] = some 8
```

Wrong arity returns `none`:

```
T_climbed.apply "ackermann" [1]       = none
T_climbed.apply "nonexistent" [0]     = none
```

---

## 8. Refusal at the type level

In `Demo.lean`, several commented examples document what doesn't
compile. The most pointed:

```lean
-- (1) Operator declares structuralSchema but its step references
--     lex2Schema's relation. The type doesn't unify; doesn't compile.
def mislabeled : AdmittedOperator := ⟨structuralSchema,
  { name := "mislabeled", arity := 2, step := ackStep }⟩
-- type error: ackStep expects lex2Schema.rel,
-- structuralSchema's rel is different
```

Uncomment this and `lake build` fails. The error is from Lean's
unifier, not a downstream certificate-checker. **The kernel is the
type checker.**

There's no separate "termination certificate" to maintain or get
wrong. The schema-operator binding is whatever Lean accepts.

---

## 9. The `WellFormed` invariant

```lean
def Theory.WellFormed (T : Theory) : Prop :=
  (T.schemas.map (·.name)).Nodup ∧
  (T.operators.map (fun ao => ao.op.name)).Nodup ∧
  ∀ ao ∈ T.operators, ao.schema ∈ T.schemas
```

Three clauses: distinct schema names, distinct operator names, every
operator's declared schema present in the theory.

Preservation theorems in `Climb.lean`:

```lean
theorem installSchema_wellFormed
    {T : Theory} (hT : T.WellFormed) {s : Schema}
    (hs : SchemaAdmissible T s) :
    (T.installSchema s hs).WellFormed

theorem installOp_wellFormed
    {T : Theory} (hT : T.WellFormed) {ao : AdmittedOperator}
    (hAdm : OperatorAdmissible T ao) :
    (T.installOp ao hAdm).WellFormed
```

Per-rung instantiation in `Demo.lean`:

```lean
theorem T₀_wellFormed       : T₀.WellFormed       :=
  installSchema_wellFormed empty_wellFormed       ⟨by decide⟩
theorem T_pred_wellFormed   : T_pred.WellFormed   :=
  installOp_wellFormed     T₀_wellFormed          ⟨.head _, by decide⟩
-- ... eleven theorems, one per admission ...
theorem T_climbed_wellFormed : T_climbed.WellFormed := T_sudan_wellFormed
```

Each one-liner threads the previous rung's well-formedness and the
admissibility witness through the corresponding preservation lemma.
The chain reaches `T_climbed_wellFormed` without `sorry`.

---

## What climbing-calc *doesn't* show, and why

It does not have a single `climb_sound` quantified theorem of the form
"for every climbed theory, every admitted operator is total." That's
because v2 already gets totality per-operator from `WellFounded.fix`:
each operator's `fn` is by construction the well-founded fix of its
step under its schema's WF proof, which Lean accepts only if the step
type-checks against `S.rel`. A quantified theorem would re-prove
this collectively. v2 prefers the type-level construction over the
universally-quantified soundness statement.

It does not represent operator bodies as inspectable data. An
`Operator S`'s `step` is a Lean closure. There is no `Expr` AST that
an LLM proposer could ship as JSON. That's the rejected v2-A path;
it would have given a more demoable "the kernel
receives a body and checks it" slide at the cost of substantial
engineering. v2-B's bet is that **type-level binding** carries more
formal rigor than **body-as-data inspectability**, even if the latter
has better narrative.

It does not include LLM-driven extension. The climb is hand-written.
A v3 with Bedrock cascade (climber's pattern) would extend the
artifact without changing its formal claims.

---

## Where to look next

- `ClimbingCalc/Object.lean` — the structural types and `Theory.apply`.
- `ClimbingCalc/Schemas.lean` — the two schemas and the decrease helpers.
- `ClimbingCalc/Climb.lean` — admission API, `WellFormed`, preservation.
- `ClimbingCalc/Demo.lean` — all step functions; the climb; per-rung WF.
- `ClimbingCalc/Counter.lean` — `ackermann(3,8) = 2045`.
- `Smoke.lean` — the scene-by-scene executable; run with `lake exe smoke`.
- `DESIGN.md` — design rationale for v2-B vs v2-A.
- `README.md` — summary, comparison to v1.
