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

1. a new total operator, certified to terminate via an admitted
   well-foundedness schema, or
2. a new schema (well-founded relation), certified well-founded.

The class of admissible operators strictly grows across the climb. At
level 0 (primitive recursion), Ackermann is provably inadmissible;
after installing a lex schema, Ackermann admits; further climbs admit
transfinite recursion. The headline crosses Peirce/Con(T₀) analogues
on the computational side: **Ackermann is not primitive-recursive,
Goodstein's function is not provably total in PA, both become
admissible after appropriate schema admissions**.

## The pattern, instantiated

| Role | Instance |
|---|---|
| Substrate | A small total functional language; theory `T = (schemas, operators)` |
| Proposer | Human or LLM offering an operator or a schema, with its certificate |
| Gate | Kernel checks: schema's well-foundedness proof type-checks; operator's recursive calls decrease under an admitted schema |

## Decisions to make

### D1. Level 0: bare or PR built-in?

- **A. Bare.** Level 0 has only `zero` and `succ`. No schemas admitted.
  First climb must install `structural` schema before any recursion is
  possible.
- **B. PR built-in.** Level 0 has `zero`, `succ`, and the `structural`
  schema. Any PR operator (`add`, `mul`, `exp`) admits from the start.

**Recommendation: B.** PR is well-understood, and the headline climb
(PR → Ackermann) lands cleanly because Ackermann is provably not PR.
With A, half the demo is installing `add` and `mul`, which adds
exposition without payoff.

### D2. Operator definition: embedded syntax or Lean function?

- **A. Embedded syntax.** Operators carry an `Expr` body parametric
  over arg numerals; `eval` interprets bodies relative to a theory.
  Substrate is genuinely *a language*; the climb is visible at the
  level of source code.
- **B. Lean function.** Operators carry a `Nat → ... → Nat` Lean
  function. `eval` just dispatches. Substrate is "any Lean total
  function;" climb is trivial because Lean already enforces totality.

**Recommendation: A.** B collapses the substrate into Lean itself —
there's nothing to climb because Lean's kernel is already the gate.
A makes "the calculator is a language with its own admissibility
criterion" visible, which is the whole pedagogical point.

### D3. `eval` strategy: fuel-bounded or Lean-WF?

- **A. Fuel-bounded.** `eval : Theory → Nat → Expr → Option Nat`. Easy
  to define. Totality is a separate theorem: for each admitted theory
  `T` and input `e`, there exists `fuel` with `eval T fuel e ≠ none`.
- **B. Lean-WF.** Define `eval` via Lean's well-founded recursion using
  the theory's certified schemas as the termination measure.
  Conceptually clean but engineering is hard — Lean's `termination_by`
  needs the measure visible at definition time, and theories are
  runtime data.

**Recommendation: A.** Fuel-bounded is climber-style and avoids the
worst engineering tarpit. Totality lives at the proof level, not the
definition level.

### D4. Termination certificate format

A certificate proves: every recursive call in this operator's body
decreases under some admitted schema's well-founded relation.

- **A. Direct Lean `WellFounded` proof.** Maximum flexibility,
  matches climber's `SoundExtension.sound`. Verbose.
- **B. Schema-instantiation DSL.** Each schema exposes a structured
  check (e.g., `structural` exposes "show the first argument is
  syntactically a constructor smaller than the LHS"); the certificate
  is the instantiation data. Cleaner demos but more code.

**Recommendation: A for v1, B as future work.** Get the soundness
theorem proved first; ergonomics later.

### D5. The disaster demo (without check)

- **A. Bogus termination cert.** The proposer claims `structural`
  decrease where the recursive call doesn't actually decrease.
  Without the kernel check, `eval` enters an infinite loop.
- **B. Bogus schema.** The proposer claims a non-well-founded relation
  is well-founded. Same effect: admitted operators under it can loop.

**Recommendation: B.** Higher-leverage — one bad schema corrupts every
operator under it, including future ones. Mirrors lean-sage's "without
governance, `(+ 1 2) ⇒ 0`" but at the schema layer.

### D6. Reflective depth

The architecture wants two-level reflection: the schema gate is itself
extensible through the kernel. Concretely:

- The kernel admits operators against admitted schemas.
- The kernel admits schemas via direct Lean WF proofs.
- A schema, once admitted, can itself be invoked by *later schemas* —
  e.g., a transfinite schema may use a lex schema in its WF proof.

This makes "the gate's admission criteria are themselves modifiable
through the gate" literal. Same shape as climber's `installPolicy`.

### D7. Headline pedagogical scenes

Proposed scene list for `Demo.lean`:

1. **Level 0.** `T₀ = ⟨structural⟩` + no operators. State: PR is
   admissible-in-principle, no operators yet installed.
2. **Climb 1.** Install `add`, `mul`, `exp` under `structural`. All admit.
3. **Climb 2 (refused).** Propose `Ackermann` under `structural`. The
   recursive call `A(n, A(S n, m))` doesn't decrease the first arg
   alone — kernel refuses. (The audience sees the gate biting.)
4. **Climb 3.** Install `lex2` schema. WF proof: lex order on `Nat × Nat`
   is well-founded (one Lean lemma).
5. **Climb 4.** Install `Ackermann` under `lex2`. Admits.
6. **Compute.** `Ackermann(3, 3) = 61`. `Ackermann(4, 1) = 65533`.
7. **Counterpoint.** `ackermann_not_PR`: in a separating model (the
   class of all PR-definable functions), Ackermann isn't reachable.
   The line is crossed *provably*, not just empirically.

Optional further rung (probably v2):

8. **Climb 5.** Install `epsilon0` schema. Install Goodstein. Compute
   a small value. Crosses the "PA-provable totality" line.

### D8. Headline theorems

Concrete proof obligations:

- **`climb_sound`** — every operator in any climbed theory is total.
  By induction on climbing steps; each step's certificate type-checked
  at admission. (Analogue: climber's `climb_sound`.)
- **`ackermann_not_admissible_in_T₀`** — countermodel. The class of
  functions admissible under `structural` alone is a proper subset of
  total functions. Ackermann's three-clause definition cannot be cast
  to fit `structural`. (Analogue: climber's `peirce_not_derivable_in_T₀`.)
- **`T_climbed_admits_ackermann`** — after `installSchema lex2;
  installOp ackermann`, `Ackermann` is in `T_climbed.operators` with
  a valid certificate. (Analogue: climber's `T₁_derives_peirce`.)

### D9. LLM proposer

Same shape as climber/lean-sage/defeater: Bedrock cascade. Each round
asks Claude for either an operator or a schema; kernel admits or refuses;
admitted items accumulate in a regenerated `Climbed.lean`. Probably
slot in as v2 after the static demos work.

**Decision:** static demos first, LLM cascade after.

## Architecture sketch

```
climbing-calc/
├── lakefile.lean
├── lean-toolchain                  # leanprover/lean4:v4.29.1 (match climber)
├── ClimbingCalc.lean               # top-level imports
├── ClimbingCalc/
│   ├── Object.lean                 # Expr, Theory, eval (fuel), Operator, Schema
│   ├── Climb.lean                  # installSchema, installOp, climb_sound
│   ├── Schemas.lean                # structural, lex2, (epsilon0 v2)
│   ├── Demo.lean                   # the 7 scenes, Ackermann admitted
│   ├── Counter.lean                # ackermann_not_PR separating model
│   ├── Reflection.lean             # (v2) epsilon0 / Goodstein rung
│   ├── Bedrock.lean                # (v2) LLM wrapper
│   ├── Elab.lean                   # (v2) splice and admit
│   └── Runner.lean                 # (v2) cascade orchestrator
├── Smoke.lean                      # lake exe smoke
├── RunnerMain.lean                 # (v2)
├── README.md
└── DESIGN.md                       # this file
```

## LOC budget

Target ~700 LOC for v1 (no LLM):

- `Object.lean` ~200 — `Expr`, `Theory`, fuel-bounded `eval`, `Operator`, `Schema`.
- `Climb.lean` ~250 — `installSchema`, `installOp`, `climb_sound`.
- `Schemas.lean` ~100 — `structural`, `lex2` with WF proofs.
- `Demo.lean` ~100 — 7 scenes.
- `Counter.lean` ~50 — separating model for Ackermann-not-PR.

v2 adds ~600 LOC for the LLM cascade and the ε₀ rung.

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
