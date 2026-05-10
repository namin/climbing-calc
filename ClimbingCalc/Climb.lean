import ClimbingCalc.Object

namespace ClimbingCalc

/-! ## The climb: admission API and structural theorems

A climb is a sequence of admissions. Each step appends either a schema
(which must be a `Schema`, i.e. carry a well-foundedness proof, *and*
must have a fresh name) or an operator (whose `fn` is a Lean-typed
total function, *and* whose declared schema is already present, *and*
whose name is fresh).

The kernel's role is structural:

1. `Schema` itself requires a `WellFounded` field — Lean's type
   checker rejects bogus schemas without `sorry`.
2. `Operator.fn : List Nat → Nat` must be a total Lean function —
   ditto.
3. `installSchema` requires `SchemaAdmissible` — no shadow schemas.
4. `installOp` requires `OperatorAdmissible` — no operators referencing
   absent schemas, no shadowing names.

What's *not* enforced at this layer: the operator's `fn` actually
decreases under its declared schema's relation. See `Object.lean`,
*Admissibility preconditions*, for the limitation and the v2 plan.
-/

/-- Append a schema. Requires `SchemaAdmissible` (name freshness). -/
def Theory.installSchema (T : Theory) (s : Schema)
    (_ : SchemaAdmissible T s) : Theory :=
  { T with schemas := s :: T.schemas }

/-- Append an operator. Requires `OperatorAdmissible`: the declared
schema must be in the theory and the operator name must be fresh. -/
def Theory.installOp (T : Theory) (op : Operator)
    (_ : OperatorAdmissible T op) : Theory :=
  { T with operators := op :: T.operators }

/-! ## Structural theorems -/

/-- Schemas survive subsequent installations. -/
theorem installSchema_preserves (T : Theory) (s : Schema)
    (h : SchemaAdmissible T s) (s' : Schema) (h' : s' ∈ T.schemas) :
    s' ∈ (T.installSchema s h).schemas := by
  simp [Theory.installSchema, List.mem_cons]; exact Or.inr h'

/-- Operators survive subsequent installations. -/
theorem installOp_preserves (T : Theory) (op : Operator)
    (h : OperatorAdmissible T op) (op' : Operator) (h' : op' ∈ T.operators) :
    op' ∈ (T.installOp op h).operators := by
  simp [Theory.installOp, List.mem_cons]; exact Or.inr h'

/-- Any schema present in a theory has a constructive well-foundedness
proof. This is the kernel's invariant: schemas cannot enter a theory
without their WF proof type-checking. -/
theorem schema_admitted_means_wf (T : Theory) (s : Schema) (_ : s ∈ T.schemas) :
    WellFounded s.rel := s.wf

end ClimbingCalc
