import ClimbingCalc.Object

namespace ClimbingCalc

/-! ## The climb: admission API and headline theorems

A climb is a sequence of admissions. Each step appends either a schema
(which must be a `Schema`, i.e. carry a well-foundedness proof) or an
operator (whose `fn` is a Lean-typed total function).

The kernel's role is structural: `Schema` requires a `WellFounded` field;
`Operator` requires a total `fn : List Nat → Nat`. Lean's type checker
rejects ill-formed candidates at admission, so the "without check" world
is not even expressible without `sorry`.
-/

/-- Append a schema. The kernel admits iff `s` is a valid `Schema` value
(i.e. Lean accepts its `wf` field as `WellFounded`). -/
def Theory.installSchema (T : Theory) (s : Schema) : Theory :=
  { T with schemas := s :: T.schemas }

/-- Append an operator. The kernel admits iff `op` is a valid `Operator`
value (i.e. Lean accepts its `fn` field as a total function). The `schema`
field records which schema the operator was admitted under. -/
def Theory.installOp (T : Theory) (op : Operator) : Theory :=
  { T with operators := op :: T.operators }

/-- Convenience: install several operators in sequence. -/
def Theory.installOps (T : Theory) : List Operator → Theory
  | []      => T
  | o :: os => (T.installOp o).installOps os

/-! ## Headline theorems -/

/--
**`installSchema_preserves`**: schemas survive installation. -/
theorem installSchema_preserves (T : Theory) (s : Schema) (s' : Schema)
    (h : s' ∈ T.schemas) : s' ∈ (T.installSchema s).schemas := by
  simp [Theory.installSchema, List.mem_cons]; exact Or.inr h

/--
**`installOp_preserves`**: operators survive installation. -/
theorem installOp_preserves (T : Theory) (op : Operator) (op' : Operator)
    (h : op' ∈ T.operators) : op' ∈ (T.installOp op).operators := by
  simp [Theory.installOp, List.mem_cons]; exact Or.inr h

/--
**`schema_admitted_means_wf`**: any schema present in a theory has a
constructive well-foundedness proof. This is the kernel's invariant: you
cannot have a schema in a theory without its WF proof type-checking.
-/
theorem schema_admitted_means_wf (T : Theory) (s : Schema) (_ : s ∈ T.schemas) :
    WellFounded s.rel := s.wf

end ClimbingCalc
