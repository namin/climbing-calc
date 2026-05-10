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
5. `Theory.WellFormed` is preserved by the climb API (theorems below).

What's *not* enforced at this layer: the operator's `fn` actually
decreases under its declared schema's relation. See `Object.lean`,
*Admissibility preconditions*, for the limitation and the v2 plan.
-/

/-- Install a schema (prepend, with freshness check). Requires
`SchemaAdmissible` (name freshness). -/
def Theory.installSchema (T : Theory) (s : Schema)
    (_ : SchemaAdmissible T s) : Theory :=
  { T with schemas := s :: T.schemas }

/-- Install an operator (prepend, with admissibility check). Requires
`OperatorAdmissible`: the declared schema must be in the theory and
the operator name must be fresh. -/
def Theory.installOp (T : Theory) (op : Operator)
    (_ : OperatorAdmissible T op) : Theory :=
  { T with operators := op :: T.operators }

/-! ## Membership preservation -/

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

/-! ## Well-formed theories

A theory is *well-formed* iff its schema names are distinct, its
operator names are distinct, and every operator references an
installed schema. The bare `Theory` structure has no built-in
guarantees; well-formedness is the invariant that the climb API
preserves.
-/

/-- A theory is well-formed when:
* schema names are pairwise distinct,
* operator names are pairwise distinct, and
* every operator's declared schema is present in the theory. -/
def Theory.WellFormed (T : Theory) : Prop :=
  (T.schemas.map (·.name)).Nodup ∧
  (T.operators.map (·.name)).Nodup ∧
  ∀ op ∈ T.operators, T.hasSchema op.schema = true

theorem empty_wellFormed : Theory.empty.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Theory.empty]
  · simp [Theory.empty]
  · intro op h; simp [Theory.empty] at h

/-- Convert the Bool-side `hasSchema = false` to set-membership form. -/
private theorem name_not_mem_of_hasSchema_false
    {T : Theory} {name : String}
    (h : T.hasSchema name = false) : name ∉ T.schemas.map (·.name) := by
  intro hmem
  obtain ⟨s', hs', hs'eq⟩ := List.mem_map.mp hmem
  unfold Theory.hasSchema at h
  rw [List.any_eq_false] at h
  have hbeq := h s' hs'
  -- hbeq : (s'.name == name) = false; hs'eq : s'.name = name
  rw [hs'eq] at hbeq
  simp at hbeq

/-- Convert the Bool-side `hasOperator = false` to set-membership form. -/
private theorem name_not_mem_of_hasOperator_false
    {T : Theory} {name : String}
    (h : T.hasOperator name = false) : name ∉ T.operators.map (·.name) := by
  intro hmem
  obtain ⟨op', hop', hop'eq⟩ := List.mem_map.mp hmem
  unfold Theory.hasOperator at h
  rw [List.any_eq_false] at h
  have hbeq := h op' hop'
  rw [hop'eq] at hbeq
  simp at hbeq

/-- `installSchema` preserves well-formedness. -/
theorem installSchema_wellFormed
    {T : Theory} (hT : T.WellFormed) {s : Schema}
    (hs : SchemaAdmissible T s) :
    (T.installSchema s hs).WellFormed := by
  obtain ⟨hSchemasNodup, hOpsNodup, hOpSchemaPresent⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · -- schema names remain distinct
    show ((s :: T.schemas).map (·.name)).Nodup
    rw [List.map_cons, List.nodup_cons]
    exact ⟨name_not_mem_of_hasSchema_false hs.name_fresh, hSchemasNodup⟩
  · -- operator names unchanged
    exact hOpsNodup
  · -- every operator's schema is still present (we only added a schema)
    intro op hop
    have hpres : T.hasSchema op.schema = true := hOpSchemaPresent op hop
    show ((s :: T.schemas).any (·.name == op.schema)) = true
    rw [List.any_cons, Bool.or_eq_true]
    exact Or.inr hpres

/-- `installOp` preserves well-formedness. -/
theorem installOp_wellFormed
    {T : Theory} (hT : T.WellFormed) {op : Operator}
    (ho : OperatorAdmissible T op) :
    (T.installOp op ho).WellFormed := by
  obtain ⟨hSchemasNodup, hOpsNodup, hOpSchemaPresent⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · -- schema names unchanged
    exact hSchemasNodup
  · -- operator names remain distinct
    show ((op :: T.operators).map (·.name)).Nodup
    rw [List.map_cons, List.nodup_cons]
    exact ⟨name_not_mem_of_hasOperator_false ho.name_fresh, hOpsNodup⟩
  · -- every operator's schema is present (schema list unchanged)
    intro op' hop'
    rcases List.mem_cons.mp hop' with rfl | hold
    · exact ho.schema_present
    · exact hOpSchemaPresent op' hold

end ClimbingCalc
