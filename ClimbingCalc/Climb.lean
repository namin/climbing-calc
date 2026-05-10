import ClimbingCalc.Object

namespace ClimbingCalc

/-! ## The climb: admission API and structural theorems

A climb is a sequence of admissions. Each step:

* `installSchema` — append a schema (requires `SchemaAdmissible`: fresh
  name). Lean has already type-checked the schema's `WellFounded`
  proof at construction time.
* `installOp` — append an admitted operator (requires
  `OperatorAdmissible`: declared schema present in theory, name
  fresh). Lean has already type-checked the operator's step function
  against the schema's relation at construction time.

What v1 left informal is now type-level: `Operator S` literally
cannot be constructed without using `S.rel` in its step's type.
There is no separate "schema-relative termination certificate" to
verify after the fact.
-/

/-- Install a schema (prepend, with freshness check). -/
def Theory.installSchema (T : Theory) (s : Schema)
    (_ : SchemaAdmissible T s) : Theory :=
  { T with schemas := s :: T.schemas }

/-- Install an operator (prepend, with admissibility check). -/
def Theory.installOp (T : Theory) (ao : AdmittedOperator)
    (_ : OperatorAdmissible T ao) : Theory :=
  { T with operators := ao :: T.operators }

/-! ## Membership preservation -/

theorem installSchema_preserves (T : Theory) (s : Schema)
    (h : SchemaAdmissible T s) (s' : Schema) (h' : s' ∈ T.schemas) :
    s' ∈ (T.installSchema s h).schemas := by
  simp [Theory.installSchema, List.mem_cons]; exact Or.inr h'

theorem installOp_preserves (T : Theory) (ao : AdmittedOperator)
    (h : OperatorAdmissible T ao) (ao' : AdmittedOperator)
    (h' : ao' ∈ T.operators) :
    ao' ∈ (T.installOp ao h).operators := by
  simp [Theory.installOp, List.mem_cons]; exact Or.inr h'

/-- Any schema present in a theory has a constructive well-foundedness
proof. -/
theorem schema_admitted_means_wf (T : Theory) (s : Schema) (_ : s ∈ T.schemas) :
    WellFounded s.rel := s.wf

/-! ## Well-formed theories

A theory is well-formed when its schema names are pairwise distinct,
its operator names are pairwise distinct, and every operator's
declared schema is in the theory. The schema-presence clause is
propositional (`∈`), matching `OperatorAdmissible.schema_present`. -/

def Theory.WellFormed (T : Theory) : Prop :=
  (T.schemas.map (·.name)).Nodup ∧
  (T.operators.map (fun ao => ao.op.name)).Nodup ∧
  ∀ ao ∈ T.operators, ao.schema ∈ T.schemas

theorem empty_wellFormed : Theory.empty.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Theory.empty]
  · simp [Theory.empty]
  · intro ao h; simp [Theory.empty] at h

private theorem name_not_mem_of_hasSchema_false
    {T : Theory} {name : String}
    (h : T.hasSchema name = false) : name ∉ T.schemas.map (·.name) := by
  intro hmem
  obtain ⟨s', hs', hs'eq⟩ := List.mem_map.mp hmem
  unfold Theory.hasSchema at h
  rw [List.any_eq_false] at h
  have hbeq := h s' hs'
  rw [hs'eq] at hbeq
  simp at hbeq

private theorem name_not_mem_of_hasOperator_false
    {T : Theory} {name : String}
    (h : T.hasOperator name = false) :
    name ∉ T.operators.map (fun ao => ao.op.name) := by
  intro hmem
  obtain ⟨ao', hao', haoeq⟩ := List.mem_map.mp hmem
  unfold Theory.hasOperator at h
  rw [List.any_eq_false] at h
  have hbeq := h ao' hao'
  rw [haoeq] at hbeq
  simp at hbeq

theorem installSchema_wellFormed
    {T : Theory} (hT : T.WellFormed) {s : Schema}
    (hs : SchemaAdmissible T s) :
    (T.installSchema s hs).WellFormed := by
  obtain ⟨hSchemasNodup, hOpsNodup, hOpSchemaPresent⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · show ((s :: T.schemas).map (·.name)).Nodup
    rw [List.map_cons, List.nodup_cons]
    exact ⟨name_not_mem_of_hasSchema_false hs.name_fresh, hSchemasNodup⟩
  · exact hOpsNodup
  · intro ao hao
    have : ao.schema ∈ T.schemas := hOpSchemaPresent ao hao
    show ao.schema ∈ s :: T.schemas
    exact List.mem_cons_of_mem s this

theorem installOp_wellFormed
    {T : Theory} (hT : T.WellFormed) {ao : AdmittedOperator}
    (hAdm : OperatorAdmissible T ao) :
    (T.installOp ao hAdm).WellFormed := by
  obtain ⟨hSchemasNodup, hOpsNodup, hOpSchemaPresent⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · exact hSchemasNodup
  · show ((ao :: T.operators).map (fun a => a.op.name)).Nodup
    rw [List.map_cons, List.nodup_cons]
    exact ⟨name_not_mem_of_hasOperator_false hAdm.name_fresh, hOpsNodup⟩
  · intro ao' hao'
    rcases List.mem_cons.mp hao' with rfl | hold
    · exact hAdm.schema_present
    · exact hOpSchemaPresent ao' hold

end ClimbingCalc
