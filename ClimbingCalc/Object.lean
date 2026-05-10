namespace ClimbingCalc

/-! ## v2: schema-indexed step functions

The substrate is *computation*: total `List Nat → Nat` functions
built by well-founded recursion on a schema's relation. The key
type-level constraint:

* a `Schema` is a well-founded relation on `List Nat` together with a
  Lean `WellFounded` proof;
* an `Operator S` carries a `step` function whose type **literally
  mentions `S.rel`** as the decreasing measure;
* its computable `fn` is `S.wf.fix step` — Lean's well-founded fix.

You cannot construct an `Operator S` whose `step` doesn't use `S.rel`
in the accessibility witnesses for its recursive calls. This is the
type-level binding between operator and schema that v1's
`fn : List Nat → Nat` lacked. -/

/-- A **schema** is a named well-founded relation on argument lists. -/
structure Schema where
  name : String
  rel  : List Nat → List Nat → Prop
  wf   : WellFounded rel

/-- An **operator admitted under schema `S`**. The `step` function's
type carries the schema-binding: every recursive call goes through
the second argument `rec`, which requires an accessibility witness in
`S.rel`. The kernel admits iff Lean type-checks this. -/
structure Operator (S : Schema) where
  name  : String
  arity : Nat
  step  : (x : List Nat) → ((y : List Nat) → S.rel y x → Nat) → Nat

/-- The computable function induced by an operator, via Lean's
`WellFounded.fix` on the schema's relation. -/
def Operator.fn {S : Schema} (op : Operator S) (args : List Nat) : Nat :=
  S.wf.fix op.step args

/-- A theory's operator list is heterogeneous: each entry pairs a
schema with an operator typed against it. -/
structure AdmittedOperator where
  schema : Schema
  op     : Operator schema

/-- A theory: schemas and operators admitted so far. -/
structure Theory where
  schemas   : List Schema
  operators : List AdmittedOperator

def Theory.empty : Theory := ⟨[], []⟩

/-- Apply an operator by name. Returns `none` if the operator is
unknown or arity doesn't match. -/
def Theory.apply (T : Theory) (name : String) (args : List Nat) : Option Nat :=
  match T.operators.find? (fun ao => ao.op.name == name) with
  | none    => none
  | some ao =>
    if ao.op.arity == args.length then some (ao.op.fn args) else none

/-- Whether a schema name is in the theory. -/
def Theory.hasSchema (T : Theory) (name : String) : Bool :=
  T.schemas.any (·.name == name)

/-- Whether an operator name is in the theory. -/
def Theory.hasOperator (T : Theory) (name : String) : Bool :=
  T.operators.any (fun ao => ao.op.name == name)

/-! ## Admissibility preconditions

* `SchemaAdmissible`: schema name must be fresh.
* `OperatorAdmissible`: the declared schema must be in the theory
  (propositional list membership), and the operator name must be
  fresh. The schema-membership is propositional rather than a
  Bool-name-check because we want the *same Schema value* the
  operator's `step` is typed against — not just any schema with the
  same name.
-/

/-- Precondition for installing a schema: name must be fresh. -/
structure SchemaAdmissible (T : Theory) (s : Schema) : Prop where
  name_fresh : T.hasSchema s.name = false

/-- Precondition for installing an operator: declared schema must be
present (as a Schema value, not just by name), and the operator's
name must be fresh. -/
structure OperatorAdmissible (T : Theory) (ao : AdmittedOperator) : Prop where
  schema_present : ao.schema ∈ T.schemas
  name_fresh     : T.hasOperator ao.op.name = false

end ClimbingCalc
