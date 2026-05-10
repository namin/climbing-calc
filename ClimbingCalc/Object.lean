namespace ClimbingCalc

/--
A **schema** is a named well-founded relation. The kernel admits a schema
iff Lean accepts the `wf` field as a `WellFounded` value — i.e. there's a
constructive proof that `rel` is well-founded.

Bogus schemas (relations claimed well-founded without a real proof) cannot
be admitted without `sorry`, which closes the disaster demo at the type
level: there is no way to install a schema without the kernel having
already type-checked its well-foundedness certificate.
-/
structure Schema where
  name    : String
  Carrier : Type
  rel     : Carrier → Carrier → Prop
  wf      : WellFounded rel

/--
An **admitted operator** carries its computable Lean function (`fn`) and a
declaration of which schema admitted it. The Lean type-checker has already
accepted `fn` as total; the `schema` field is metadata recording the climb
rung at which the operator entered.
-/
structure Operator where
  name   : String
  arity  : Nat
  schema : String
  fn     : List Nat → Nat

/-- A **theory**: schemas and operators admitted so far. -/
structure Theory where
  schemas   : List Schema
  operators : List Operator

/-- The empty theory: nothing admitted. -/
def Theory.empty : Theory := ⟨[], []⟩

/-- Apply an operator by name. Returns `none` if the operator is unknown
or the argument count doesn't match its declared arity. -/
def Theory.apply (T : Theory) (name : String) (args : List Nat) : Option Nat :=
  match T.operators.find? (·.name == name) with
  | none    => none
  | some op =>
    if op.arity == args.length then some (op.fn args) else none

/-- Whether a schema name is in the theory. -/
def Theory.hasSchema (T : Theory) (name : String) : Bool :=
  T.schemas.any (·.name == name)

/-- Whether an operator name is in the theory. -/
def Theory.hasOperator (T : Theory) (name : String) : Bool :=
  T.operators.any (·.name == name)

end ClimbingCalc
