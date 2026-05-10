import ClimbingCalc.Object

namespace ClimbingCalc

/-- The **structural** schema: recursion on a single `Nat` argument via
`<`. The well-foundedness proof is Lean's standard `Nat.lt_wfRel.wf`.

Operators admitted under this schema are those definable by primitive
recursion on a single argument: `add`, `mul`, `exp`, etc. -/
def structuralSchema : Schema where
  name    := "structural"
  Carrier := Nat
  rel     := (· < ·)
  wf      := Nat.lt_wfRel.wf

/-- The **lex2** schema: lexicographic order on pairs of naturals. The
well-foundedness proof is `Prod.lex_wf`, which lifts well-foundedness of
two relations to their lex product.

Ackermann is the canonical operator admitted here: the recursive calls
`A(n+1, m+1) ↝ A(n+1, m)` and `A(n+1, m+1) ↝ A(n, _)` both decrease
lexicographically on `(n, m)`, though neither decreases on a single
coordinate alone. -/
def lex2Schema : Schema where
  name    := "lex2"
  Carrier := Nat × Nat
  rel     := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).rel
  wf      := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

end ClimbingCalc
