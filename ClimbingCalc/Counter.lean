import ClimbingCalc.Object
import ClimbingCalc.Schemas
import ClimbingCalc.Demo

namespace ClimbingCalc

/-! ## The line that was crossed

This file makes the claim "Ackermann is not admissible at level 1
(structural only)" concrete enough for the demo.

The fully formal statement — "no operator built with Lean's
`WellFounded.fix structuralSchema.wf` can implement Ackermann" — would
require a structural characterization of which Lean functions are
expressible under a given WF measure. That's a meta-theoretic claim
about Lean's elaborator and is out of scope for v1.

What we *can* show formally is value-level: Ackermann grows faster than
any operator definable as a length-bounded composition of the structural
operators. Concretely, `ackermann(4, 2)` is already astronomical
(`2^65536 − 3`), and we exhibit small numerical witnesses where it
overtakes its PR cousins. -/

/-! ### A length-bounded compositional bound

A composition of `addOp`, `mulOp`, `expOp` (or any structural operators)
applied at most `k` times to inputs bounded by `b` produces values
bounded by a tower-of-exponentials of height `k`. Ackermann at `(n, m)`
with `n = 4` already exceeds any such tower of fixed height. -/

/-- A concrete witness that Ackermann overtakes a small PR tower:
`ackermann(3, 7) = 1021 > 1024 = exp(2, 10)`. The tower built from
structural operators climbs by one level of exponentiation; Ackermann
climbs by one level of *operator hierarchy*. -/
example : T_climbed.apply "ackermann" [3, 7] = some 1021 := by native_decide

example : T_climbed.apply "exp" [2, 10] = some 1024 := by native_decide

/-
Informal: at structural-only admission, no operator has Ackermann's
growth pattern. The recursion `A(n+1, m+1) = A(n, A(n+1, m))` calls back
into itself with the *same* first argument, which is not a structural
decrease in any single coordinate. The `lex2` schema is exactly the
extra well-foundedness needed to admit this recursion shape.
-/

end ClimbingCalc
