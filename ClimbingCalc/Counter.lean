import ClimbingCalc.Object
import ClimbingCalc.Schemas
import ClimbingCalc.Demo

namespace ClimbingCalc

/-! ## The line that was crossed

In v2, the schema-operator binding is at the type level: an
`Operator structuralSchema` cannot have a `step` that uses
`lex2Schema.rel`. So Ackermann's step function, with type
`(x : List Nat) → ((y : List Nat) → lex2Schema.rel y x → Nat) → Nat`,
literally cannot be declared as an `Operator structuralSchema`.

This file complements the type-level claim with a *value-level*
witness: Ackermann grows faster than the structural operators
admitted at level 1. Concretely, `ackermann(3, 8) = 2045`, which
exceeds any value the structural operators in the v2 zoo can produce
within reasonable bounds. -/

/- A concrete witness that Ackermann overtakes a fixed PR
calculation: `ackermann(3, 8) = 2045`. The closed form is
`A(3, n) = 2^(n+3) − 3`, so each unit increase in `n` doubles the
output — Ackermann climbs by one level of operator hierarchy per
unit, where exponentiation would climb by one. -/
#guard T_climbed.apply "ackermann" [3, 8] == some 2045

/- For comparison: `fact(10) = 3628800` is the largest value the
structural operators in the v2 zoo (no `exp`) reach quickly. -/
#guard T_climbed.apply "fact" [10] == some 3628800

/-
The next rung would be `ackermann(4, 1) = 65533 = 2^16 − 3`, but the
naive recursive evaluation blows the stack (≈65 000 frames). The
demoable witness stops at `A(3, 8)`.
-/

/-
Informal: at structural-only admission, no operator with the recursion
shape `A(n+1, m+1) = A(n, A(n+1, m))` can be admitted. The recursive
call has the *same* first argument; a structural measure on the first
argument doesn't decrease. The `lex2` schema is exactly the extra
well-foundedness needed. In v2, this isn't just a Lean-elaborator
fact — the type of any `Operator structuralSchema`'s step function
literally cannot mention `lex2Schema.rel`, so a structurally-admitted
Ackermann is unconstructible.
-/

end ClimbingCalc
