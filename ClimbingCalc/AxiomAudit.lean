import ClimbingCalc.Climb

/-!
# Axiom audit

Machine-witnesses that the climbing calculator's admission guarantees rest only on
the Lean kernel plus the standard classical axioms — crucially, **no
`Lean.ofReduceBool`**. That axiom is injected by `native_decide`, which trusts the
compiler instead of the kernel; this artifact's thesis is "the type checker *is* the
gate", so the proof surface must stay kernel-only. The behavioral demos use `#guard`
(a build-time evaluation, not a proof term), so they introduce no axioms here.

Each `#guard_msgs in #print axioms …` below pins the exact axiom footprint: if any
audited theorem ever acquires a new axiom (e.g. a stray `native_decide` creeps back
in), the build fails.
-/

namespace ClimbingCalc

/-- info: 'ClimbingCalc.empty_wellFormed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms empty_wellFormed

/-- info: 'ClimbingCalc.installSchema_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms installSchema_wellFormed

/-- info: 'ClimbingCalc.installOp_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms installOp_wellFormed

/-- info: 'ClimbingCalc.installSchema_preserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms installSchema_preserves

/-- info: 'ClimbingCalc.installOp_preserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms installOp_preserves

/-- info: 'ClimbingCalc.schema_admitted_means_wf' does not depend on any axioms -/
#guard_msgs in
#print axioms schema_admitted_means_wf

end ClimbingCalc
