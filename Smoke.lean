import ClimbingCalc

open ClimbingCalc

def label (k : String) (v : String) : IO Unit :=
  IO.println s!"  {k}: {v}"

def showApply (T : Theory) (name : String) (args : List Nat) : IO Unit :=
  label s!"{name}({args})" (toString (T.apply name args))

def main : IO Unit := do
  IO.println "================================================================"
  IO.println "climbing-calc — the calculator that climbs"
  IO.println "================================================================"
  IO.println ""

  IO.println "Scene 1: T_bare — empty theory"
  label "schemas" (toString (T_bare.schemas.map (·.name)))
  label "operators" (toString (T_bare.operators.map (·.name)))
  IO.println ""

  IO.println "Scene 2: T₀ — install structural schema"
  label "schemas" (toString (T₀.schemas.map (·.name)))
  label "operators" (toString (T₀.operators.map (·.name)))
  IO.println ""

  IO.println "Scene 3: T₁ — admit add, mul, exp under structural"
  label "operators" (toString (T₁.operators.map (·.name)))
  showApply T₁ "add" [2, 3]
  showApply T₁ "mul" [3, 4]
  showApply T₁ "exp" [2, 5]
  IO.println ""

  IO.println "Scene 4: T₂ — install lex2 schema"
  label "schemas" (toString (T₂.schemas.map (·.name)))
  IO.println ""

  IO.println "Scene 5: T_climbed — admit ackermann under lex2"
  label "operators" (toString (T_climbed.operators.map (·.name)))
  showApply T_climbed "ackermann" [0, 5]
  showApply T_climbed "ackermann" [1, 5]
  showApply T_climbed "ackermann" [2, 2]
  showApply T_climbed "ackermann" [3, 3]
  IO.println ""

  IO.println "Scene 6: refusal — wrong arity / unknown operator"
  showApply T_climbed "ackermann" [1]
  showApply T_climbed "nonexistent" [0]
  IO.println ""

  IO.println "Scene 7: the line crossed"
  showApply T_climbed "ackermann" [3, 7]
  showApply T_climbed "exp" [2, 10]
  IO.println "  ackermann(n, m) outgrows any fixed tower of exp; lex2 admits it."
