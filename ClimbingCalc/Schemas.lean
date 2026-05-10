import ClimbingCalc.Object

namespace ClimbingCalc

/-! ## The schemas

Each schema is a well-founded relation on `List Nat`. The relations
are defined via a *measure*: a function `List Nat → α` where `α`
carries a known well-founded order. `InvImage.wf` lifts the WF proof.
-/

/-- A schema's measure pulled from the head of an argument list
(falling back to 0 for the empty list). -/
def listHead0 : List Nat → Nat
  | []     => 0
  | x :: _ => x

/-- A schema's measure pulled from the first two args of an argument
list, padded with 0 for short lists. -/
def listLex2 : List Nat → Nat × Nat
  | []           => (0, 0)
  | [a]          => (a, 0)
  | a :: b :: _  => (a, b)

/-- The **structural** schema: an argument list is "smaller" than
another iff its first element is `Nat`-less. Admits operators that
recurse by decreasing the first argument (primitive recursion on the
first arg). -/
def structuralSchema : Schema where
  name := "structural"
  rel  := fun y x => listHead0 y < listHead0 x
  wf   := InvImage.wf listHead0 Nat.lt_wfRel.wf

/-- The **lex2** schema: lexicographic order on the first two args.
Admits operators whose recursive calls decrease lexicographically on
`(arg₀, arg₁)` — most famously Ackermann and Sudan, which call
themselves with `(n, _)` (same first arg, smaller second) and
`(n-1, _)` (smaller first arg). -/
def lex2Schema : Schema where
  name := "lex2"
  rel  := fun y x => Prod.Lex (· < ·) (· < ·) (listLex2 y) (listLex2 x)
  wf   := InvImage.wf listLex2 (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-! ## Decrease helpers

Small lemmas that produce accessibility witnesses for the common
shapes of recursive calls. Demos use these to keep step functions
readable.
-/

/-- For structural recursion: `n :: rest` decreases to `n' :: rest'`
when `n' < n` (rests are irrelevant to the measure). -/
theorem structuralSchema.dec_first
    {n' n : Nat} (rest' rest : List Nat) (h : n' < n) :
    structuralSchema.rel (n' :: rest') (n :: rest) := by
  show listHead0 _ < listHead0 _
  exact h

/-- For lex2: `(n, m) :: rest` decreases to `(n, m') :: rest'` when
`m' < m`. -/
theorem lex2Schema.dec_right
    {n m m' : Nat} (rest' rest : List Nat) (h : m' < m) :
    lex2Schema.rel (n :: m' :: rest') (n :: m :: rest) := by
  show Prod.Lex (· < ·) (· < ·) (n, m') (n, m)
  exact Prod.Lex.right _ h

/-- For lex2: `(n, m) :: rest` decreases to `(n', anything) :: rest'`
when `n' < n` (any second component is OK because lex order strictly
prefers the first). -/
theorem lex2Schema.dec_left
    {n' n m' m : Nat} (rest' rest : List Nat) (h : n' < n) :
    lex2Schema.rel (n' :: m' :: rest') (n :: m :: rest) := by
  show Prod.Lex (· < ·) (· < ·) (n', m') (n, m)
  exact Prod.Lex.left _ _ h

end ClimbingCalc
