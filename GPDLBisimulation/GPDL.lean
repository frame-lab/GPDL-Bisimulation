import GPDLBisimulation.GKAT

section
variable
  {σ : Type u}
  {t : Type v}
  {T : List t}
  [DecidableEq t]
  [DecidableEq σ]

inductive Formula (σ : Type u) (T : List t)
  | atom_prop : {p // p ∈ T} → Formula σ T
  | top : Formula σ T
  | neg : Formula σ T → Formula σ T
  | and : Formula σ T → Formula σ T → Formula σ T
  | diamond : GKAT.Exp σ T → Formula σ T → Formula σ T

def Formula.bot : Formula σ T := Formula.neg Formula.top

def Formula.or : Formula σ T → Formula σ T → Formula σ T
  | φ₁, φ₂ => .neg (.and (.neg φ₁) (.neg φ₂))

def Formula.impl : Formula σ T → Formula σ T → Formula σ T
  | φ₁, φ₂ => .neg (.and φ₁ (.neg φ₂))

def formula.box : GKAT.Exp σ T → Formula σ T → Formula σ T
  | π, φ => .neg (.diamond π (.neg φ))

structure Model (σ : Type u) (T : List t) where
  W : Type w
  R : σ → W → W
  V : {p // p ∈ T} → W → Bool
