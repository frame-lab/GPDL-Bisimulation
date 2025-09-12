universe u v w

section
variable
  {σ : Type u}
  {T : Type v}
  {X : Type w}
  [DecidableEq σ]

inductive BExp (T : Type v) : Type v
  | zero : BExp T
  | one : BExp T
  | prim : T → BExp T
  | and : BExp T → BExp T → BExp T
  | or : BExp T → BExp T → BExp T
  | not : BExp T → BExp T
deriving Repr

instance : Zero (BExp T) where
  zero := .zero

instance : One (BExp T) where
  one := .one

inductive Exp (σ : Type u) (T : Type v) : Type (max u v)
  | do : σ → Exp σ T
  | assert : BExp T → Exp σ T
  | seq : Exp σ T → Exp σ T → Exp σ T
  | if : BExp T → Exp σ T → Exp σ T → Exp σ T
  | while : BExp T → Exp σ T → Exp σ T
deriving Repr

def At (T : Type u) := T → Bool --!!!!!!!!!

def eval (v : At T) : BExp T → Bool
  | 0 => False
  | 1 => True
  | .prim t => v t
  | .and b c => eval v b && eval v c
  | .or b c => eval v b || eval v c
  | .not b =>  ! eval v b


inductive GuardedString (σ : Type u) (T : Type v)
  | final (state : At T) : GuardedString σ T
  | cons (state : At T) (action : σ) (next : GuardedString σ T) : GuardedString σ T

inductive two where
  | zero : two
  | one : two
deriving DecidableEq, BEq

def G (σ : Type u) (T : Type v) (X : Type w) := At T → (two ⊕ σ × X)

instance : Zero (two ⊕ σ × X) where
  zero := Sum.inl two.zero

instance : One (two ⊕ σ × X) where
  one := Sum.inl two.one

structure GCoalgebra (σ : Type u) (T : Type v) where
  states : Type w
  map : states → G σ T states

structure GAutomaton (σ : Type u) (T : Type v) where
  states : (Type w)
  map : states → G σ T states
  start : states

def accept (X : GAutomaton σ T) (s : X.states) : GuardedString σ T → Prop
  | .final α => X.map s α = 1
  | .cons α p x => ∃ (t : X.states), X.map s α = Sum.inr (p, t) ∧ accept X t x

def l (X : GAutomaton σ T) (s : X.states) := {α : GuardedString σ T // accept X s α}

def language (X : GAutomaton σ T) := l X X.start

instance : One (G σ T X) where
  one := fun _ ↦ 1

def uniform_continuation (X : GCoalgebra σ T)
  (Y : X.states → Bool)
  (h : G σ T X.states) : GCoalgebra σ T :=
  ⟨
    X.states,
    fun x α ↦
      if Y x then
        match X.map x α with
        | 1 => h α
        | _ => X.map x α
      else X.map x α
  ⟩

def coproduct (X Y : GCoalgebra σ T) : GCoalgebra σ T :=
  ⟨
    (X.states ⊕ Y.states),
    fun z α ↦ match z with
    | .inl x =>
      match (X.map x α) with
      | 0 => 0
      | 1 => 1
      | .inr (a, b) => .inr (a, .inl b)
    | .inr y =>
      match (Y.map y α) with
      | 0 => 0
      | 1 => 1
      | .inr (a, b) => .inr (a, .inr b)
  ⟩


def exp2coalgebra_aux : Exp σ T → ((X : GCoalgebra σ T) × G σ T X.states)--(two ⊕ σ × X.states))
  | .assert b =>
    ⟨
      ⟨Empty, fun _ ↦ 1⟩,
      fun α ↦ if eval α b then 1 else 0
    ⟩
  | .do p =>
    ⟨
      ⟨Unit, fun _ ↦ 1⟩,
      fun _ ↦ .inr (p, ())
    ⟩
  | .if b f g =>
    let ⟨cf, i_f⟩ := exp2coalgebra_aux f
    let ⟨cg, i_g⟩ := exp2coalgebra_aux g
    ⟨
      coproduct cf cg,
      fun α ↦
        if eval α b
        then
          match i_f α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, .inl b)
        else
          match i_g α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, .inr b)
    ⟩
  | .seq f g =>
    let ⟨cf, i_f⟩ := exp2coalgebra_aux f
    let ⟨cg, i_g⟩ := exp2coalgebra_aux g
    let i_e : G σ T (cf.states ⊕ cg.states) :=
      fun α ↦
        match i_f α with
        | 1 => match i_g α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, .inr b)
        | _ => match i_f α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, .inl b)
    ⟨
      uniform_continuation (coproduct cf cg)
        Sum.isLeft
        (
          fun α ↦ match i_g α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, .inr b)
        ),
        i_e
    ⟩
  | .while b f =>
    let ⟨cf, i_f⟩ := exp2coalgebra_aux f
    let i_e : G σ T cf.states :=
      fun α ↦
        if !(eval α b) then 1
        else
          match i_f α with
          | 1 => 0
          | _ => i_f α
    ⟨
      uniform_continuation cf
        (fun _ ↦ true) i_e,
      i_e
    ⟩

def exp2automaton (e : Exp σ T) : GAutomaton σ T :=
  let ⟨⟨s, m⟩, i_e⟩ := exp2coalgebra_aux e
  ⟨
    Unit ⊕ s,
    fun st => match st with
    | .inl () =>
      fun α ↦
      match i_e α with
      | 0 => 0
      | 1 => 1
      | .inr (a, b) => .inr (a, .inr b)
    | .inr a =>
      fun α ↦
      match m a α with
      | 0 => 0
      | 1 => 1
      | .inr (a, b) => .inr (a, .inr b),
    .inl ()
  ⟩
