import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

import Batteries.Data.UnionFind

open Std Batteries

universe u v w

section
variable
  {σ : Type u}
  {t : Type v}
  [DecidableEq t]
  [DecidableEq σ]

namespace GKAT

inductive BExp (t : Type v)
  | zero : BExp t
  | one : BExp t
  | prim : t → BExp t
  | and : BExp t → BExp t → BExp t
  | or : BExp t → BExp t → BExp t
  | not : BExp t → BExp t
deriving Repr, DecidableEq

instance : Zero (BExp t) where
  zero := .zero

instance : One (BExp t) where
  one := .one

inductive Exp (σ : Type u) (t : Type v) : Type (max u v)
  | do : σ → Exp σ t
  | assert : BExp t → Exp σ t
  | seq : Exp σ t → Exp σ t → Exp σ t
  | if : BExp t → Exp σ t → Exp σ t → Exp σ t
  | while : BExp t → Exp σ t → Exp σ t
deriving Repr

def At (T : List t) := T.sublists

def eval (v : List t) : BExp t → Bool
  | 0 => false
  | 1 => true
  | .prim b =>
    b ∈ v
  | .and b c => eval v b && eval v c
  | .or b c => eval v b || eval v c
  | .not b =>  ! eval v b

inductive two where
  | zero : two
  | one : two
deriving DecidableEq, BEq

def G (σ : Type u) (t : Type v) (X : Type w) := List t → (two ⊕ σ × X)

instance : Zero (two ⊕ σ × X) where
  zero := Sum.inl two.zero

instance : One (two ⊕ σ × X) where
  one := Sum.inl two.one

structure GCoalgebra (σ : Type u) (t : Type v) where
  states : Nat
  map : Fin states → G σ t (Fin states)

structure GAutomaton (σ : Type u) (t : Type v) where
  states : Nat
  map : Fin states → G σ t (Fin states)
  start : Fin states

instance : One (G σ t X) where
  one := fun _ ↦ 1

def uniform_continuation (X : GCoalgebra σ t)
  (Y : Fin X.states → Bool)
  (h : G σ t (Fin X.states)) : GCoalgebra σ t :=
  ⟨
    X.states,
    fun x α ↦
      if (Y x) ∧ (X.map x α = 1)
      then h α
      else X.map x α
  ⟩

def coproduct (X Y : GCoalgebra σ t) : GCoalgebra σ t :=
  ⟨
    (X.states + Y.states),
    fun z α ↦
      if h : z < X.states
      then
        match (X.map ⟨z, h⟩ α) with
        | 0 => 0
        | 1 => 1
        | .inr (a, b) => .inr (a, ⟨b, Nat.lt_add_right Y.states b.isLt⟩)
      else
        match (Y.map (⟨(z - X.states), by
          apply Nat.sub_lt_right_of_lt_add (le_of_not_gt h)
          rw [Nat.add_comm Y.states X.states]
          exact z.isLt
        ⟩ : Fin (Y.states)) α) with
        | 0 => 0
        | 1 => 1
        | .inr (a, b) => .inr (a, ⟨X.states + b, Nat.add_lt_add_left b.isLt X.states⟩)
  ⟩


def exp2coalgebra_aux : Exp σ t → ((X : GCoalgebra σ t) × G σ t (Fin X.states))--(two ⊕ σ × X.states))
  | .assert b =>
    ⟨
      ⟨0, fun ⟨n, lt⟩ => False.elim ((Nat.not_lt_zero n) lt)⟩,
      fun α ↦ if eval α b then 1 else 0
    ⟩
  | .do p =>
    ⟨
      ⟨1, fun _ ↦ 1⟩,
      fun _ ↦ .inr (p, ⟨0, Nat.zero_lt_one⟩)
    ⟩
  | .if b f g =>
    let ⟨⟨Xf, δf⟩, i_f⟩ := exp2coalgebra_aux f
    let ⟨⟨Xg, δg⟩, i_g⟩ := exp2coalgebra_aux g
    ⟨
      coproduct ⟨Xf, δf⟩ ⟨Xg, δg⟩,
      fun α ↦
        if eval α b
        then
          match i_f α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, ⟨b, Nat.lt_add_right Xg b.isLt⟩)
        else
          match i_g α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, ⟨Xf + b, Nat.add_lt_add_left b.isLt Xf⟩)
    ⟩
  | .seq f g =>
    let ⟨⟨Xf, δf⟩, i_f⟩ := exp2coalgebra_aux f
    let ⟨⟨Xg, δg⟩, i_g⟩ := exp2coalgebra_aux g
    ⟨
      uniform_continuation (coproduct ⟨Xf, δf⟩ ⟨Xg, δg⟩)
        (· < Xf)
        (
          fun α ↦ match i_g α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, ⟨Xf + b, by simp [coproduct]⟩)
        ),
        fun α ↦
        match i_f α with
        | 1 => match i_g α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, ⟨Xf + b, Nat.add_lt_add_left b.isLt Xf⟩)
        | _ => match i_f α with
          | 0 => 0
          | 1 => 1
          | .inr (a, b) => .inr (a, ⟨b, Nat.lt_add_right Xg b.isLt⟩)
    ⟩
  | .while b f =>
    let ⟨⟨Xf, δf⟩, i_f⟩ := exp2coalgebra_aux f
    let i_e : G σ t (Fin Xf) :=
      fun α ↦
        if !(eval α b) then 1
        else
          match i_f α with
          | 1 => 0
          | _ => i_f α
    ⟨
      uniform_continuation ⟨Xf, δf⟩
        (· < Xf) i_e,
      i_e
    ⟩

def exp2automaton (e : Exp σ t) : GAutomaton σ t :=
  let ⟨⟨s, m⟩, i_e⟩ := exp2coalgebra_aux e
  ⟨
    s + 1,
    fun st => match st with
    | 0 =>
      fun α ↦
      match i_e α with
      | 0 => 0
      | 1 => 1
      | .inr (a, b) => .inr (a, ⟨b + 1, Nat.add_lt_add_right b.isLt 1⟩)
    | ⟨n + 1, h⟩ =>
      fun α ↦
      match m ⟨n, Nat.succ_lt_succ_iff.mp h⟩ α with
      | 0 => 0
      | 1 => 1
      | .inr (a, b) => .inr (a, ⟨b + 1, Nat.add_lt_add_right b.isLt 1⟩),
    ⟨0, Nat.zero_lt_succ s⟩
  ⟩

def accepting {X : GCoalgebra σ t} (T : List t) (s : Fin X.states): Bool :=
  List.any (At T) (fun α ↦ X.map s α = 1)

def not_dead_states (X : GCoalgebra σ t) (T : List t) : Vector Bool X.states :=
  let rec accepting_in_steps (N : Nat) : Vector Bool X.states :=
    match N with
    | 0 => Vector.map (accepting T) (Vector.finRange X.states)
    | n + 1 =>
      (Vector.finRange X.states).map (fun x ↦
        (accepting_in_steps n).get x ||
        List.any (At T) (fun α ↦
          match (X.map x α) with
          | .inr (_, b) => (accepting_in_steps n).get b
          | _ => false ))
  accepting_in_steps X.states

def normalize (T : List t) (X : GAutomaton σ t) : GAutomaton σ t :=
  let not_dead_states_x := not_dead_states ⟨X.states, X.map⟩ T
  ⟨
    X.states,
    fun x α ↦
      match X.map x α with
      | .inr (_, b) =>
          if (not_dead_states_x.get b) then X.map x α else 0
      | _ => X.map x α,
    X.start
  ⟩

def inner_loop_aux (X Y : GAutomaton σ t) (x : Fin X.states) (y : Fin Y.states)
      (A : List (List t)) (Q : Queue (Fin X.states × Fin Y.states)) :=
      match A with
      | [] => (Q, true)
      | α::A' =>
        match X.map x α, Y.map y α with
        | .inl b1, .inl b2 =>
          if b1 = b2
          then inner_loop_aux X Y x y A' Q
          else (Q, false)
        | .inr (p1, x'), .inr (p2, y') =>
          if p1 = p2
          then inner_loop_aux X Y x y A' (Q.enqueue (x', y'))
          else (Queue.empty, false)
        | _, _ => (Queue.empty, false)

def inner_loop (T : List t)
                (X Y : GAutomaton σ t)
                (x : Fin X.states) (y : Fin Y.states)
                (Q : Queue (Fin X.states × Fin Y.states))
                : Queue (Fin X.states × Fin Y.states) × Bool :=
    inner_loop_aux X Y x y (At T) Q

partial def outer_loop (T : List t)
                (X Y : GAutomaton σ t)
                (Q : Queue (Fin X.states × Fin Y.states))
                (UF : UnionFind) : Bool :=
    match Q.dequeue? with
    | none => true
    | some ⟨⟨x, y⟩, Q'⟩ =>
      let ⟨UF', eq⟩ := UF.checkEquiv! x (y + X.states)
      if eq then
        outer_loop T X Y Q' UF'
      else
        let ⟨Q'', B'⟩ := inner_loop T X Y x y Q'
        if B'
        then outer_loop T X Y Q'' (UF'.union! x (y + X.states))
        else false

def bisimulation (T : List t) (X Y : GAutomaton σ t) : Bool :=
  outer_loop T X Y
    (Queue.enqueue (X.start, Y.start) Queue.empty)
    (UnionFind.mkEmpty (X.states + Y.states))

def atomic_tests_bexp : BExp t → List t
  | .zero => []
  | .one => []
  | .prim b => [b]
  | .and b c => List.union (atomic_tests_bexp b) (atomic_tests_bexp c)
  | .or b c => List.union (atomic_tests_bexp b) (atomic_tests_bexp c)
  | .not b => atomic_tests_bexp b

def atomic_tests : Exp σ t -> List t
  | .do _ => []
  | .assert b => atomic_tests_bexp b
  | .seq f g => List.union (atomic_tests f) (atomic_tests g)
  | .if b f g => List.union (atomic_tests_bexp b) (List.union (atomic_tests f) (atomic_tests g))
  | .while b f => List.union (atomic_tests_bexp b) (atomic_tests f)

def check_equivalence (e1 e2 : Exp σ t) : Bool :=
  let T : List t := List.union (atomic_tests e1) (atomic_tests e2)
  bisimulation T
    (normalize T (exp2automaton e1))
    (normalize T (exp2automaton e2))



#eval check_equivalence
  (.do 'e' : Exp Char Char)
  (.seq  (.assert 1) (.do 'e' ): Exp Char Char)

#eval check_equivalence
  (.if (.prim 'b')
    (.do 'e') (.do 'f'))
  (.if (.not (.prim 'b'))
    (.do 'f') (.do 'e'))

#eval check_equivalence
  (.while (.prim 'b')
    (.do 'e'))
  (.while (.not (.prim 'b'))
    (.do 'e'))

#eval check_equivalence
  (.if (.prim 'b')
    (.if (.prim 'c')
      (.do 'f')
      (.do 'g'))
    (.do 'g'))
  (.if (.prim 'c')
    (.if (.prim 'b')
      (.do 'f')
      (.do 'g'))
    (.do 'g'))

#eval check_equivalence
  (.if (.prim 'b')
    (.if (.prim 'c')
      (.do 'f')
      (.do 'g'))
    (.do 'g'))
  (.if (.and (.prim 'b') (.prim 'c'))
    (.do 'f')
    (.do 'g'))

end GKAT
