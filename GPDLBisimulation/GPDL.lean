import GPDLBisimulation.GKAT

section
variable
  {σ : Type u}
  {t : Type v}
  [DecidableEq σ]
  [BEq σ]
  [BEq t]

inductive Formula (σ : Type u) (t : Type v)
  | atom_prop : t → Formula σ t
  | top : Formula σ t
  | neg : Formula σ t → Formula σ t
  | and : Formula σ t → Formula σ t → Formula σ t
  | diamond : GKAT.Exp σ t → Formula σ t → Formula σ t
deriving BEq

def Formula.bot : Formula σ t := Formula.neg Formula.top

def Formula.or : Formula σ t → Formula σ t → Formula σ t
  | φ₁, φ₂ => .neg (.and (.neg φ₁) (.neg φ₂))

def Formula.impl : Formula σ t → Formula σ t → Formula σ t
  | φ₁, φ₂ => .neg (.and φ₁ (.neg φ₂))

def Formula.box : GKAT.Exp σ t → Formula σ t → Formula σ t
  | π, φ => .neg (.diamond π (.neg φ))

structure Model (σ : Type u) (t : Type v) where
  W : Type w
  Ws : List W
  R : σ → W → Option W
  V : t → List W

def bexp2formula : GKAT.BExp t → Formula σ t
  | .one => .top
  | .prim b => .atom_prop b
  | .and b c => .and (bexp2formula b) (bexp2formula c)
  | .not b => .neg (bexp2formula b)

def PrefFormula (σ : Type u) (t : Type v) := List σ × Formula σ t

def findContra : List (PrefFormula σ t) → Bool
  | [] => False
  | (s, f) :: fs =>
    List.any fs (fun (s', f') =>
      s == s' && (f == .neg f' || f' == .neg f)) || findContra fs

def complexityB : GKAT.BExp t → Nat
  | .and b c => (complexityB b) + (complexityB c) + 1
  | .not b => (complexityB b) + 1
  | _ => 1

def complexityProg : GKAT.Exp σ t → Nat
  | .do _ => 1
  | .assert b => complexityB b + 1
  | .seq f g => complexityProg f + complexityProg g + 1
  | .if b f g => complexityB b + complexityProg f + complexityProg g + 1
  | .while b f => complexityB b + complexityProg f

def complexity : Formula σ t → Nat
  | .neg f => complexity f + 1
  | .and f1 f2 => complexity f1 + complexity f2 + 1
  | .diamond (p) f => complexityProg p + complexity f
  | _ => 1

omit [BEq t] in
theorem compBeqF {σ : Type u} (b : GKAT.BExp t) : complexityB b = complexity (bexp2formula b : Formula σ t) := by
  induction b <;> simp [bexp2formula, complexityB, complexity]
  case and b c ih1 ih2 => rw [ih1, ih2]
  case not b ih => rw [ih]

omit [BEq σ] [BEq t] in
theorem complexityBPos (b : GKAT.BExp t) : 0 < complexityB b := by
  induction b <;> rw [complexityB] <;> grind

omit [BEq σ] [BEq t] [DecidableEq σ] in
theorem complexityProgPos (p : GKAT.Exp σ t) : 0 < complexityProg p := by
  induction p <;> rw [complexityProg] <;> try grind

omit [BEq σ] [BEq t] [DecidableEq σ] in
theorem complexityPos (f : Formula σ t) : 0 < complexity f := by
  induction f <;> rw [complexity] <;> grind

def complexityP : PrefFormula σ t → Nat
  | (_, f) => complexity f

def closed_tableau
  (exp : List (PrefFormula σ t))
  (unexp : List (PrefFormula σ t)) : Bool :=
  if findContra (exp ++ unexp) then true else
  match unexp with
  | [] => false
  | (s, f) :: fs => match f with
    | .neg (.neg f') =>
      have : complexityP (s, f') < complexityP (s, f'.neg.neg) := by
        simp [complexityP, complexity]; grind
      closed_tableau ((s, f) :: exp) ((s,f') :: fs)

    | .and f1 f2 =>
      have : complexityP (s, f1) + (complexityP (s, f2) + (List.map complexityP fs).sum) < complexityP (s, f1.and f2) + (List.map complexityP fs).sum := by
        simp [complexityP, complexity]; grind
      closed_tableau ((s, f) :: exp) ((s,f1) :: (s, f2) :: fs)

    | .neg (.and f1 f2) =>
      have : complexityP (s, f1.neg) < complexityP (s, (f1.and f2).neg) := by
        simp [complexityP, complexity]; grind
      have : complexityP (s, f2.neg) < complexityP (s, (f1.and f2).neg) := by
        simp [complexityP, complexity]; grind
      closed_tableau ((s, f) :: exp) ((s, .neg f1) :: fs) &&
      closed_tableau ((s, f) :: exp) ((s, .neg f2) :: fs)

    | .diamond (.do p) f' =>
      have : complexityP (p :: s, f') < complexityP (s, Formula.diamond (GKAT.Exp.do p) f') := by
        simp [complexityP, complexity]; exact complexityProgPos (GKAT.Exp.do p)
      closed_tableau ((s, f) :: exp) (((p :: s), f') :: fs)

    | .neg (.diamond (.do p) f') =>
      have : complexityP (p :: s, f'.neg) < complexityP (s, (Formula.diamond (GKAT.Exp.do p) f').neg) := by
        simp [complexityP, complexity]; exact complexityProgPos (GKAT.Exp.do p)
      if (exp ++ unexp).any (fun (s', _) => s' == (p :: s))
      then closed_tableau ((s, f) :: exp) (((p :: s), .neg f') :: fs)
      else closed_tableau ((s, f) :: exp) fs

    | .diamond (.assert b) f' =>
      have : complexityP (s, bexp2formula b) + (complexityP (s, f') + (List.map complexityP fs).sum) <
        complexityP (s, Formula.diamond (GKAT.Exp.assert b) f') + (List.map complexityP fs).sum := by
        simp [complexityP, complexity, complexityProg]; rw [compBeqF b, Nat.add_assoc]
        simp [Nat.add_comm (complexity (bexp2formula b)) 1]; exact lt_one_add (complexity (bexp2formula b))
      closed_tableau ((s, f) :: exp) ((s, bexp2formula b) :: (s, f') :: fs)

    | .neg (.diamond (.assert b) f') =>
      have : complexityP (s, (bexp2formula b).neg) < complexityP (s, (Formula.diamond (GKAT.Exp.assert b) f').neg) := by
        simp [complexityP, complexity, complexityProg]; rw [compBeqF b]
        apply Nat.lt_add_right (complexity f'); exact lt_add_one (complexity (bexp2formula b))
      have : complexityP (s, f'.neg) < complexityP (s, (Formula.diamond (GKAT.Exp.assert b) f').neg) := by
        simp [complexityP, complexity]; exact complexityProgPos (GKAT.Exp.assert b)
      closed_tableau ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: fs) &&
      closed_tableau ((s, f) :: exp) ((s, .neg f') :: fs)

    | .diamond (.seq p1 p2) f' =>
      have : complexityP (s, Formula.diamond p1 (Formula.diamond p2 f')) < complexityP (s, Formula.diamond (p1.seq p2) f') := by
        simp [complexityP, complexity, complexityProg]; grind
      closed_tableau ((s, f) :: exp) ((s, .diamond p1 (.diamond p2 f')) :: fs)

    | .neg (.diamond (.seq p1 p2) f') =>
      have : complexityP (s, (Formula.diamond p1 (Formula.diamond p2 f')).neg) <
      complexityP (s, (Formula.diamond (p1.seq p2) f').neg) := by
        simp [complexityP, complexity, complexityProg]; grind
      closed_tableau ((s, f) :: exp) ((s, .neg (.diamond p1 (.diamond p2 f'))) :: fs)

    | .diamond (.if b p1 p2) f' =>
      have : complexityP (s, bexp2formula b) + (complexityP (s, Formula.diamond p1 f') + (List.map complexityP fs).sum) <
        complexityP (s, Formula.diamond (GKAT.Exp.if b p1 p2) f') + (List.map complexityP fs).sum := by
        simp [complexityP, complexity, complexityProg]; rw [compBeqF b, ←Nat.add_assoc, ←Nat.add_assoc]
        apply Nat.add_lt_add_right; apply Nat.add_lt_add_right; rw [Nat.add_assoc, Nat.add_assoc]
        apply Nat.add_lt_add_left; apply Nat.lt_add_of_pos_right; exact Nat.zero_lt_succ (complexityProg p2)
      have : complexityP (s, (bexp2formula b).neg) + (complexityP (s, Formula.diamond p2 f') + (List.map complexityP fs).sum) <
        complexityP (s, Formula.diamond (GKAT.Exp.if b p1 p2) f') + (List.map complexityP fs).sum := by
        simp [complexityP, complexity, complexityProg]; rw [compBeqF b, ←Nat.add_assoc, ←Nat.add_assoc]
        apply Nat.add_lt_add_right; apply Nat.add_lt_add_right; rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
        apply Nat.add_lt_add_left; rw [Nat.add_comm]; apply Nat.lt_add_of_pos_left; exact complexityProgPos p1
      closed_tableau ((s, f) :: exp) (((s, bexp2formula b)) :: (s, .diamond p1 f') :: fs) &&
      closed_tableau ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: (s, .diamond p2 f') :: fs)

    | .neg (.diamond (.if b p1 p2) f') =>
      have : complexityP (s, bexp2formula b) + (complexityP (s, (Formula.diamond p1 f').neg) + (List.map complexityP fs).sum) <
      complexityP (s, (Formula.diamond (GKAT.Exp.if b p1 p2) f').neg) + (List.map complexityP fs).sum := by
        simp [complexityP, complexity, complexityProg]; rw [compBeqF b, ←Nat.add_assoc]; apply Nat.add_lt_add_right
        rw [←Nat.add_assoc, ←Nat.add_assoc]; apply Nat.add_lt_add_right; apply Nat.add_lt_add_right
        rw [Nat.add_assoc, Nat.add_assoc]; apply Nat.add_lt_add_left
        apply Nat.lt_add_of_pos_right; exact Nat.zero_lt_succ (complexityProg p2)
      have : complexityP (s, (bexp2formula b).neg) + (complexityP (s, (Formula.diamond p2 f').neg) + (List.map complexityP fs).sum) <
      complexityP (s, (Formula.diamond (GKAT.Exp.if b p1 p2) f').neg) + (List.map complexityP fs).sum := by
        simp [complexityP, complexity, complexityProg]; rw [compBeqF b, ←Nat.add_assoc]
        apply Nat.add_lt_add_right; rw [←Nat.add_assoc, ←Nat.add_assoc]; apply Nat.add_lt_add_right
        apply Nat.add_lt_add_right; rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]; apply Nat.add_lt_add_left
        rw [Nat.add_comm, Nat.add_comm (complexityProg p1) (complexityProg p2 + 1)]
        apply Nat.lt_add_of_pos_right; exact complexityProgPos p1
      closed_tableau ((s, f) :: exp) (((s, bexp2formula b)) :: (s, .neg (.diamond p1 f')) :: fs) &&
      closed_tableau ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: (s, .neg (.diamond p2 f')) :: fs)

    | f' =>
      have : 0 < complexityP (s, f') := complexityPos f'
      closed_tableau ((s, f) :: exp) fs
termination_by List.sum (List.map complexityP unexp)


partial def closed_tableau'
  (exp : List (PrefFormula σ t))
  (unexp : List (PrefFormula σ t)) : Bool :=
  if findContra (exp ++ unexp) then true else
  match unexp with
  | (s, f) :: fs => match f with
    | .neg (.neg f') =>
      closed_tableau' ((s, f) :: exp) ((s,f') :: fs)

    | .and f1 f2 =>
      closed_tableau' ((s, f) :: exp) ((s,f1) :: (s, f2) :: fs)

    | .neg (.and f1 f2) =>
      closed_tableau' ((s, f) :: exp) ((s, .neg f1) :: fs) &&
      closed_tableau' ((s, f) :: exp) ((s, .neg f2) :: fs)

    | .diamond (.seq p1 p2) f' =>
      closed_tableau' ((s, f) :: exp) ((s, .diamond p1 (.diamond p2 f')) :: fs)

    | .neg (.diamond (.seq p1 p2) f') =>
      closed_tableau' ((s, f) :: exp) ((s, .neg (.diamond p1 (.diamond p2 f'))) :: fs)

    | .diamond (.assert b) f' =>
      closed_tableau' ((s, f) :: exp) ((s, bexp2formula b) :: (s, f') :: fs)

    | .neg (.diamond (.assert b) f') =>
      closed_tableau' ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: fs) &&
      closed_tableau' ((s, f) :: exp) ((s, .neg f') :: fs)

    | .diamond (.do p) f' =>
      let x : List (PrefFormula σ t) :=
        exp.filterMap
          (fun pf => match pf with
            | (s', .neg (.diamond (.do p') f'')) =>
              if (s' == s) && (p' == p)
              then some ((p :: s), .neg f'')
              else none
            | _ => none)
      closed_tableau' ((s, f) :: exp) (((p :: s), f') :: (x ++ fs))

    --!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    -- (p :: s) já presente no ramo
    | .neg (.diamond (.do p) f') =>
      if (exp ++ unexp).any (fun (s', _) => s' == (p :: s))
      then closed_tableau' ((s, f) :: exp) (((p :: s), .neg f') :: fs)
      else closed_tableau' ((s, f) :: exp) fs
    --!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    | .diamond (.if b p1 p2) f' =>
      closed_tableau' ((s, f) :: exp) (((s, bexp2formula b)) :: (s, .diamond p1 f') :: fs) &&
      closed_tableau' ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: (s, .diamond p2 f') :: fs)

    | .neg (.diamond (.if b p1 p2) f') =>
      closed_tableau' ((s, f) :: exp) (((s, bexp2formula b)) :: (s, .neg (.diamond p1 f')) :: fs) &&
      closed_tableau' ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: (s, .neg (.diamond p2 f')) :: fs)


    | f' =>
      closed_tableau' ((s, f) :: exp) fs

  -- expandir boxes que faltem
  | [] => false

partial def closed_tableau''
  (exp : List (PrefFormula σ t))
  (unexp : List (PrefFormula σ t)) : Option (Model σ t) :=
  if findContra (exp ++ unexp) then none else
  match unexp with
  | (s, f) :: fs => match f with
    | .neg (.neg f') =>
      closed_tableau'' ((s, f) :: exp) ((s,f') :: fs)

    | .and f1 f2 =>
      closed_tableau'' ((s, f) :: exp) ((s,f1) :: (s, f2) :: fs)

    | .neg (.and f1 f2) =>
      match closed_tableau'' ((s, f) :: exp) ((s, .neg f1) :: fs) with
      | some M => some M
      | none => closed_tableau'' ((s, f) :: exp) ((s, .neg f2) :: fs)

    | .diamond (.seq p1 p2) f' =>
      closed_tableau'' ((s, f) :: exp) ((s, .diamond p1 (.diamond p2 f')) :: fs)

    | .neg (.diamond (.seq p1 p2) f') =>
      closed_tableau'' ((s, f) :: exp) ((s, .neg (.diamond p1 (.diamond p2 f'))) :: fs)

    | .diamond (.assert b) f' =>
      closed_tableau'' ((s, f) :: exp) ((s, bexp2formula b) :: (s, f') :: fs)

    | .neg (.diamond (.assert b) f') =>
      match closed_tableau'' ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: fs) with
      | some M => some M
      | none => closed_tableau'' ((s, f) :: exp) ((s, .neg f') :: fs)

    | .diamond (.do p) f' =>
      let x : List (PrefFormula σ t) :=
        exp.filterMap
          (fun pf => match pf with
            | (s', .neg (.diamond (.do p') f'')) =>
              if (s' == s) && (p' == p)
              then some ((p :: s), .neg f'')
              else none
            | _ => none)
      closed_tableau'' ((s, f) :: exp) (((p :: s), f') :: (x ++ fs))

    --!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    -- (p :: s) já presente no ramo
    | .neg (.diamond (.do p) f') =>
      if (exp ++ unexp).any (fun (s', _) => s' == (p :: s))
      then closed_tableau'' ((s, f) :: exp) (((p :: s), .neg f') :: fs)
      else closed_tableau'' ((s, f) :: exp) fs
    --!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    | .diamond (.if b p1 p2) f' =>
      match closed_tableau'' ((s, f) :: exp) (((s, bexp2formula b)) :: (s, .diamond p1 f') :: fs)with
      | some M => some M
      | none => closed_tableau'' ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: (s, .diamond p2 f') :: fs)

    | .neg (.diamond (.if b p1 p2) f') =>
      match closed_tableau'' ((s, f) :: exp) (((s, bexp2formula b)) :: (s, .neg (.diamond p1 f')) :: fs) with
      | some M => some M
      | none => closed_tableau'' ((s, f) :: exp) (((s, .neg (bexp2formula b))) :: (s, .neg (.diamond p2 f')) :: fs)


    | f' =>
      closed_tableau'' ((s, f) :: exp) fs
  | [] =>
    some {
      W := List σ
      Ws := (exp.map (fun (s, _) => s)).dedup
      R :=
        fun p s =>
          if (exp.any (fun (s', _) => s' == (p :: s)))
          then some (p :: s)
          else none
      V := fun b =>
        (exp.filterMap
          (fun (s, f) =>
            if f == .atom_prop b
            then some s
            else none))
    }


def f1 : Formula Char Char :=
  .impl
    (.and
      (.diamond (.if (.prim 'b') (.do 'f') (.do 'g')) (.atom_prop 'p'))
      (.atom_prop 'b'))
    (.diamond (.do 'f') (.atom_prop 'p'))

def f2 : Formula Char Char :=
  .impl
    (.box (.do 'p') (.atom_prop 'f'))
    (.diamond (.do 'p') (.atom_prop 'f'))



#eval closed_tableau' [] [([], (.neg f2))]
