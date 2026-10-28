import Frege.Execution

namespace Frege.Program

universe u
variable {C : Type u}

/-- One leftmost reduction, together with a kernel-checkable derivation. -/
def reduceOnce : {n : Nat} → (p : Program C n) → Option {q // Step p q}
  | _, .var _ => none
  | _, .coeff _ => none
  | _, .app (.lam p) q => some ⟨beta p q, .beta p q⟩
  | _, .app p q =>
    match reduceOnce p with
    | some ⟨p', h⟩ => some ⟨.app p' q, .left h⟩
    | none =>
      match reduceOnce q with
      | some ⟨q', h⟩ => some ⟨.app p q', .right h⟩
      | none => none
  | _, .lam p =>
    match reduceOnce p with
    | some ⟨p', h⟩ => some ⟨.lam p', .underLam h⟩
    | none => none

/-- Bounded execution; exhaustion returns a proved prefix, not a false normality claim. -/
def execute {n} : Nat → (p : Program C n) → {q // Steps p q}
  | 0, p => ⟨p, .refl p⟩
  | fuel+1, p =>
    match reduceOnce p with
    | none => ⟨p, .refl p⟩
    | some ⟨q, h⟩ =>
      let ⟨r, hs⟩ := execute fuel q
      ⟨r, .next h hs⟩

theorem execute_sound {Obj : Type v} {Fun : Type w} {Expr : Type x}
    {O : Operations Obj Fun Expr} (I : ProgramInterpretation O C)
    (vc : O.BasicLawVConcept) (vf : O.BasicLawVFunction)
    (vi : O.BasicLawVI) (conv : I.Conversion) {n}
    (fuel : Nat) (p : Program C n) (env : Fin n → Obj) :
    I.denote p env = I.denote (execute fuel p).val env :=
  I.execution_sound vc vf vi conv (execute fuel p).property env

def identity : Program C 0 := .lam (.var 0)
def konst : Program C 0 := .lam (.lam (.var 1))

example : (execute 1 (.app (identity : Program Empty 0) identity)).val = identity := rfl
example : (execute 2 (.app (.app (konst : Program Empty 0) identity) konst)).val = identity := rfl

end Frege.Program
