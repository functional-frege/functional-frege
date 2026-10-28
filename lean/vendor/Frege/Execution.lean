import Frege.Application
import Frege.Programs

namespace Frege

universe u v w c

variable {Obj : Type u} {Fun : Type v} {Expr : Type w} {C : Type c}

/-- Realization of exactly the scoped program bodies, not all object functions. -/
structure ProgramInterpretation (O : Operations Obj Fun Expr) (C : Type c) where
  coefficient : C → Obj
  function : {n : Nat} → Program C (n+1) → (Fin n → Obj) → Fun

namespace ProgramInterpretation

variable {O : Operations Obj Fun Expr} (I : ProgramInterpretation O C)

def denote : {n : Nat} → Program C n → (Fin n → Obj) → Obj
  | _, .var i, env => env i
  | _, .coeff c, _ => I.coefficient c
  | _, .app p q, env => O.app (denote p env) (denote q env)
  | _, .lam p, env => O.range (I.function p env)

/-- Function-level Conversion, restricted to the admitted program grammar. -/
def Conversion : Prop := ∀ {n} (p : Program C (n+1)) (env : Fin n → Obj) a,
  O.eval (I.function p env) a = I.denote p (Fin.cases a env)

theorem denote_rename (vf : O.BasicLawVFunction) (conv : I.Conversion)
    {n m} (p : Program C n) (ρ : Fin n → Fin m) (env : Fin m → Obj) :
    I.denote (p.rename ρ) env = I.denote p (fun i => env (ρ i)) := by
  induction p generalizing m with
  | var i => rfl
  | coeff c => rfl
  | app p q hp hq => simp only [Program.rename, denote, hp, hq]
  | lam p hp =>
    simp only [Program.rename, denote]
    apply (vf _ _).mpr
    intro a
    rw [conv, conv, hp]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem denote_subst (vf : O.BasicLawVFunction) (conv : I.Conversion)
    {n m} (p : Program C n) (σ : Fin n → Program C m) (env : Fin m → Obj) :
    I.denote (p.subst σ) env = I.denote p (fun i => I.denote (σ i) env) := by
  induction p generalizing m with
  | var i => rfl
  | coeff c => rfl
  | app p q hp hq => simp only [Program.subst, denote, hp, hq]
  | lam p hp =>
    simp only [Program.subst, denote]
    apply (vf _ _).mpr
    intro a
    rw [conv, conv, hp]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Program.liftSub_succ, I.denote_rename vf conv]
      rfl

/-- Object beta is obtained from Frege application and function Conversion. -/
theorem beta_sound (vc : O.BasicLawVConcept) (vf : O.BasicLawVFunction)
    (vi : O.BasicLawVI) (conv : I.Conversion) {n}
    (p : Program C (n+1)) (q : Program C n) (env : Fin n → Obj) :
    I.denote (.app (.lam p) q) env = I.denote (Program.beta p q) env := by
  simp only [denote, O.range_application vc vf vi,
    Program.beta, I.denote_subst vf conv]
  rw [conv]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Soundness of every syntactic reduction, including beneath a binder. -/
theorem step_sound (vc : O.BasicLawVConcept) (vf : O.BasicLawVFunction)
    (vi : O.BasicLawVI) (conv : I.Conversion) {n} {p q : Program C n}
    (h : Program.Step p q) (env : Fin n → Obj) : I.denote p env = I.denote q env := by
  induction h with
  | beta p q => exact I.beta_sound vc vf vi conv p q env
  | left h ih => exact congrArg (fun z => O.app z _) (ih env)
  | right h ih => exact congrArg (O.app _) (ih env)
  | underLam h ih =>
    simp only [denote]
    apply (vf _ _).mpr
    intro a
    rw [conv, conv]
    exact ih _

theorem execution_sound (vc : O.BasicLawVConcept) (vf : O.BasicLawVFunction)
    (vi : O.BasicLawVI) (conv : I.Conversion) {n} {p q : Program C n}
    (h : Program.Steps p q) (env : Fin n → Obj) : I.denote p env = I.denote q env := by
  induction h with
  | refl p => rfl
  | next h hs ih => exact (I.step_sound vc vf vi conv h env).trans ih

end ProgramInterpretation
end Frege
