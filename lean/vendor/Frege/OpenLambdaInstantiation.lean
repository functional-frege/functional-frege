import Frege.OpenLambdaSyntax

/-!
# Substitution laws for both free and bound variables

These laws justify the explicit instantiation rule in the open term algebra.
They cover arbitrary substitutions for free names as well as local indices,
with the inserted terms shifted beneath each lambda binder. In particular,
instantiation commutes with beta contraction and with eta expansion.
-/

namespace Frege.OpenLambda

open Program

/-- First renaming and then instantiating composes the local-variable maps. -/
theorem instantiation_after_renaming (term : Term n) (rename : Fin n → Fin m)
    (bound : Fin m → Term k) (free : Nat → Term k) :
    instantiate bound free (Program.rename rename term) =
      instantiate (fun index => bound (rename index)) free term := by
  induction term generalizing m k with
  | var index => rfl
  | coeff name => rfl
  | app left right leftProof rightProof =>
      simp only [Program.rename, instantiate, leftProof rename bound free, rightProof rename bound free]
  | lam body bodyProof =>
      simp only [Program.rename, instantiate,
        bodyProof (liftRen rename) (liftSub bound) (fun name => Program.rename Fin.succ (free name))]
      congr 2
      funext index
      refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

/-- Renaming the result renames every inserted free and local argument. -/
theorem renaming_after_instantiation (term : Term n) (bound : Fin n → Term m)
    (free : Nat → Term m) (rename : Fin m → Fin k) :
    Program.rename rename (instantiate bound free term) =
      instantiate (fun index => Program.rename rename (bound index))
        (fun name => Program.rename rename (free name)) term := by
  induction term generalizing m k with
  | var index => rfl
  | coeff name => rfl
  | app left right leftProof rightProof =>
      simp only [Program.rename, instantiate, leftProof bound free rename, rightProof bound free rename]
  | lam body bodyProof =>
      simp only [instantiate, Program.rename,
        bodyProof (liftSub bound) (fun name => Program.rename Fin.succ (free name)) (liftRen rename)]
      have boundMaps :
          (fun index => Program.rename (liftRen rename) (liftSub bound index)) =
            liftSub (fun index => Program.rename rename (bound index)) := by
        funext index
        refine Fin.cases ?_ (fun index => ?_) index
        · rfl
        · simp only [liftSub_succ, rename_comp]
          rfl
      have freeMaps :
          (fun name => Program.rename (liftRen rename) (Program.rename Fin.succ (free name))) =
            (fun name => Program.rename Fin.succ (Program.rename rename (free name))) := by
        funext name
        simp only [rename_comp]
        rfl
      rw [boundMaps, freeMaps]

/-- Instantiation composes simultaneously on local variables and free names. -/
theorem instantiating_twice_is_composition (term : Term n)
    (firstBound : Fin n → Term m) (firstFree : Nat → Term m)
    (secondBound : Fin m → Term k) (secondFree : Nat → Term k) :
    instantiate secondBound secondFree (instantiate firstBound firstFree term) =
      instantiate (fun index => instantiate secondBound secondFree (firstBound index))
        (fun name => instantiate secondBound secondFree (firstFree name)) term := by
  induction term generalizing m k with
  | var index => rfl
  | coeff name => rfl
  | app left right leftProof rightProof =>
      simp only [instantiate, leftProof firstBound firstFree secondBound secondFree,
        rightProof firstBound firstFree secondBound secondFree]
  | lam body bodyProof =>
      simp only [instantiate, bodyProof (liftSub firstBound)
        (fun name => Program.rename Fin.succ (firstFree name)) (liftSub secondBound)
        (fun name => Program.rename Fin.succ (secondFree name))]
      have boundMaps :
          (fun index => instantiate (liftSub secondBound)
            (fun name => Program.rename Fin.succ (secondFree name)) (liftSub firstBound index)) =
          liftSub (fun index => instantiate secondBound secondFree (firstBound index)) := by
        funext index
        refine Fin.cases ?_ (fun index => ?_) index
        · rfl
        · simp only [liftSub_succ, instantiation_after_renaming]
          exact (renaming_after_instantiation (firstBound index) secondBound secondFree Fin.succ).symm
      have freeMaps :
          (fun name => instantiate (liftSub secondBound)
            (fun other => Program.rename Fin.succ (secondFree other))
            (Program.rename Fin.succ (firstFree name))) =
          (fun name => Program.rename Fin.succ (instantiate secondBound secondFree (firstFree name))) := by
        funext name
        simp only [instantiation_after_renaming, liftSub_succ]
        exact (renaming_after_instantiation (firstFree name) secondBound secondFree Fin.succ).symm
      rw [boundMaps, freeMaps]

/-- Keeping the free names unchanged recovers the existing local substitution. -/
theorem instantiation_with_unchanged_free_names (term : Term n) (bound : Fin n → Term m) :
    instantiate bound Program.coeff term = subst bound term := by
  induction term generalizing m with
  | var index => rfl
  | coeff name => rfl
  | app left right leftProof rightProof => simp only [instantiate, subst, leftProof bound, rightProof bound]
  | lam body bodyProof =>
      simp only [instantiate, subst, Program.rename]
      exact congrArg Program.lam (bodyProof (liftSub bound))

theorem instantiation_after_local_substitution (term : Term n) (replace : Fin n → Term m)
    (bound : Fin m → Term k) (free : Nat → Term k) :
    instantiate bound free (subst replace term) =
      instantiate (fun index => instantiate bound free (replace index)) free term := by
  rw [← instantiation_with_unchanged_free_names term replace, instantiating_twice_is_composition]
  rfl

/-- Beta contraction commutes with arbitrary capture-avoiding instantiation. -/
theorem instantiation_commutes_with_beta (body : Term (n + 1)) (argument : Term n)
    (bound : Fin n → Term m) (free : Nat → Term m) :
    instantiate bound free (beta body argument) =
      beta (instantiate (liftSub bound) (fun name => Program.rename Fin.succ (free name)) body)
        (instantiate bound free argument) := by
  simp only [beta, instantiation_after_local_substitution]
  rw [← instantiation_with_unchanged_free_names, instantiating_twice_is_composition]
  have boundMaps :
      (fun index => instantiate (single (instantiate bound free argument)) Program.coeff (liftSub bound index)) =
        (fun index => instantiate bound free (single argument index)) := by
    funext index
    refine Fin.cases ?_ (fun index => ?_) index
    · rfl
    · simp only [liftSub_succ, instantiation_after_renaming, single, Fin.cases_succ, instantiate]
      exact (instantiating_with_variables_is_renaming (bound index) id).trans (rename_id _)
  have freeMaps :
      (fun name => instantiate (single (instantiate bound free argument)) Program.coeff
        (Program.rename Fin.succ (free name))) = free := by
    funext name
    simp only [instantiation_after_renaming, single, Fin.cases_succ]
    exact (instantiating_with_variables_is_renaming (free name) id).trans (rename_id _)
  rw [boundMaps, freeMaps]

/-- Eta expansion commutes with instantiation; its freshness condition is preserved. -/
theorem instantiation_commutes_with_eta_expansion (term : Term n)
    (bound : Fin n → Term m) (free : Nat → Term m) :
    instantiate bound free (.lam (.app (Program.rename Fin.succ term) (.var 0))) =
      .lam (.app (Program.rename Fin.succ (instantiate bound free term)) (.var 0)) := by
  simp only [instantiate, instantiation_after_renaming, liftSub_succ, liftSub_zero]
  rw [← renaming_after_instantiation term bound free Fin.succ]

end Frege.OpenLambda
