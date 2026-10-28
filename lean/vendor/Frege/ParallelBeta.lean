import Frege.Programs

/-!
# Parallel beta reduction

This is the beta part of the confluence argument needed to separate elements
of the starting lambda-term algebra. Parallel reduction may reduce both sides
of an application and its root beta redex in a single step. Substitution
compatibility and complete development then give the diamond property.

The later beta-eta modules add eta reduction and connect the result to the
quotient presentation. Beta confluence alone is not the paper's model.
-/

namespace Frege.Program

universe u
variable {C : Type u}

theorem renaming_a_beta_result (body : Program C (n + 1)) (argument : Program C n)
    (rename : Fin n → Fin m) :
    Program.rename rename (beta body argument) =
      beta (Program.rename (liftRen rename) body) (Program.rename rename argument) := by
  simp only [beta, rename_subst, subst_rename]
  congr 1
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

theorem substituting_into_a_beta_result (body : Program C (n + 1)) (argument : Program C n)
    (replace : Fin n → Program C m) :
    subst replace (beta body argument) =
      beta (subst (liftSub replace) body) (subst replace argument) := by
  simp only [beta, subst_comp]
  congr 1
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · rfl
  · simp only [single, Fin.cases_succ, liftSub_succ, subst_rename]
    exact (subst_var (replace index)).symm

/-- Parallel beta reduction, with reflexive variable and coefficient cases. -/
inductive ParallelBeta : {n : Nat} → Program C n → Program C n → Prop where
  | var (index : Fin n) : ParallelBeta (.var index) (.var index)
  | coeff (value : C) : ParallelBeta (.coeff value) (.coeff value)
  | app : ParallelBeta left left' → ParallelBeta right right' →
      ParallelBeta (.app left right) (.app left' right')
  | lam : ParallelBeta body body' → ParallelBeta (.lam body) (.lam body')
  | beta : ParallelBeta body body' → ParallelBeta argument argument' →
      ParallelBeta (.app (.lam body) argument) (Program.beta body' argument')

namespace ParallelBeta

theorem refl (term : Program C n) : ParallelBeta term term := by
  induction term with
  | var index => exact .var index
  | coeff value => exact .coeff value
  | app left right leftProof rightProof => exact .app leftProof rightProof
  | lam body proof => exact .lam proof

/-- Parallel beta steps survive any capture-avoiding renaming. -/
theorem rename {left right : Program C n} (step : ParallelBeta left right) (rename : Fin n → Fin m) :
    ParallelBeta (Program.rename rename (n := n) left) (Program.rename rename right) := by
  induction step generalizing m with
  | var index => exact .var _
  | coeff value => exact .coeff value
  | app _ _ leftProof rightProof => exact .app (leftProof rename) (rightProof rename)
  | lam _ bodyProof => exact .lam (bodyProof (liftRen rename))
  | beta bodyStep argumentStep bodyProof argumentProof =>
      rw [renaming_a_beta_result]
      exact .beta (bodyProof (liftRen rename)) (argumentProof rename)

theorem lifted_substitutions_reduce_pointwise
    (first second : Fin n → Program C m)
    (pointwise : ∀ index, ParallelBeta (first index) (second index)) :
    ∀ index, ParallelBeta (liftSub first index) (liftSub second index) := by
  intro index
  refine Fin.cases ?_ (fun index => ?_) index
  · exact .var 0
  · exact rename (pointwise index) Fin.succ

/-- Reducing a body and all substituted arguments gives a parallel step. -/
theorem substitute {left right : Program C n} (step : ParallelBeta left right)
    (first second : Fin n → Program C m)
    (pointwise : ∀ index, ParallelBeta (first index) (second index)) :
    ParallelBeta (subst first (n := n) left) (subst second right) := by
  induction step generalizing m with
  | var index => exact pointwise index
  | coeff value => exact .coeff value
  | app _ _ leftProof rightProof => exact .app (leftProof first second pointwise) (rightProof first second pointwise)
  | lam _ bodyProof =>
      exact .lam (bodyProof (liftSub first) (liftSub second)
        (lifted_substitutions_reduce_pointwise first second pointwise))
  | beta bodyStep argumentStep bodyProof argumentProof =>
      rw [substituting_into_a_beta_result]
      exact .beta
        (bodyProof (liftSub first) (liftSub second)
          (lifted_substitutions_reduce_pointwise first second pointwise))
        (argumentProof first second pointwise)

end ParallelBeta

/-- Contract every original beta redex, recursively developing its subterms. -/
def completeBetaDevelopment : Program C n → Program C n
  | .var index => .var index
  | .coeff value => .coeff value
  | .lam body => .lam (completeBetaDevelopment body)
  | .app (.lam body) argument => beta (completeBetaDevelopment body) (completeBetaDevelopment argument)
  | .app left right => .app (completeBetaDevelopment left) (completeBetaDevelopment right)

/-- Every parallel reduct continues to the same complete development. -/
theorem ParallelBeta.continues_to_complete_development
    (step : ParallelBeta left right) : ParallelBeta right (completeBetaDevelopment left) := by
  induction step with
  | var index => exact .var index
  | coeff value => exact .coeff value
  | lam _ bodyProof => exact .lam bodyProof
  | @app n left left' right right' leftStep rightStep leftProof rightProof =>
      cases left with
      | var index => exact .app leftProof rightProof
      | coeff value => exact .app leftProof rightProof
      | app first second => exact .app leftProof rightProof
      | lam body =>
          cases leftStep with
          | lam bodyStep =>
              cases leftProof with
              | lam bodyProof => exact .beta bodyProof rightProof
  | @beta n body body' argument argument' bodyStep argumentStep bodyProof argumentProof =>
      apply ParallelBeta.substitute bodyProof (single argument') (single (completeBetaDevelopment argument))
      intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · exact argumentProof
      · exact .var index

/-- Two parallel beta steps from one term can be joined in one further step. -/
theorem ParallelBeta.diamond (first : ParallelBeta source left) (second : ParallelBeta source right) :
    ∃ common, ParallelBeta left common ∧ ParallelBeta right common :=
  ⟨completeBetaDevelopment source, first.continues_to_complete_development,
    second.continues_to_complete_development⟩

end Frege.Program
