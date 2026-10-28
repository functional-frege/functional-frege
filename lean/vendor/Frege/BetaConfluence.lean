import Frege.ParallelBeta

/-!
# Confluence of ordinary beta reduction

Parallel beta steps have the diamond property. We lift that property to finite
paths, then prove that parallel and ordinary beta reduction have the same
finite reachability relation. The resulting confluence theorem concerns the
actual `Program.Step` relation used for executable program traces.

This is one dependency of beta-eta separation. It does not assert confluence
after eta is added, nor nontriviality of the beta-eta quotient.
-/

namespace Frege.Program

universe u
variable {C : Type u}

namespace Steps

theorem trans (first : Steps left middle) (second : Steps middle right) : Steps left right := by
  induction first with
  | refl term => exact second
  | next step _ rest => exact .next step (rest second)

theorem appLeft {left right : Program C n} (steps : Steps left right) (argument : Program C n) :
    Steps (.app (n := n) left argument) (.app right argument) := by
  induction steps with
  | refl term => exact .refl _
  | next step _ rest => exact .next (.left step) rest

theorem appRight {left right : Program C n} (steps : Steps left right) (function : Program C n) :
    Steps (.app (n := n) function left) (.app function right) := by
  induction steps with
  | refl term => exact .refl _
  | next step _ rest => exact .next (.right step) rest

theorem underLam (steps : Steps left right) : Steps (.lam left) (.lam right) := by
  induction steps with
  | refl term => exact .refl _
  | next step _ rest => exact .next (.underLam step) rest

theorem app (first : Steps left left') (second : Steps right right') :
    Steps (.app left right) (.app left' right') :=
  (appLeft first right).trans (appRight second left')

end Steps

/-- Finite parallel reductions, retaining their starting and ending terms. -/
inductive ParallelBetaSteps : {n : Nat} → Program C n → Program C n → Prop where
  | refl (term : Program C n) : ParallelBetaSteps term term
  | next : ParallelBeta first second → ParallelBetaSteps second last → ParallelBetaSteps first last

namespace ParallelBetaSteps

theorem trans (first : ParallelBetaSteps left middle) (second : ParallelBetaSteps middle right) :
    ParallelBetaSteps left right := by
  induction first with
  | refl term => exact second
  | next step _ rest => exact .next step (rest second)

/-- Move one parallel step past a finite path, using the diamond property. -/
theorem strip {source left right : Program C n}
    (step : ParallelBeta source left) (path : ParallelBetaSteps source right) :
    ∃ common, ParallelBetaSteps left common ∧ ParallelBeta right common := by
  induction path generalizing left with
  | refl source => exact ⟨left, .refl _, step⟩
  | next first _ rest =>
      obtain ⟨corner, fromLeft, fromNext⟩ := ParallelBeta.diamond step first
      obtain ⟨common, fromCorner, fromRight⟩ := rest fromNext
      exact ⟨common, .next fromLeft fromCorner, fromRight⟩

/-- Any two finite parallel paths from one term have a common continuation. -/
theorem confluence {source left right : Program C n}
    (first : ParallelBetaSteps source left) (second : ParallelBetaSteps source right) :
    ∃ common, ParallelBetaSteps left common ∧ ParallelBetaSteps right common := by
  induction first generalizing right with
  | refl source => exact ⟨right, second, .refl _⟩
  | next step _ rest =>
      obtain ⟨corner, fromNext, fromRight⟩ := strip step second
      obtain ⟨common, fromLeft, fromCorner⟩ := rest fromNext
      exact ⟨common, fromLeft, .next fromRight fromCorner⟩

end ParallelBetaSteps

/-- A single ordinary step is a permitted parallel step. -/
theorem Step.toParallelBeta {left right : Program C n} (step : Step left right) : ParallelBeta left right := by
  induction step with
  | beta body argument => exact .beta (.refl body) (.refl argument)
  | left _ proof => exact .app proof (.refl _)
  | right _ proof => exact .app (.refl _) proof
  | underLam _ proof => exact .lam proof

theorem Steps.toParallelBetaSteps (steps : Steps left right) : ParallelBetaSteps left right := by
  induction steps with
  | refl term => exact .refl term
  | next step _ rest => exact .next step.toParallelBeta rest

/-- A parallel step is realised by finitely many ordinary beta steps. -/
theorem ParallelBeta.toSteps (step : ParallelBeta left right) : Steps left right := by
  induction step with
  | var index => exact .refl _
  | coeff value => exact .refl _
  | app _ _ leftProof rightProof => exact .app leftProof rightProof
  | lam _ bodyProof => exact .underLam bodyProof
  | beta _ _ bodyProof argumentProof =>
      exact (Steps.app (.underLam bodyProof) argumentProof).trans
        (.next (.beta _ _) (.refl _))

theorem ParallelBetaSteps.toSteps (steps : ParallelBetaSteps left right) : Steps left right := by
  induction steps with
  | refl term => exact .refl term
  | next step _ rest => exact step.toSteps.trans rest

/-- Ordinary beta reduction is confluent, including beneath lambda binders.

Both inputs are actual finite executions in `Program.Steps`; the common term
comes with two further executions. No termination or normalisation assumption
is required, and the theorem applies to arbitrary fixed coefficients.
-/
theorem beta_reduction_is_confluent {source left right : Program C n}
    (first : Steps source left) (second : Steps source right) :
    ∃ common, Steps left common ∧ Steps right common := by
  obtain ⟨common, fromLeft, fromRight⟩ :=
    ParallelBetaSteps.confluence first.toParallelBetaSteps second.toParallelBetaSteps
  exact ⟨common, fromLeft.toSteps, fromRight.toSteps⟩

end Frege.Program
