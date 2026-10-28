import Frege.VariableSupport
import Frege.RelationClosure

/-!
# Eta contraction and finite eta reductions

An eta contraction removes the redundant abstraction in `lambda x. f x`
when `f` does not use `x`. The shifted source in the root constructor encodes
that condition directly. These definitions are a subrelation of the existing
beta–eta calculus, not a replacement for its equality relation.
-/

namespace Frege.OpenLambda

inductive EtaStep : {n : Nat} → Term n → Term n → Prop where
  | eta (term : Term n) :
      EtaStep (.lam (.app (Program.rename Fin.succ term) (.var 0))) term
  | left : EtaStep left right → EtaStep (.app left argument) (.app right argument)
  | right : EtaStep argument other → EtaStep (.app function argument) (.app function other)
  | underLam : EtaStep body other → EtaStep (.lam body) (.lam other)

abbrev EtaSteps {n : Nat} := Relations.Path (@EtaStep n)
abbrev EtaOptional {n : Nat} := Relations.Optional (@EtaStep n)

namespace EtaStep

theorem toBetaEta {left right : Term n} (step : EtaStep left right) : BetaEtaStep left right := by
  induction step with
  | eta term => exact .eta term
  | left _ proof => exact .left proof
  | right _ proof => exact .right proof
  | underLam _ proof => exact .underLam proof

theorem instantiate {left right : Term n} (step : EtaStep left right)
    (bound : Fin n → Term m) (free : Nat → Term m) :
    EtaStep (OpenLambda.instantiate bound free left) (OpenLambda.instantiate bound free right) := by
  induction step generalizing m with
  | eta term =>
      rw [instantiation_commutes_with_eta_expansion]
      exact .eta _
  | left _ proof => exact .left (proof bound free)
  | right _ proof => exact .right (proof bound free)
  | underLam _ proof =>
      exact .underLam (proof (Program.liftSub bound)
        (fun name => Program.rename Fin.succ (free name)))

theorem substitute {left right : Term n} (step : EtaStep left right)
    (replace : Fin n → Term m) :
    EtaStep (Program.subst replace left) (Program.subst replace right) := by
  simpa only [instantiation_with_unchanged_free_names] using step.instantiate replace Program.coeff

theorem rename {left right : Term n} (step : EtaStep left right) (rename : Fin n → Fin m) :
    EtaStep (Program.rename rename left) (Program.rename rename right) := by
  simpa only [instantiating_with_variables_is_renaming] using
    step.instantiate (fun index => .var (rename index)) Program.coeff

theorem fromApplication {function argument result : Term n}
    (step : EtaStep (.app function argument) result) :
    (∃ other, EtaStep function other ∧ result = .app other argument) ∨
    (∃ other, EtaStep argument other ∧ result = .app function other) := by
  cases step with
  | left step => exact .inl ⟨_, step, rfl⟩
  | right step => exact .inr ⟨_, step, rfl⟩

theorem fromLambda {body : Term (n + 1)} {result : Term n}
    (step : EtaStep (.lam body) result) :
    (∃ term, body = .app (Program.rename Fin.succ term) (.var 0) ∧ result = term) ∨
    (∃ other, EtaStep body other ∧ result = .lam other) := by
  cases step with
  | eta term => exact .inl ⟨_, rfl, rfl⟩
  | underLam step => exact .inr ⟨_, step, rfl⟩

/-- A reduct of a weakened term can be unshifted, with no new variable captured. -/
theorem unshift {term : Term n} {result : Term (n + 1)}
    (step : EtaStep (Program.rename Fin.succ term) result) :
    ∃ smaller, EtaStep term smaller ∧ result = Program.rename Fin.succ smaller := by
  let smaller := Program.beta result (.coeff 0)
  have unused : AvoidsNewest result :=
    step.toBetaEta.preserves_support _ (a_weakened_term_avoids_the_new_variable term)
  refine ⟨smaller, ?_, (removing_an_unused_variable_and_restoring_it_changes_nothing result unused (.coeff 0)).symm⟩
  have unshifted := step.substitute (Program.single (.coeff 0))
  change EtaStep (Program.beta (Program.rename Fin.succ term) (.coeff 0)) smaller at unshifted
  rwa [substituting_into_a_weakened_term] at unshifted

end EtaStep

namespace EtaSteps

theorem appLeft {left right : Term n} (path : EtaSteps left right) (argument : Term n) :
    EtaSteps (.app left argument) (.app right argument) :=
  path.map (fun term => Program.app term argument) EtaStep.left

theorem appRight {left right : Term n} (path : EtaSteps left right) (function : Term n) :
    EtaSteps (.app function left) (.app function right) :=
  path.map (fun term => Program.app function term) EtaStep.right

theorem app {left right argument other : Term n}
    (functions : EtaSteps left right) (arguments : EtaSteps argument other) :
    EtaSteps (.app left argument) (.app right other) :=
  (appLeft functions argument).trans (appRight arguments right)

theorem underLam {left right : Term (n + 1)} (path : EtaSteps left right) :
    EtaSteps (.lam left) (.lam right) := path.map Program.lam EtaStep.underLam

theorem rename {left right : Term n} (path : EtaSteps left right) (rename : Fin n → Fin m) :
    EtaSteps (Program.rename rename left) (Program.rename rename right) :=
  path.map (Program.rename rename) (fun step => step.rename rename)

theorem substitute {left right : Term n} (path : EtaSteps left right) (replace : Fin n → Term m) :
    EtaSteps (Program.subst replace left) (Program.subst replace right) :=
  path.map (Program.subst replace) (fun step => step.substitute replace)

/-- Reducing a substituted argument may require a step at each of its occurrences. -/
theorem substituting_reducing_arguments (term : Term n) (first second : Fin n → Term m)
    (arguments : ∀ index, EtaSteps (first index) (second index)) :
    EtaSteps (Program.subst first term) (Program.subst second term) := by
  induction term generalizing m with
  | var index => exact arguments index
  | coeff name => exact .refl _
  | app left right leftProof rightProof => exact app (leftProof first second arguments) (rightProof first second arguments)
  | lam body bodyProof =>
      apply underLam
      apply bodyProof (Program.liftSub first) (Program.liftSub second)
      intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · exact .refl _
      · exact rename (arguments index) Fin.succ

theorem toBetaEta {left right : Term n} (path : EtaSteps left right) : BetaEtaSteps left right := by
  induction path with
  | refl _ => exact .refl _
  | next step _ rest => exact .next step.toBetaEta rest

end EtaSteps

namespace EtaOptional

theorem underLam {left right : Term (n + 1)} (step : EtaOptional left right) :
    EtaOptional (.lam left) (.lam right) := by
  rcases step with step | same
  · exact .inl (.underLam step)
  · exact .inr (congrArg Program.lam same)

theorem appLeft {left right : Term n} (step : EtaOptional left right) (argument : Term n) :
    EtaOptional (.app left argument) (.app right argument) := by
  rcases step with step | same
  · exact .inl (.left step)
  · exact .inr (congrArg (fun term => Program.app term argument) same)

theorem appRight {left right : Term n} (step : EtaOptional left right) (function : Term n) :
    EtaOptional (.app function left) (.app function right) := by
  rcases step with step | same
  · exact .inl (.right step)
  · exact .inr (congrArg (Program.app function) same)

end EtaOptional

end Frege.OpenLambda
