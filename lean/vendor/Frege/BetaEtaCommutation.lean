import Frege.EtaConfluence
import Frege.BetaConfluence

/-!
# Commuting beta and eta reductions

The central square joins a beta contraction and an eta contraction from the
same source. After beta there may be several eta steps because substitution
can duplicate the eta redex; after eta, at most one beta step is needed.
No reduction is assumed to terminate.
-/

namespace Frege.OpenLambda

abbrev BetaOptional {n : Nat} := Relations.Optional (@Program.Step Nat n)

theorem beta_step_is_a_beta_eta_step {left right : Term n} (step : Program.Step left right) :
    BetaEtaStep left right := by
  induction step with
  | beta body argument => exact .beta body argument
  | left _ proof => exact .left proof
  | right _ proof => exact .right proof
  | underLam _ proof => exact .underLam proof

theorem substituting_preserves_a_beta_step {left right : Term n}
    (step : Program.Step left right) (replace : Fin n → Term m) :
    Program.Step (Program.subst replace left) (Program.subst replace right) := by
  induction step generalizing m with
  | beta body argument =>
      rw [Program.substituting_into_a_beta_result]
      exact .beta _ _
  | left _ proof => exact .left (proof replace)
  | right _ proof => exact .right (proof replace)
  | underLam _ proof => exact .underLam (proof (Program.liftSub replace))

theorem unshifting_a_beta_step {term : Term n} {result : Term (n + 1)}
    (step : Program.Step (Program.rename Fin.succ term) result) :
    ∃ smaller, Program.Step term smaller ∧ result = Program.rename Fin.succ smaller := by
  let smaller := Program.beta result (.coeff 0)
  have unused : AvoidsNewest result :=
    (beta_step_is_a_beta_eta_step step).preserves_support _
      (a_weakened_term_avoids_the_new_variable term)
  refine ⟨smaller, ?_, (removing_an_unused_variable_and_restoring_it_changes_nothing result unused (.coeff 0)).symm⟩
  have unshifted := substituting_preserves_a_beta_step step (Program.single (.coeff 0))
  change Program.Step (Program.beta (Program.rename Fin.succ term) (.coeff 0)) smaller at unshifted
  rwa [substituting_into_a_weakened_term] at unshifted

theorem beta_step_from_application {function argument result : Term n}
    (step : Program.Step (.app function argument) result) :
    (∃ body, function = .lam body ∧ result = Program.beta body argument) ∨
    (∃ other, Program.Step function other ∧ result = .app other argument) ∨
    (∃ other, Program.Step argument other ∧ result = .app function other) := by
  cases step with
  | beta body argument => exact .inl ⟨_, rfl, rfl⟩
  | left step => exact .inr (.inl ⟨_, step, rfl⟩)
  | right step => exact .inr (.inr ⟨_, step, rfl⟩)

namespace BetaOptional

theorem toSteps {left right : Term n} (step : BetaOptional left right) : Program.Steps left right := by
  rcases step with one | same
  · exact .next one (.refl _)
  · subst right; exact .refl _

theorem underLam {left right : Term (n + 1)} (step : BetaOptional left right) :
    BetaOptional (.lam left) (.lam right) := by
  rcases step with step | same
  · exact .inl (.underLam step)
  · exact .inr (congrArg Program.lam same)

theorem appLeft {left right : Term n} (step : BetaOptional left right) (argument : Term n) :
    BetaOptional (.app left argument) (.app right argument) := by
  rcases step with step | same
  · exact .inl (.left step)
  · exact .inr (congrArg (fun term => Program.app term argument) same)

theorem appRight {left right : Term n} (step : BetaOptional left right) (function : Term n) :
    BetaOptional (.app function left) (.app function right) := by
  rcases step with step | same
  · exact .inl (.right step)
  · exact .inr (congrArg (Program.app function) same)

end BetaOptional

/-- Resolve the overlap between an outer eta contraction and an inner beta step. -/
theorem a_beta_step_commutes_with_outer_eta (term : Term n) {other : Term n}
    (step : Program.Step (.lam (.app (Program.rename Fin.succ term) (.var 0))) other) :
    ∃ common, EtaSteps other common ∧ BetaOptional term common := by
  cases step with
  | underLam inside =>
      rcases beta_step_from_application inside with ⟨body, shape, resultEq⟩ |
        ⟨function, functionStep, resultEq⟩ | ⟨argument, impossible, resultEq⟩
      · cases term with
        | var index => cases shape
        | coeff name => cases shape
        | app left right => cases shape
        | lam original =>
            have bodyEq := Program.lam.inj shape
            subst body
            rw [resultEq, beta_inside_an_eta_expanded_lambda]
            exact ⟨.lam original, .refl _, .inr rfl⟩
      · obtain ⟨common, fromTerm, shape⟩ := unshifting_a_beta_step functionStep
        rw [resultEq, shape]
        exact ⟨common, .single (.eta common), .inl fromTerm⟩
      · cases impossible

/-- Substitution evaluates the body of a redundant eta abstraction directly. -/
theorem applying_an_eta_body (term argument : Term n) :
    Program.beta (.app (Program.rename Fin.succ term) (.var 0)) argument = .app term argument := by
  change Program.app (Program.beta (Program.rename Fin.succ term) argument) argument = _
  rw [substituting_into_a_weakened_term]

/-- A beta/eta fork joins by eta steps and at most one beta step, respectively. -/
theorem beta_and_eta_contractions_commute {source left right : Term n}
    (betaStep : Program.Step source left) (etaStep : EtaStep source right) :
    ∃ common, EtaSteps left common ∧ BetaOptional right common := by
  induction betaStep with
  | beta body argument =>
      rcases etaStep.fromApplication with ⟨function, functionStep, rfl⟩ | ⟨other, argumentStep, rfl⟩
      · rcases functionStep.fromLambda with ⟨term, shape, functionEq⟩ | ⟨otherBody, bodyStep, functionEq⟩
        · subst function
          rw [shape, applying_an_eta_body]
          exact ⟨.app term argument, .refl _, .inr rfl⟩
        · subst function
          exact ⟨Program.beta otherBody argument,
            .single (bodyStep.substitute (Program.single argument)), .inl (.beta _ _)⟩
      · refine ⟨Program.beta body other, ?_, .inl (.beta _ _)⟩
        apply EtaSteps.substituting_reducing_arguments body (Program.single argument) (Program.single other)
        intro index
        refine Fin.cases ?_ (fun _ => ?_) index
        · exact .single argumentStep
        · exact .refl _
  | @left n function other argument step proof =>
      rcases etaStep.fromApplication with ⟨result, functionStep, rfl⟩ | ⟨result, argumentStep, rfl⟩
      · obtain ⟨common, fromOther, fromResult⟩ := proof functionStep
        exact ⟨.app common argument, EtaSteps.appLeft fromOther argument,
          BetaOptional.appLeft fromResult argument⟩
      · exact ⟨.app other result, .single (.right argumentStep), .inl (.left step)⟩
  | @right n function argument other step proof =>
      rcases etaStep.fromApplication with ⟨result, functionStep, rfl⟩ | ⟨result, argumentStep, rfl⟩
      · exact ⟨.app result other, .single (.left functionStep), .inl (.right step)⟩
      · obtain ⟨common, fromOther, fromResult⟩ := proof argumentStep
        exact ⟨.app function common, EtaSteps.appRight fromOther function,
          BetaOptional.appRight fromResult function⟩
  | @underLam n body other step proof =>
      rcases etaStep.fromLambda with ⟨term, shape, resultEq⟩ | ⟨result, bodyStep, rfl⟩
      · subst right
        rw [shape] at step
        exact a_beta_step_commutes_with_outer_eta term (.underLam step)
      · obtain ⟨common, fromOther, fromResult⟩ := proof bodyStep
        exact ⟨.lam common, EtaSteps.underLam fromOther, BetaOptional.underLam fromResult⟩

/-- Move one beta contraction past a finite sequence of eta contractions. -/
theorem a_beta_step_commutes_with_eta_steps {source left right : Term n}
    (betaStep : Program.Step source left) (etaPath : EtaSteps source right) :
    ∃ common, EtaSteps left common ∧ BetaOptional right common := by
  induction etaPath generalizing left with
  | refl _ => exact ⟨left, .refl _, .inl betaStep⟩
  | next first rest remaining =>
      obtain ⟨corner, fromLeft, fromNext⟩ := beta_and_eta_contractions_commute betaStep first
      rcases fromNext with one | same
      · obtain ⟨common, fromCorner, fromRight⟩ := remaining one
        exact ⟨common, fromLeft.trans fromCorner, fromRight⟩
      · subst corner
        exact ⟨_, fromLeft.trans rest, .inr rfl⟩

/-- Any beta path and eta path from the same term have opposite-colour continuations. -/
theorem finite_beta_and_eta_reductions_commute {source left right : Term n}
    (betaPath : Program.Steps source left) (etaPath : EtaSteps source right) :
    ∃ common, EtaSteps left common ∧ Program.Steps right common := by
  induction betaPath generalizing right with
  | refl _ => exact ⟨right, etaPath, .refl _⟩
  | next first _ remaining =>
      obtain ⟨corner, fromNext, fromRight⟩ := a_beta_step_commutes_with_eta_steps first etaPath
      obtain ⟨common, fromLeft, fromCorner⟩ := remaining fromNext
      exact ⟨common, fromLeft, (BetaOptional.toSteps fromRight).trans fromCorner⟩

end Frege.OpenLambda
