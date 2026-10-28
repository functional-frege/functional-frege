import Frege.EtaReduction

/-!
# Confluence of eta contraction

Two eta contractions from the same term can be joined with at most one
further contraction on each side. The only overlap needing a side-condition
argument is an outer eta contraction against a contraction inside its body.
The support lemmas show that the inner result still avoids the bound variable.

The relation-closure theorem then joins arbitrary finite eta reductions.
Combining this with beta confluence still requires their commutation proof.
-/

namespace Frege.OpenLambda

/-- Shifting two terms beneath a binder cannot make them syntactically equal. -/
theorem weakening_is_injective {left right : Term n}
    (same : Program.rename Fin.succ left = Program.rename Fin.succ right) : left = right := by
  have unshifted := congrArg (fun term => Program.beta term (.coeff 0)) same
  simpa only [substituting_into_a_weakened_term] using unshifted

/-- Join an outer eta contraction with any competing eta contraction. -/
theorem EtaStep.join_with_outer_eta (term : Term n) {other : Term n}
    (step : EtaStep (.lam (.app (Program.rename Fin.succ term) (.var 0))) other) :
    ∃ common, EtaOptional term common ∧ EtaOptional other common := by
  rcases step.fromLambda with ⟨result, shape, resultEq⟩ | ⟨body, inside, rfl⟩
  · subst other
    have same : term = result := weakening_is_injective (Program.app.inj shape).1
    subst result
    exact ⟨term, .inr rfl, .inr rfl⟩
  · rcases inside.fromApplication with ⟨function, functionStep, rfl⟩ | ⟨argument, impossible, rfl⟩
    · obtain ⟨common, fromTerm, shape⟩ := functionStep.unshift
      rw [shape]
      exact ⟨common, .inl fromTerm, .inl (.eta common)⟩
    · cases impossible

/-- Competing eta contractions join in zero or one eta steps on each side. -/
theorem eta_contractions_have_an_optional_diamond {source left right : Term n}
    (first : EtaStep source left) (second : EtaStep source right) :
    ∃ common, EtaOptional left common ∧ EtaOptional right common := by
  induction first with
  | eta term => exact EtaStep.join_with_outer_eta term second
  | @left n function other argument step proof =>
      rcases second.fromApplication with ⟨result, functionStep, rfl⟩ | ⟨result, argumentStep, rfl⟩
      · obtain ⟨common, fromOther, fromResult⟩ := proof functionStep
        exact ⟨.app common argument, EtaOptional.appLeft fromOther argument,
          EtaOptional.appLeft fromResult argument⟩
      · exact ⟨.app other result, .inl (.right argumentStep), .inl (.left step)⟩
  | @right n argument other function step proof =>
      rcases second.fromApplication with ⟨result, functionStep, rfl⟩ | ⟨result, argumentStep, rfl⟩
      · exact ⟨.app result other, .inl (.left functionStep), .inl (.right step)⟩
      · obtain ⟨common, fromOther, fromResult⟩ := proof argumentStep
        exact ⟨.app function common, EtaOptional.appRight fromOther function,
          EtaOptional.appRight fromResult function⟩
  | @underLam n body other step proof =>
      rcases second.fromLambda with ⟨term, shape, resultEq⟩ | ⟨result, bodyStep, rfl⟩
      · subst right
        rw [shape] at step
        obtain ⟨common, fromTerm, fromOther⟩ := EtaStep.join_with_outer_eta term (.underLam step)
        exact ⟨common, fromOther, fromTerm⟩
      · obtain ⟨common, fromOther, fromResult⟩ := proof bodyStep
        exact ⟨.lam common, EtaOptional.underLam fromOther, EtaOptional.underLam fromResult⟩

/-- All finite eta reductions from a term can be continued to a common result. -/
theorem eta_reduction_is_confluent {source left right : Term n}
    (first : EtaSteps source left) (second : EtaSteps source right) :
    ∃ common, EtaSteps left common ∧ EtaSteps right common :=
  Relations.optional_diamonds_give_confluence eta_contractions_have_an_optional_diamond first second

end Frege.OpenLambda
