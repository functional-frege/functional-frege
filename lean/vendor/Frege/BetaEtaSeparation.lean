import Frege.BetaEtaConfluence

/-!
# Separation in the constructed extensional term algebra

Confluence turns a conversion into two reductions to a common term.
Consequently, two normal forms are convertible exactly when they are
syntactically equal. Distinct free names are normal forms, so their classes
give an explicit injection of the natural numbers into the actual algebra.

This proves nontriviality and infinitude of the starting extensional algebra.
The comprehension expansion and the full PE-lambda model remain separate
obligations; this file does not claim consistency of the entire manuscript.
-/

namespace Frege.OpenLambda

def BetaEtaNormal (term : Term n) : Prop := ∀ result, ¬ BetaEtaStep term result

/-- A term with no beta or eta redex can only reduce to itself. -/
theorem a_beta_eta_normal_term_has_no_nontrivial_reduction {term result : Term n}
    (normal : BetaEtaNormal term) (path : BetaEtaSteps term result) : term = result := by
  cases path with
  | refl _ => rfl
  | next step _ => exact False.elim (normal _ step)

/-- Convertibility implies a common reduct; no normalisation assumption is needed. -/
theorem BetaEtaConvertible.has_common_reduct {left right : Term n}
    (conversion : BetaEtaConvertible left right) :
    ∃ common, BetaEtaSteps left common ∧ BetaEtaSteps right common := by
  induction conversion with
  | refl term => exact ⟨term, .refl _, .refl _⟩
  | step one => exact ⟨_, .next one (.refl _), .refl _⟩
  | symm _ proof =>
      obtain ⟨common, fromLeft, fromRight⟩ := proof
      exact ⟨common, fromRight, fromLeft⟩
  | trans _ _ first second =>
      obtain ⟨firstCommon, fromLeft, fromMiddle⟩ := first
      obtain ⟨secondCommon, fromMiddle', fromRight⟩ := second
      obtain ⟨common, fromFirst, fromSecond⟩ := beta_eta_reduction_is_confluent fromMiddle fromMiddle'
      exact ⟨common, fromLeft.trans fromFirst, fromRight.trans fromSecond⟩

/-- Two terms are beta–eta convertible exactly when they reduce to a common term. -/
theorem beta_eta_conversion_iff_common_reduct (left right : Term n) :
    BetaEtaConvertible left right ↔
      ∃ common, BetaEtaSteps left common ∧ BetaEtaSteps right common := by
  constructor
  · exact BetaEtaConvertible.has_common_reduct
  · rintro ⟨common, fromLeft, fromRight⟩
    exact fromLeft.toConversion.trans fromRight.toConversion.symm

/-- Distinct beta–eta normal forms cannot be equated by conversion. -/
theorem beta_eta_normal_forms_are_convertible_exactly_when_equal
    (left right : Term n) (leftNormal : BetaEtaNormal left) (rightNormal : BetaEtaNormal right) :
    BetaEtaConvertible left right ↔ left = right := by
  constructor
  · intro conversion
    obtain ⟨common, fromLeft, fromRight⟩ := conversion.has_common_reduct
    exact (a_beta_eta_normal_term_has_no_nontrivial_reduction leftNormal fromLeft).trans
      (a_beta_eta_normal_term_has_no_nontrivial_reduction rightNormal fromRight).symm
  · intro same; subst right; exact .refl _

/-- The concrete quotient preserves every distinction between normal forms. -/
theorem normal_forms_have_equal_algebra_classes_exactly_when_equal
    (left right : Term 0) (leftNormal : BetaEtaNormal left) (rightNormal : BetaEtaNormal right) :
    termClass left = termClass right ↔ left = right :=
  (quotient_classes_are_equal_exactly_when_beta_eta_convertible left right).trans
    (beta_eta_normal_forms_are_convertible_exactly_when_equal left right leftNormal rightNormal)

theorem a_free_name_is_beta_eta_normal (name : Nat) : BetaEtaNormal (Program.coeff (n := n) name) := by
  intro result step
  cases step

/-- Arbitrarily many distinct elements are explicitly exhibited in the algebra. -/
theorem the_free_name_classes_form_an_injection (first second : Nat)
    (sameClass : termClass (.coeff first) = termClass (.coeff second)) : first = second := by
  have sameTerms := (normal_forms_have_equal_algebra_classes_exactly_when_equal
    (.coeff first) (.coeff second) (a_free_name_is_beta_eta_normal first)
    (a_free_name_is_beta_eta_normal second)).1 sameClass
  exact Program.coeff.inj sameTerms

/-- The constructed algebra contains two unequal elements. -/
theorem the_constructed_extensional_algebra_is_nontrivial :
    termClass (.coeff 0) ≠ termClass (.coeff 1) := by
  intro same
  have impossible := the_free_name_classes_form_an_injection 0 1 same
  cases impossible

end Frege.OpenLambda
