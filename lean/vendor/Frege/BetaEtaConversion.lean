import Frege.OpenLambdaAlgebra
import Frege.OpenLambdaInstantiation

/-!
# The term algebra uses exactly beta–eta conversion

A reduction step contracts one beta or eta redex, at any position in a term.
Convertibility is the reflexive, symmetric, transitive closure of those steps.
There is no substitution constructor in either definition. Instead, we prove
that capture-avoiding substitution preserves reduction and hence conversion.

This makes the explicit instantiation rule in `OpenLambda.Equality` admissible:
the quotient used for the algebra has precisely ordinary beta–eta conversion
as its equality relation. Confluence and distinctness of quotient classes
are proved separately in `BetaEtaConfluence.lean` and `BetaEtaSeparation.lean`;
neither follows merely from this equivalence.
-/

namespace Frege.OpenLambda

/-- One beta or eta contraction, including contractions beneath lambda binders. -/
inductive BetaEtaStep : {n : Nat} → Term n → Term n → Prop where
  | beta (body : Term (n + 1)) (argument : Term n) :
      BetaEtaStep (.app (.lam body) argument) (Program.beta body argument)
  | eta (term : Term n) :
      BetaEtaStep (.lam (.app (Program.rename Fin.succ term) (.var 0))) term
  | left : BetaEtaStep left right → BetaEtaStep (.app left argument) (.app right argument)
  | right : BetaEtaStep argument other → BetaEtaStep (.app function argument) (.app function other)
  | underLam : BetaEtaStep body other → BetaEtaStep (.lam body) (.lam other)

/-- A finite sequence of beta and eta contractions. -/
inductive BetaEtaSteps : {n : Nat} → Term n → Term n → Prop where
  | refl (term : Term n) : BetaEtaSteps term term
  | next : BetaEtaStep first second → BetaEtaSteps second last → BetaEtaSteps first last

/-- Conversion allows finitely many forward or backward beta–eta steps. -/
inductive BetaEtaConvertible : {n : Nat} → Term n → Term n → Prop where
  | refl (term : Term n) : BetaEtaConvertible term term
  | step : BetaEtaStep left right → BetaEtaConvertible left right
  | symm : BetaEtaConvertible left right → BetaEtaConvertible right left
  | trans : BetaEtaConvertible left middle → BetaEtaConvertible middle right →
      BetaEtaConvertible left right

/-- Substituting free names and local variables preserves each contraction.

For eta, the term being contracted was weakened beneath a fresh binder. The
instantiation lemma preserves this shape, so substitution cannot capture the
bound variable or invalidate the eta side condition.
-/
theorem BetaEtaStep.instantiate {left right : Term n} (step : BetaEtaStep left right)
    (bound : Fin n → Term m) (free : Nat → Term m) :
    BetaEtaStep (OpenLambda.instantiate bound free left)
      (OpenLambda.instantiate bound free right) := by
  induction step generalizing m with
  | beta body argument =>
      rw [instantiation_commutes_with_beta]
      exact .beta _ _
  | eta term =>
      rw [instantiation_commutes_with_eta_expansion]
      exact .eta _
  | left _ proof => exact .left (proof bound free)
  | right _ proof => exact .right (proof bound free)
  | underLam _ proof =>
      exact .underLam (proof (Program.liftSub bound)
        (fun name => Program.rename Fin.succ (free name)))

theorem BetaEtaStep.rename {left right : Term n} (step : BetaEtaStep left right)
    (rename : Fin n → Fin m) :
    BetaEtaStep (Program.rename rename left) (Program.rename rename right) := by
  simpa only [instantiating_with_variables_is_renaming] using
    step.instantiate (fun index => .var (rename index)) Program.coeff

namespace BetaEtaSteps

theorem trans {first middle last : Term n}
    (before : BetaEtaSteps first middle) (after : BetaEtaSteps middle last) :
    BetaEtaSteps first last := by
  induction before with
  | refl _ => exact after
  | next step _ rest => exact .next step (rest after)

theorem instantiate {left right : Term n} (steps : BetaEtaSteps left right)
    (bound : Fin n → Term m) (free : Nat → Term m) :
    BetaEtaSteps (OpenLambda.instantiate bound free left)
      (OpenLambda.instantiate bound free right) := by
  induction steps with
  | refl _ => exact .refl _
  | next step _ rest => exact .next (step.instantiate bound free) rest

theorem toConversion {left right : Term n} (steps : BetaEtaSteps left right) :
    BetaEtaConvertible left right := by
  induction steps with
  | refl _ => exact .refl _
  | next step _ rest => exact .trans (.step step) rest

end BetaEtaSteps

namespace BetaEtaConvertible

theorem appLeft {left right : Term n} (equation : BetaEtaConvertible left right)
    (argument : Term n) : BetaEtaConvertible (.app left argument) (.app right argument) := by
  induction equation with
  | refl _ => exact .refl _
  | step one => exact .step (.left one)
  | symm _ proof => exact .symm proof
  | trans _ _ first second => exact .trans first second

theorem appRight {left right : Term n} (equation : BetaEtaConvertible left right)
    (function : Term n) : BetaEtaConvertible (.app function left) (.app function right) := by
  induction equation with
  | refl _ => exact .refl _
  | step one => exact .step (.right one)
  | symm _ proof => exact .symm proof
  | trans _ _ first second => exact .trans first second

theorem app {left right argument other : Term n}
    (functions : BetaEtaConvertible left right) (arguments : BetaEtaConvertible argument other) :
    BetaEtaConvertible (.app left argument) (.app right other) :=
  (functions.appLeft argument).trans (arguments.appRight right)

theorem underLam {left right : Term (n + 1)} (equation : BetaEtaConvertible left right) :
    BetaEtaConvertible (.lam left) (.lam right) := by
  induction equation with
  | refl _ => exact .refl _
  | step one => exact .step (.underLam one)
  | symm _ proof => exact .symm proof
  | trans _ _ first second => exact .trans first second

/-- Conversion is closed under substitution as a theorem, not an extra rule. -/
theorem instantiate {left right : Term n} (equation : BetaEtaConvertible left right)
    (bound : Fin n → Term m) (free : Nat → Term m) :
    BetaEtaConvertible (OpenLambda.instantiate bound free left)
      (OpenLambda.instantiate bound free right) := by
  induction equation with
  | refl _ => exact .refl _
  | step one => exact .step (one.instantiate bound free)
  | symm _ proof => exact .symm proof
  | trans _ _ first second => exact .trans first second

end BetaEtaConvertible

theorem BetaEtaStep.toEquation {left right : Term n} (step : BetaEtaStep left right) :
    Equality left right := by
  induction step with
  | beta body argument => exact .beta body argument
  | eta term => exact .eta term
  | left _ proof => exact .app proof (.refl _)
  | right _ proof => exact .app (.refl _) proof
  | underLam _ proof => exact .lam proof

theorem BetaEtaConvertible.toEquation {left right : Term n}
    (equation : BetaEtaConvertible left right) : Equality left right := by
  induction equation with
  | refl _ => exact .refl _
  | step one => exact one.toEquation
  | symm _ proof => exact .symm proof
  | trans _ _ first second => exact .trans first second

/-- Every derivation in the algebra's equality presentation is ordinary conversion. -/
theorem Equality.toBetaEtaConversion {left right : Term n} (equation : Equality left right) :
    BetaEtaConvertible left right := by
  induction equation with
  | refl _ => exact .refl _
  | symm _ proof => exact .symm proof
  | trans _ _ first second => exact .trans first second
  | app _ _ functions arguments => exact functions.app arguments
  | lam _ proof => exact proof.underLam
  | beta body argument => exact .step (.beta body argument)
  | eta term => exact .step (.eta term)
  | instantiate bound free _ proof => exact proof.instantiate bound free

/-- The equational presentation adds no equalities beyond beta–eta conversion. -/
theorem algebra_equations_are_exactly_beta_eta_conversion (left right : Term n) :
    Equality left right ↔ BetaEtaConvertible left right :=
  ⟨Equality.toBetaEtaConversion, BetaEtaConvertible.toEquation⟩

/-- Two representatives denote the same algebra element exactly when convertible. -/
theorem quotient_classes_are_equal_exactly_when_beta_eta_convertible (left right : Term 0) :
    termClass left = termClass right ↔ BetaEtaConvertible left right := by
  constructor
  · intro sameClass
    exact (Quotient.exact sameClass).toBetaEtaConversion
  · intro convertible
    exact Quotient.sound convertible.toEquation

end Frege.OpenLambda
