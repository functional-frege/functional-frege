import FregeanECA.ComputationalAbstraction
import FregeanECA.Pure

/-! The semantic bridge from ordinary lambda terms to the existing, explicit
K/S bracket translation. No conversion or completeness principle is assumed. -/

namespace FregeanECA.LambdaInterpretation

open Frege
universe u c

variable {D : Type u} {C : Type c}

theorem meaning_rename (A : CombinatoryAlgebra D) (ext : A.IsExtensional)
    (coefficient : C → D) {n m : Nat} (p : Program C n)
    (rename : Fin n → Fin m) (environment : Fin m → D) :
    A.programMeaning coefficient (Program.rename rename p) environment =
      A.programMeaning coefficient p (fun i => environment (rename i)) := by
  induction p generalizing m with
  | var i => rfl
  | coeff value => rfl
  | app left right ihl ihr =>
      simp only [Program.rename, CombinatoryAlgebra.meaning_of_an_application, ihl, ihr]
  | lam body ih =>
      apply ext
      intro argument
      simp only [Program.rename, CombinatoryAlgebra.every_program_binder_evaluates_its_body]
      rw [ih]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem meaning_subst (A : CombinatoryAlgebra D) (ext : A.IsExtensional)
    (coefficient : C → D) {n m : Nat} (p : Program C n)
    (substitute : Fin n → Program C m) (environment : Fin m → D) :
    A.programMeaning coefficient (Program.subst substitute p) environment =
      A.programMeaning coefficient p
        (fun i => A.programMeaning coefficient (substitute i) environment) := by
  induction p generalizing m with
  | var i => rfl
  | coeff value => rfl
  | app left right ihl ihr =>
      simp only [Program.subst, CombinatoryAlgebra.meaning_of_an_application, ihl, ihr]
  | lam body ih =>
      apply ext
      intro argument
      simp only [Program.subst, CombinatoryAlgebra.every_program_binder_evaluates_its_body]
      rw [ih]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change A.programMeaning coefficient (Program.rename Fin.succ (substitute j))
          (Fin.cases argument environment) = _
        exact meaning_rename A ext coefficient (substitute j) Fin.succ _

theorem step_sound (A : CombinatoryAlgebra D) (ext : A.IsExtensional)
    (coefficient : Nat → D) {n : Nat} {left right : OpenLambda.Term n}
    (step : OpenLambda.BetaEtaStep left right) :
    ∀ environment, A.programMeaning coefficient left environment =
      A.programMeaning coefficient right environment := by
  induction step with
  | beta body argument =>
      intro environment
      rw [CombinatoryAlgebra.meaning_of_an_application,
        CombinatoryAlgebra.every_program_binder_evaluates_its_body,
        Program.beta, meaning_subst A ext]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
  | eta term =>
      intro environment
      apply ext
      intro argument
      rw [CombinatoryAlgebra.every_program_binder_evaluates_its_body,
        CombinatoryAlgebra.meaning_of_an_application, meaning_rename A ext]
      rfl
  | left _ ih =>
      intro environment
      exact congrArg (fun code => A.apply code _) (ih environment)
  | right _ ih =>
      intro environment
      exact congrArg (A.apply _) (ih environment)
  | underLam _ ih =>
      intro environment
      apply ext
      intro argument
      rw [CombinatoryAlgebra.every_program_binder_evaluates_its_body,
        CombinatoryAlgebra.every_program_binder_evaluates_its_body]
      exact ih _

/-- Ordinary beta-eta conversion preserves the explicit bracket interpretation
in every extensional combinatory algebra, under every variable assignment. -/
theorem conversion_sound (A : CombinatoryAlgebra D) (ext : A.IsExtensional)
    (coefficient : Nat → D) {n : Nat} {left right : OpenLambda.Term n}
    (conversion : OpenLambda.BetaEtaConvertible left right) :
    ∀ environment, A.programMeaning coefficient left environment =
      A.programMeaning coefficient right environment := by
  induction conversion with
  | refl => intro _; rfl
  | step reduction => exact step_sound A ext coefficient reduction
  | symm _ ih => intro environment; exact (ih environment).symm
  | trans _ _ first second =>
      intro environment
      exact (first environment).trans (second environment)

theorem beta_after_substitution {n : Nat} (body : OpenLambda.Term (n + 1))
    (environment : Fin n → OpenLambda.Term 0) (argument : OpenLambda.Term 0) :
    Program.beta (Program.subst (Program.liftSub environment) body) argument =
      Program.subst (Fin.cases argument environment) body := by
  rw [Program.beta, Program.subst_comp]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Program.liftSub_succ, Program.subst_rename,
      Program.single, Fin.cases_succ, Program.subst_var]

theorem meaning_in_term_algebra {n : Nat} (p : OpenLambda.Term n)
    (environment : Fin n → OpenLambda.Term 0) :
    OpenLambda.algebra.programMeaning (fun name => OpenLambda.termClass (.coeff name)) p
      (fun i => OpenLambda.termClass (environment i)) =
        OpenLambda.termClass (Program.subst environment p) := by
  induction p with
  | var i => rfl
  | coeff name => rfl
  | app left right ihl ihr =>
      simp only [CombinatoryAlgebra.meaning_of_an_application, ihl, ihr, Program.subst]
      rfl
  | lam body ih =>
      apply OpenLambda.the_constructed_open_term_algebra_is_extensional
      intro argument
      refine Quotient.inductionOn argument ?_
      intro term
      change OpenLambda.algebra.apply
        (OpenLambda.algebra.programMeaning (fun name => OpenLambda.termClass (.coeff name))
          (.lam body) (fun i => OpenLambda.termClass (environment i)))
        (OpenLambda.termClass term) =
          OpenLambda.algebra.apply
            (OpenLambda.termClass (.lam (Program.subst (Program.liftSub environment) body)))
            (OpenLambda.termClass term)
      rw [CombinatoryAlgebra.every_program_binder_evaluates_its_body]
      have environments :
          Fin.cases (OpenLambda.termClass term)
            (fun i => OpenLambda.termClass (environment i)) =
          (fun i => OpenLambda.termClass (Fin.cases term environment i)) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [environments, ih]
      apply Eq.symm
      exact (Quotient.sound (OpenLambda.Equality.beta
        (Program.subst (Program.liftSub environment) body) term)).trans
          (congrArg OpenLambda.termClass (beta_after_substitution body environment term))

/-- Evaluating the actual bracket compilation in the canonical algebra yields
the class of the original lambda term, rather than a newly assumed meaning. -/
theorem canonical_meaning (p : OpenLambda.Term 0) :
    OpenLambda.algebra.programMeaning (fun name => OpenLambda.termClass (.coeff name)) p
      Fin.elim0 = OpenLambda.termClass p := by
  have result := meaning_in_term_algebra p Fin.elim0
  have objects : (fun i : Fin 0 => OpenLambda.termClass (Fin.elim0 i)) = Fin.elim0 := by
    funext i; exact Fin.elim0 i
  have variables : (Fin.elim0 : Fin 0 → OpenLambda.Term 0) = Program.var := by
    funext i; exact Fin.elim0 i
  rw [objects] at result
  simpa only [variables, Program.subst_var] using result

def pureAlgebra (A : CombinatoryAlgebra D) : Pure.Interpretation D where
  apply := A.apply
  constantK := A.constant
  constantS := A.distribute

/-- Literal translation from finite K/S syntax to the paper's pure signature. -/
def combinatorTranslation {n : Nat} (variables : Fin n → Pure.Term) :
    CombinatorTerm Nat n → Pure.Term
  | .variable i => variables i
  | .coefficient name => .var name
  | .constant => .constantK
  | .distribute => .constantS
  | .application left right => .app (combinatorTranslation variables left)
      (combinatorTranslation variables right)

theorem combinator_translation_value (A : CombinatoryAlgebra D)
    (coefficient : Nat → D) {n : Nat} (variables : Fin n → Pure.Term)
    (term : CombinatorTerm Nat n) :
    Pure.termValue (pureAlgebra A) coefficient (combinatorTranslation variables term) =
      CombinatorTerm.evaluate A coefficient term
        (fun i => Pure.termValue (pureAlgebra A) coefficient (variables i)) := by
  induction term with
  | «variable» i => rfl
  | coefficient name => rfl
  | constant => rfl
  | distribute => rfl
  | application left right ihl ihr =>
      exact congr (congrArg A.apply ihl) ihr

/-- The fixed translation eliminates all lambda binders by the already checked
K/S bracket algorithm and maps each free name to the same object variable. -/
def translation (p : OpenLambda.Term 0) : Pure.Term :=
  combinatorTranslation Fin.elim0 (CombinatorTerm.fromProgram p)

def equation (left right : OpenLambda.Term 0) : Pure.Formula :=
  .equal (translation left) (translation right)

theorem translation_value (A : CombinatoryAlgebra D) (coefficient : Nat → D)
    (p : OpenLambda.Term 0) :
    Pure.termValue (pureAlgebra A) coefficient (translation p) =
      A.programMeaning coefficient p Fin.elim0 := by
  unfold translation
  rw [combinator_translation_value]
  unfold CombinatoryAlgebra.programMeaning
  congr 1
  funext i
  exact Fin.elim0 i

theorem conversion_makes_equation_true (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) (coefficient : Nat → D)
    {left right : OpenLambda.Term 0} (conversion : OpenLambda.BetaEtaConvertible left right) :
    (equation left right).truth (pureAlgebra A) coefficient := by
  change Pure.termValue (pureAlgebra A) coefficient (translation left) =
    Pure.termValue (pureAlgebra A) coefficient (translation right)
  rw [translation_value, translation_value]
  exact conversion_sound A ext coefficient conversion Fin.elim0

/-- The canonical model supplies the reverse implication for the literal
translated equation. No assumption of syntactic completeness occurs here. -/
theorem canonical_equation_reflects_conversion (left right : OpenLambda.Term 0)
    (same : (equation left right).truth (pureAlgebra OpenLambda.algebra)
      (fun name => OpenLambda.termClass (.coeff name))) :
    OpenLambda.BetaEtaConvertible left right := by
  change Pure.termValue _ _ (translation left) = Pure.termValue _ _ (translation right) at same
  rw [translation_value, translation_value, canonical_meaning, canonical_meaning] at same
  exact (ComputationalAbstraction.canonical_abstraction_exact left right).mp same

/-- Shift every free object variable past one new object binder. -/
def shift : Pure.Term → Pure.Term
  | .var i => .var (i + 1)
  | .constantK => .constantK
  | .constantS => .constantS
  | .app left right => .app (shift left) (shift right)

theorem shift_value (P : Pure.Interpretation D) (assignment : Nat → D)
    (argument : D) (term : Pure.Term) :
    Pure.termValue P (Positive.pushObject assignment argument) (shift term) =
      Pure.termValue P assignment term := by
  induction term with
  | var i => rfl
  | constantK => rfl
  | constantS => rfl
  | app left right ihl ihr => simp only [shift, Pure.termValue, ihl, ihr]

/-- The actual native formula saying that the translated programs agree at
every object input. Shifting keeps the new bound variable fresh. -/
def pointwiseEquation (M N : OpenLambda.Term 0) : Pure.Formula :=
  .forallObject (.equal (.app (shift (translation M)) (.var 0))
    (.app (shift (translation N)) (.var 0)))

theorem pointwise_equation_truth (P : Pure.Interpretation D) (assignment : Nat → D)
    (M N : OpenLambda.Term 0) :
    (pointwiseEquation M N).truth P assignment ↔
      ∀ x, P.apply (Pure.termValue P assignment (translation M)) x =
        P.apply (Pure.termValue P assignment (translation N)) x := by
  change (∀ x, P.apply
    (Pure.termValue P (Positive.pushObject assignment x) (shift (translation M))) x =
    P.apply (Pure.termValue P (Positive.pushObject assignment x) (shift (translation N))) x) ↔ _
  simp only [shift_value]

theorem pointwise_iff_equation (P : Pure.Interpretation D)
    (conditions : Pure.ECAConditions P) (assignment : Nat → D)
    (M N : OpenLambda.Term 0) :
    (pointwiseEquation M N).truth P assignment ↔ (equation M N).truth P assignment := by
  rw [pointwise_equation_truth]
  constructor
  · exact conditions.extensional _ _
  · intro same x
    exact congrArg (fun code => P.apply code x) same

end FregeanECA.LambdaInterpretation

#print axioms FregeanECA.LambdaInterpretation.conversion_sound
#print axioms FregeanECA.LambdaInterpretation.canonical_meaning
#print axioms FregeanECA.LambdaInterpretation.canonical_equation_reflects_conversion
