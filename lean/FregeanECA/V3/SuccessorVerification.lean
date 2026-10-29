import FregeanECA.V3.PaperResults
import FregeanECA.Part2.ArithmeticInterpretation
import FregeanECA.LambdaInterpretation

/-! The literal worked program, a checked companion example that is no longer
printed in the paper: translate lambda x. k (k x),
substitute K for the free name k, identify its composition code, and prove
its specification on the available least inductive number relation. -/
namespace FregeanECA.V3.SuccessorVerification
open FFL FFL.FirstOrder Functional Axioms Guarded Part2
open scoped FFL.FirstOrder
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- The free name 0 is k; the bound index 0 is x. -/
def twiceLambda : Frege.OpenLambda.Term 0 :=
  .lam (.app (.coeff 0) (.app (.coeff 0) (.var 0)))

/-- Capture-free object-term substitution [K/k], with k indexed by 0. -/
def substituteK : Pure.Term → Pure.Term
  | .var i => if i = 0 then .constantK else .var i
  | .constantK => .constantK
  | .constantS => .constantS
  | .app p q => .app (substituteK p) (substituteK q)

def code : Pure.Term := substituteK (LambdaInterpretation.translation twiceLambda)

theorem substitution_value (M : Pure.Interpretation D) (objects : Nat → D)
    (t : Pure.Term) :
    Pure.termValue M objects (substituteK t) =
      Pure.termValue M (fun i => if i = 0 then M.constantK else objects i) t := by
  induction t with
  | var i => simp only [substituteK]; split <;> simp_all [Pure.termValue]
  | constantK => rfl
  | constantS => rfl
  | app p q hp hq => simp only [substituteK, Pure.termValue, hp, hq]

/-- The displayed beta equation concerns the actual fixed bracket translation,
not an independently selected object with the desired behavior. -/
theorem code_application (M : Positive.Interpretation D R)
    (laws : Positive.CombinatoryLaws M) (objects : Nat → D) (x : D) :
    M.apply (Pure.termValue M.pure objects code) x =
      M.apply M.constantK (M.apply M.constantK x) := by
  unfold code
  rw [substitution_value]
  change laws.algebra.apply
    (Pure.termValue (LambdaInterpretation.pureAlgebra laws.algebra)
      (fun i => if i = 0 then M.constantK else objects i)
      (LambdaInterpretation.translation twiceLambda)) x = _
  rw [LambdaInterpretation.translation_value]
  simp only [twiceLambda, Frege.CombinatoryAlgebra.every_program_binder_evaluates_its_body,
    Frege.CombinatoryAlgebra.meaning_of_an_application,
    Frege.CombinatoryAlgebra.meaning_of_a_coefficient,
    Frege.CombinatoryAlgebra.meaning_of_a_variable, Fin.cases_zero]
  rfl

theorem code_is_composition (M : Positive.Interpretation D R)
    (laws : Positive.CombinatoryLaws M)
    (ext : ∀ a b, (∀ x, M.apply a x = M.apply b x) → a = b)
    (objects : Nat → D) :
    Pure.termValue M.pure objects code = Specifications.compose M M.constantK M.constantK := by
  apply ext
  intro x
  rw [code_application M laws, Specifications.composition_correct M laws]

/-- The exact worked derivation, for any available relation satisfying the
paper's definition of N. The triple is obtained using the composition rule. -/
theorem verifies (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, Cleaner.Axiom p → Valid M p)
    (objects : Nat → D) (N : R 0)
    (natural : Arithmetic.RepresentsLeast M.applicative N) :
    Pure.termValue M.applicative.pure objects code =
      Specifications.compose M.applicative M.applicative.constantK M.applicative.constantK ∧
    Specifications.meets M.applicative (Pure.termValue M.applicative.pure objects code) N N ∧
    ∀ n, Specifications.holds M.applicative N n →
      Specifications.holds M.applicative N
        (M.applicative.apply (Pure.termValue M.applicative.pure objects code) n) ∧
      M.applicative.apply (Pure.termValue M.applicative.pure objects code) n =
        Arithmetic.modelSuccessor M.applicative (Arithmetic.modelSuccessor M.applicative n) := by
  obtain ⟨full, _⟩ := Cleaner.conditions M h
  have ts := full_tf_reduct_satisfies_full_ts full
  have identity := code_is_composition M.applicative ts.combinatory ts.extensional objects
  have one : Specifications.meets M.applicative M.applicative.constantK N N :=
    (Arithmetic.represented_least_is_inductive M.applicative natural).2
  have two := Specifications.composition_specification M.applicative ts.combinatory
    M.applicative.constantK M.applicative.constantK N N N one one
  rw [← identity] at two
  refine ⟨identity, two, ?_⟩
  intro n hn
  exact ⟨two n hn, code_application M.applicative ts.combinatory objects n⟩

/-- A1 supplies the actual available N used by the verified example. -/
theorem available_domain (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, Cleaner.Axiom p → Valid M p) (objects : Nat → D) :
    ∃ N : R 0, Arithmetic.RepresentsLeast M.applicative N ∧
      Specifications.meets M.applicative (Pure.termValue M.applicative.pure objects code) N N := by
  obtain ⟨full, _⟩ := Cleaner.conditions M h
  obtain ⟨N, domain⟩ := Arithmetic.full_ts_has_peano_domain M.applicative
    (full_tf_reduct_satisfies_full_ts full)
  exact ⟨N, domain.represents_least, (verifies M h objects N domain.represents_least).2.1⟩

def specificationFormula : Applicative.Formula :=
  .implies ArithmeticInterpretation.naturalDefinition
    (.forallObject (.implies (Arithmetic.unary 0 (.var 0))
      (.conjunction (Arithmetic.unary 0 (.app code (.var 0)))
        (.equal (.app code (.var 0))
          (Arithmetic.successorTerm (Arithmetic.successorTerm (.var 0)))))))

def codeIdentity : Pure.Formula :=
  .equal code (.app (.app .constantS (.app .constantK .constantK)) .constantK)

theorem code_identity_provable : Cleaner.theory ⊢ sentence codeIdentity.functional := by
  apply PaperResults.provable_of_valid
  intro D F R _ _ M h objects functions predicates
  apply (pure_functional_embedding_preserves_truth M codeIdentity objects functions predicates).mpr
  obtain ⟨full, _⟩ := Cleaner.conditions M h
  have ts := full_tf_reduct_satisfies_full_ts full
  exact code_is_composition M.applicative ts.combinatory ts.extensional objects

/-- Actual universally closed Foundation derivability, in addition to the
native model-level worked derivation. N remains guarded by its definition. -/
theorem specification_provable :
    Cleaner.theory ⊢ sentence specificationFormula.functional := by
  apply PaperResults.provable_of_valid
  intro D F R _ _ M h objects functions predicates
  apply (shared_formula_preserves_truth M specificationFormula objects functions predicates).mpr
  intro natural n hn
  have natural' := (ArithmeticInterpretation.natural_definition_truth
    M.applicative objects predicates).mp natural
  have result := (verifies M h (Positive.pushObject objects n) (predicates 0 0) natural').2.2 n hn
  simpa only [Applicative.Formula.truth, Arithmetic.unary, Positive.Term.value,
    Positive.pushObject, Arithmetic.successorTerm, Arithmetic.modelSuccessor,
    Specifications.holds, pure_term_preserves_value] using result

end FregeanECA.V3.SuccessorVerification

#print axioms FregeanECA.V3.SuccessorVerification.verifies
#print axioms FregeanECA.V3.SuccessorVerification.available_domain
#print axioms FregeanECA.V3.SuccessorVerification.code_identity_provable
#print axioms FregeanECA.V3.SuccessorVerification.specification_provable
