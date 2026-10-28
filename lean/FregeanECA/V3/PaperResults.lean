import FregeanECA.V3.Cleaner
import FregeanECA.V3.RelationalComprehension
import FregeanECA.V3.Specifications

/-! Exact auxiliary statements printed in the V3 manuscript. Semantic proofs
are lifted to Foundation derivability explicitly by first-order completeness.
The inverse is a defined cross-sort operation, not an element of the function
sort and not an extra mathematical axiom. -/
namespace FregeanECA.V3.PaperResults
open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2
open scoped FFL.FirstOrder
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

theorem provable_of_valid (p : Formula)
    (valid : ∀ {D F : Type} {R : Nat → Type}
      [Nonempty F] [∀ n, Nonempty (R n)] (M : Interpretation D F R),
      (∀ q, Cleaner.Axiom q → Valid M q) → Valid M p) :
    Cleaner.theory ⊢ sentence p := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ hM
  have := sorts_of_model hM
  have native := (model_iff_valid (extractedRealization M) Cleaner.Axiom).mp hM
  apply (sentence_truth (extractedRealization M)
    inferInstance (fun _ => inferInstance) p).mpr
  exact valid (extracted M) native

/-- The complete inverse proposition, with the iff and evaluation identity
included explicitly, not only inferred in the paper-to-proof index. -/
theorem inverse (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, Cleaner.Axiom p → Valid M p) :
    ∃ inverse : D → F,
      (∀ x f, inverse x = f ↔ M.delta f = x) ∧
      (∀ f, inverse (M.delta f) = f) ∧
      (∀ x, M.delta (inverse x) = x) ∧
      (∀ x y, M.applicative.apply x y = M.eval (inverse x) y) ∧
      (∀ f x, M.applicative.apply (M.delta f) x = M.eval f x) := by
  obtain ⟨inv, left, right, app⟩ := Cleaner.inverse_application M h
  refine ⟨inv, ?_, left, right, app, ?_⟩
  · intro x f
    constructor
    · intro eq
      exact (congrArg M.delta eq).symm.trans (right x)
    · intro eq
      exact (congrArg inv eq).symm.trans (left f)
  · intro f x
    rw [app, left]

/-- forall x exists f forall g (g=f iff delta g=x). This is the native
sentence authorizing the unique-preimage definition of the inverse. -/
def uniquePreimage : Formula := .forallObject (.existsFunction (.forallFunction
  (iffF (.functionEqual 0 1) (.equal (.delta 0) (.var 0)))))

theorem unique_preimage_provable : Cleaner.theory ⊢ sentence uniquePreimage := by
  apply provable_of_valid
  intro D F R _ _ M h o f r x
  obtain ⟨inv, eqv, _, _, _, _⟩ := inverse M h
  refine ⟨inv x, ?_⟩
  intro g
  apply (iffF_truth M _ _ _ _ _).mpr
  change g = inv x ↔ M.delta g = x
  exact eq_comm.trans (eqv x g)

def pointwiseIdentity : Formula := allFunctions 2
  (iffF (.functionEqual 0 1)
    (.forallObject (.equal (.eval 0 (.var 0)) (.eval 1 (.var 0)))))

def basicLawVAndExtensionality : Formula :=
  .conjunction Cleaner.A3 (.conjunction pointwiseIdentity extensionality)

theorem basic_law_V_and_extensionality_valid (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, Cleaner.Axiom p → Valid M p) :
    Valid M basicLawVAndExtensionality := by
  obtain ⟨full, fe⟩ := Cleaner.conditions M h
  intro o f r
  refine ⟨h _ (Or.inl .a3) o f r, ?_, ?_⟩
  · intro g f'
    apply (iffF_truth M _ _ _ _ _).mpr
    change (f' = g) ↔ (∀ x, M.eval f' x = M.eval g x)
    exact ⟨fun eq x => congrArg (fun k => M.eval k x) eq,
      (functionExtensionality_truth M o f r).mp (fe o f r) f' g⟩
  · apply (extensionality_truth M o f r).mpr
    exact full.toRawTFConditions.application_extensional

/-- The two equivalences and object extensionality printed in prop:blv,
as one actual closed first-order derivability statement. -/
theorem basic_law_V_and_extensionality_provable :
    Cleaner.theory ⊢ sentence basicLawVAndExtensionality :=
  provable_of_valid _ (fun M h => basic_law_V_and_extensionality_valid M h)

/-- Both literal V3 axiom presentations hold in the same concrete open-term
model with all relations and the function-copy expansion. -/
theorem concrete_models :
    (∀ p, Cleaner.Axiom p → Valid openFunctional p) ∧
    (∀ p, RelationalComprehension.Axiom p → Valid openFunctional p) := by
  constructor
  · exact (Cleaner.axioms_iff_fullFE openFunctional).mpr
      (FunctionExtensionality.copy_satisfies_full_FE openSpecification
        openSpecification_satisfies_full_TS)
  · rw [V2.withECA_valid_iff]
    refine ⟨?_, (V2.fc_comprehension_axioms_iff openFunctional).mpr
      openSpecification_satisfies_full_TS.full_comprehension⟩
    apply eca_axioms_of_conditions
    exact ⟨openSpecification_satisfies_full_TS.combinatory.constant,
      openSpecification_satisfies_full_TS.combinatory.distribute,
      openSpecification_satisfies_full_TS.extensional,
      openSpecification_satisfies_full_TS.nontrivial⟩

theorem concrete_encoded_models :
    ∃ M : SmallStruc language,
      M ⊧* Cleaner.theory ∧ M ⊧* RelationalComprehension.theory :=
  ⟨taggedModel openFunctional,
    taggedModel_valid openFunctional Cleaner.Axiom concrete_models.1,
    taggedModel_valid openFunctional RelationalComprehension.Axiom concrete_models.2⟩

/-- All three assertions of the worked specification proposition, including
graph existence without assuming the pre/postcondition hypotheses. -/
theorem specification (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, Cleaner.Axiom p → Valid M p)
    (p q : D) (P Q T : R 0) :
    (∀ x, M.applicative.apply (Specifications.compose M.applicative p q) x =
      M.applicative.apply q (M.applicative.apply p x)) ∧
    (Specifications.meets M.applicative p P Q →
      Specifications.meets M.applicative q Q T →
      Specifications.meets M.applicative (Specifications.compose M.applicative p q) P T) ∧
    ∃ G : R 1,
      (∀ x y, M.applicative.satisfies 1 G (Fin.cases x (fun _ => y)) ↔
        y = M.applicative.apply (Specifications.compose M.applicative p q) x) ∧
      (Specifications.meets M.applicative p P Q →
        Specifications.meets M.applicative q Q T →
        ∀ x y, M.applicative.satisfies 1 G (Fin.cases x (fun _ => y)) →
          Specifications.holds M.applicative P x → Specifications.holds M.applicative T y) := by
  obtain ⟨full, _⟩ := Cleaner.conditions M h
  have ts := full_tf_reduct_satisfies_full_ts full
  refine ⟨Specifications.composition_correct M.applicative ts.combinatory p q,
    Specifications.composition_specification M.applicative ts.combinatory p q P Q T, ?_⟩
  obtain ⟨G, hg⟩ := Specifications.composition_graph M.applicative
    ts.combinatory ts.full_comprehension p q
  refine ⟨G, ?_, ?_⟩
  · intro x y
    simpa only [Specifications.composition_correct M.applicative ts.combinatory] using hg x y
  · intro hp hq x y hxy hx
    rw [(hg x y).mp hxy]
    exact hq _ (hp x hx)

end FregeanECA.V3.PaperResults

#print axioms FregeanECA.V3.PaperResults.inverse
#print axioms FregeanECA.V3.PaperResults.unique_preimage_provable
#print axioms FregeanECA.V3.PaperResults.basic_law_V_and_extensionality_provable
#print axioms FregeanECA.V3.PaperResults.concrete_models
#print axioms FregeanECA.V3.PaperResults.concrete_encoded_models
#print axioms FregeanECA.V3.PaperResults.specification
