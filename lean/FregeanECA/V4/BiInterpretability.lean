import FregeanECA.V3.Certificate
import FregeanECA.V3.PaperResults
import FregeanECA.V3.ModelReconstruction
import FregeanECA.Interpretability

/-!
Bi-interpretability of FF (`V3.Cleaner.theory`) and NECA + RC
(`V3.RelationalComprehension.theory`), in the standard sense: two
interpretations whose composites are isomorphic to the identity through
definable isomorphisms, provably in the respective theories.

* `K : FF → NECA + RC` is `Interpretability.translate` (function variables
  become object variables, delta becomes the identity, evaluation becomes
  application).  `M : NECA + RC → FF` is the embedding `p.functional`.
* `K ∘ M` is the identity on every symbol of the algebraic language; only
  variables are renamed.  `double_translation_provability` records that a
  sentence and its double translation are interderivable.
* `M ∘ K` interprets FF in FF with the function sort read as a copy of the
  object sort.  The definable map `f ↦ δ f` is an isomorphism from the
  identity interpretation to this composite exactly when FF proves: it is
  surjective (`coverage`), it is injective and respects function identity
  (`A3`), and it commutes with evaluation (`evaluation`, i.e.
  `f(x) = (δ f)·x`).  Commutation with `δ`, application, `K`, `S` and every
  relation symbol is a syntactic identity.  These three sentences are
  derivable, and `ModelReconstruction.formula_round_trip` is the resulting
  translation lemma in every model.
-/
namespace FregeanECA.V4.BiInterpretability

open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2
open scoped FFL.FirstOrder

universe u v w

/-- Validity of an embedded applicative formula depends only on the
applicative reduct of the structure. -/
theorem valid_functional_iff {D : Type u} {F : Type v} {R : Nat → Type w} [Nonempty F]
    (M : Interpretation D F R) (p : Applicative.Formula) :
    Valid M p.functional ↔
      ∀ (o : Nat → D) (r : Positive.PredicateAssignment R), p.truth M.applicative o r := by
  constructor
  · intro valid o r
    exact (shared_formula_preserves_truth M p o
      (fun _ => Classical.choice inferInstance) r).mp (valid o _ r)
  · intro valid o f r
    exact (shared_formula_preserves_truth M p o f r).mpr (valid o r)

/-- `K ∘ M` is the identity on the algebraic language: an applicative formula
and its double translation are valid in exactly the same functional
structures. -/
theorem double_translation_validity {D : Type u} {F : Type v} {R : Nat → Type w}
    [Nonempty F] (M : Interpretation D F R) (p : Applicative.Formula) :
    Valid M (Interpretability.translate p.functional).functional ↔ Valid M p.functional := by
  have : Nonempty D := ⟨M.applicative.constantK⟩
  exact (Interpretability.translation_validity M p.functional).symm.trans
    ((valid_functional_iff (copyExpansion M.applicative) p).trans
      (valid_functional_iff M p).symm)

/-- The same statement for derivability in NECA + RC. -/
theorem double_translation_provability (p : Applicative.Formula) :
    (V3.RelationalComprehension.theory ⊢
        sentence (Interpretability.translate p.functional).functional) ↔
      (V3.RelationalComprehension.theory ⊢ sentence p.functional) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    have := sorts_of_model h
    refine ⟨M↓[language], h, ?_⟩
    exact (sentence_truth (extractedRealization M) inferInstance (fun _ => inferInstance) _).trans
      ((double_translation_validity (extracted M) p).trans
        (sentence_truth (extractedRealization M) inferInstance (fun _ => inferInstance) _).symm)
  · intro M _ _ _ h
    have := sorts_of_model h
    refine ⟨M↓[language], h, ?_⟩
    exact (sentence_truth (extractedRealization M) inferInstance (fun _ => inferInstance) _).trans
      ((double_translation_validity (extracted M) p).symm.trans
        (sentence_truth (extractedRealization M) inferInstance (fun _ => inferInstance) _).symm)

/-- Surjectivity of `f ↦ δ f`: the coverage sentence. -/
theorem coverage_provable : V3.Cleaner.theory ⊢ sentence coverage :=
  V3.Cleaner.coverage_provable

/-- Injectivity of `f ↦ δ f` and preservation of function identity: A3. -/
theorem injective_abstraction_provable : V3.Cleaner.theory ⊢ sentence V3.Cleaner.A3 :=
  V3.PaperResults.provable_of_valid _ (fun _ h => h _ (Or.inl .a3))

/-- Commutation of `f ↦ δ f` with evaluation: `f(x) = (δ f)·x`. -/
theorem evaluation_provable : V3.Cleaner.theory ⊢ sentence evaluation :=
  V3.PaperResults.provable_of_valid _ (fun _ h => h _ (Or.inr .evaluation))

/-- The translation lemma induced by the isomorphism, in every model of FF. -/
theorem translation_lemma {D F : Type} {R : Nat → Type}
    [Nonempty F] [∀ n, Nonempty (R n)] (M : Interpretation D F R)
    (h : ∀ q, V3.Cleaner.Axiom q → Valid M q) :
    ∃ e : F ≃ D, (∀ f, e f = M.delta f) ∧
      ∀ (p : Formula) (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R),
        p.truth M o f r ↔
          p.truth (copyExpansion M.applicative) o (fun i => e (f i)) r := by
  obtain ⟨tf, fe⟩ := V3.Cleaner.conditions M h
  obtain ⟨e, he, _, tl⟩ := V3.ModelReconstruction.reconstruction M tf fe
  exact ⟨e, he, tl⟩

/-- Bi-interpretability of FF and NECA + RC: the two interpretations transfer
proofs; `K ∘ M` is the identity on the algebraic language; and the definable
map `f ↦ δ f` is, provably in FF, an isomorphism from the identity to
`M ∘ K`, with the induced translation lemma valid in every model. -/
theorem bi_interpretability :
    (∀ p : Functional.Formula, type_of% (V3.Certificate.cleaner_to_algebra p)) ∧
    (∀ p : Applicative.Formula, type_of% (V3.Certificate.algebra_to_cleaner p)) ∧
    (∀ p : Applicative.Formula, type_of% (double_translation_provability p)) ∧
    (V3.Cleaner.theory ⊢ sentence coverage) ∧
    (V3.Cleaner.theory ⊢ sentence V3.Cleaner.A3) ∧
    (V3.Cleaner.theory ⊢ sentence evaluation) ∧
    (∀ {D F : Type} {R : Nat → Type} [Nonempty F] [∀ n, Nonempty (R n)]
      (M : Interpretation D F R) (h : ∀ q, V3.Cleaner.Axiom q → Valid M q),
      type_of% (translation_lemma M h)) :=
  ⟨V3.Certificate.cleaner_to_algebra, V3.Certificate.algebra_to_cleaner,
    double_translation_provability, coverage_provable, injective_abstraction_provable,
    evaluation_provable, fun M h => translation_lemma M h⟩

end FregeanECA.V4.BiInterpretability

#print axioms FregeanECA.V4.BiInterpretability.double_translation_provability
#print axioms FregeanECA.V4.BiInterpretability.bi_interpretability
