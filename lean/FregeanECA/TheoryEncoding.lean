import FregeanECA.GuardedModels
import FregeanECA.LogicBridge
import FregeanECA.AxiomsSpecification

/-! Concrete axiom sets in Foundation's first-order sequent calculus. -/
namespace FregeanECA.Encoded
open FFL FFL.FirstOrder
open Guarded

def theory (axioms : Functional.Formula → Prop) : Theory language :=
  Theory.eqAxiom language ∪ sortTheory ∪ {σ | ∃ p, axioms p ∧ sentence p = σ}

instance equalityIncluded (axioms : Functional.Formula → Prop) :
    Theory.eqAxiom language ⪯ theory axioms :=
  Entailment.Axiomatized.le_of_subset (fun _ h => Or.inl (Or.inl h))

theorem sorts_of_model {M : Type u} [Nonempty M] [Structure language M]
    {axioms : Functional.Formula → Prop} (h : M↓[language] ⊧* theory axioms) :
    SortCorrect M :=
  models_sortTheory_iff.mp ⟨fun {p} hp => h.models _ (Or.inl (Or.inr hp))⟩

theorem model_iff_valid {D : Type u} {F : Type v} {R : Nat → Type w}
    {M : Type z} [Nonempty M] [Structure language M] [Structure.Eq language M]
    [SortCorrect M] [Nonempty F] [∀ n, Nonempty (R n)]
    {typed : Functional.Interpretation D F R} (real : Realization typed M)
    (axioms : Functional.Formula → Prop) :
    M↓[language] ⊧* theory axioms ↔ ∀ p, axioms p → Axioms.Valid typed p := by
  constructor
  · intro h p hp
    exact (sentence_truth real inferInstance (fun _ => inferInstance) p).mp
      (h.models _ (Or.inr ⟨p, hp, rfl⟩))
  · intro h
    refine ⟨?_⟩
    intro p hp
    rcases hp with (he | hs) | ⟨q, hq, rfl⟩
    · exact (inferInstance : M↓[language] ⊧* Theory.eqAxiom language).models _ he
    · exact (models_sortTheory_iff.mpr (inferInstance : SortCorrect M)).models _ hs
    · exact (sentence_truth real inferInstance (fun _ => inferInstance) q).mpr (h q hq)

noncomputable def taggedModel {D F : Type} {R : Nat → Type}
    [Nonempty D] [Nonempty F] (typed : Functional.Interpretation D F R) :
    SmallStruc language :=
  @Structure.toStruc language (Tagged D F R) inferInstance (taggedStructure typed)

theorem taggedModel_valid {D F : Type} {R : Nat → Type}
    [Nonempty D] [Nonempty F] [∀ n, Nonempty (R n)]
    (typed : Functional.Interpretation D F R) (axioms : Functional.Formula → Prop)
    (h : ∀ p, axioms p → Axioms.Valid typed p) :
    taggedModel typed ⊧* theory axioms := by
  letI := taggedStructure typed
  letI := tagged_equality typed
  letI := tagged_sortCorrect typed
  exact (model_iff_valid (taggedRealization typed) axioms).mpr h

theorem taggedModel_truth {D F : Type} {R : Nat → Type}
    [Nonempty D] [Nonempty F] [∀ n, Nonempty (R n)]
    (typed : Functional.Interpretation D F R) (p : Functional.Formula) :
    taggedModel typed ⊧ sentence p ↔ Axioms.Valid typed p := by
  letI := taggedStructure typed
  exact sentence_truth (taggedRealization typed) inferInstance (fun _ => inferInstance) p

theorem same_validity_same_proofs (axioms other : Functional.Formula → Prop)
    (same : ∀ {D F : Type} {R : Nat → Type}
      [Nonempty F] [∀ n, Nonempty (R n)] (typed : Functional.Interpretation D F R),
      (∀ p, axioms p → Axioms.Valid typed p) ↔
      (∀ p, other p → Axioms.Valid typed p)) (σ : Sentence language) :
    (theory axioms ⊢ σ) ↔ (theory other ⊢ σ) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    letI := sorts_of_model h
    have hm := (model_iff_valid (extractedRealization M) other).mp h
    refine ⟨M↓[language], ?_, Iff.rfl⟩
    exact (model_iff_valid (extractedRealization M) axioms).mpr ((same (extracted M)).mpr hm)
  · intro M _ _ _ h
    letI := sorts_of_model h
    have hm := (model_iff_valid (extractedRealization M) axioms).mp h
    refine ⟨M↓[language], ?_, Iff.rfl⟩
    exact (model_iff_valid (extractedRealization M) other).mpr ((same (extracted M)).mp hm)

end FregeanECA.Encoded
