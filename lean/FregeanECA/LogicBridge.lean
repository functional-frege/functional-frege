import Foundation.FirstOrder.Completeness.CounterModel

/-!
# From concrete model constructions to first-order proofs

These helpers use Foundation's actual classical first-order sequent calculus,
soundness, and completeness.  They do not define provability as validity.
The input theories must be sets of concrete first-order sentences.  In
particular, applying them to a many-sorted theory still requires its guarded
encoding and the corresponding model construction and truth lemma.

Dependency: FormalizedFormalLogic/Foundation,
commit 81810b9f22c49fbb32bd89c1e9737059d83a37e6.
-/

namespace FregeanECA.LogicBridge

open FFL FFL.FirstOrder
open scoped FFL.FirstOrder

universe u v

variable {L₁ L₂ : Language.{u}}
variable {T : Theory L₁} {U : Theory L₂}
variable {φ : Sentence L₁} {ψ : Sentence L₂}

/-- A model lift preserving a particular sentence transfers an actual proof.
The direction is contravariant: every target model supplies a source model. -/
theorem provable_of_model_lift
    (lift : ∀ M : SmallStruc L₂, M ⊧* U →
      ∃ N : SmallStruc L₁, N ⊧* T ∧ (N ⊧ φ ↔ M ⊧ ψ))
    (proof : T ⊢ φ) : U ⊢ ψ := by
  apply Theory.Proof.small_complete
  intro M hM
  obtain ⟨N, hN, truth⟩ := lift M hM
  exact truth.mp (Theory.Proof.sound_small proof hN)

/-- Two concrete model lifts give equivalence of first-order provability.
The translations and lifts remain explicit proof obligations. -/
theorem provable_iff_of_model_lifts
    (forward : ∀ M : SmallStruc L₂, M ⊧* U →
      ∃ N : SmallStruc L₁, N ⊧* T ∧ (N ⊧ φ ↔ M ⊧ ψ))
    (backward : ∀ N : SmallStruc L₁, N ⊧* T →
      ∃ M : SmallStruc L₂, M ⊧* U ∧ (M ⊧ ψ ↔ N ⊧ φ)) :
    (T ⊢ φ) ↔ (U ⊢ ψ) :=
  ⟨provable_of_model_lift forward, provable_of_model_lift backward⟩

/-- Model expansions and reducts preserve every sentence in the designated
source language, hence give syntactic conservativity for that translation. -/
theorem conservative_of_model_expansions
    (translate : Sentence L₁ → Sentence L₂)
    (reduct : ∀ M : SmallStruc L₂, M ⊧* U →
      ∃ N : SmallStruc L₁, N ⊧* T ∧
        ∀ σ : Sentence L₁, (N ⊧ σ ↔ M ⊧ translate σ))
    (expand : ∀ N : SmallStruc L₁, N ⊧* T →
      ∃ M : SmallStruc L₂, M ⊧* U ∧
        ∀ σ : Sentence L₁, (M ⊧ translate σ ↔ N ⊧ σ)) :
    ∀ σ : Sentence L₁, (T ⊢ σ) ↔ (U ⊢ translate σ) := by
  intro σ
  apply provable_iff_of_model_lifts
  · intro M hM
    obtain ⟨N, hN, truth⟩ := reduct M hM
    exact ⟨N, hN, truth σ⟩
  · intro N hN
    obtain ⟨M, hM, truth⟩ := expand N hN
    exact ⟨M, hM, truth σ⟩

/-- Equality of concrete model classes entails equality of provable sentences
in a fixed language. -/
theorem provable_iff_of_same_models {V : Theory L₁}
    (models : ∀ M : SmallStruc L₁, (M ⊧* T ↔ M ⊧* V)) :
    (T ⊢ φ) ↔ (V ⊢ φ) := by
  apply provable_iff_of_model_lifts
  · intro M hM
    exact ⟨M, (models M).mpr hM, Iff.rfl⟩
  · intro M hM
    exact ⟨M, (models M).mp hM, Iff.rfl⟩

/-- For a target theory proving the equality axioms, Foundation's equality
completeness theorem restricts the lift to models whose equality is genuine
carrier equality.  Its quotient-model construction is reused here. -/
theorem provable_of_eq_model_lift [L₂.Eq] [𝗘𝗤 L₂ ⪯ U]
    (lift : ∀ (M : Type u) [Nonempty M] [Structure L₂ M]
      [Structure.Eq L₂ M], M↓[L₂] ⊧* U →
      ∃ N : SmallStruc L₁, N ⊧* T ∧ (N ⊧ φ ↔ M↓[L₂] ⊧ ψ))
    (proof : T ⊢ φ) : U ⊢ ψ := by
  apply Theory.Proof.complete_on_eq_models.{u, 0} ψ
  intro M _ _ _ hM
  obtain ⟨N, hN, truth⟩ := lift M hM
  exact truth.mp (Theory.Proof.sound_small proof hN)

/-- Bidirectional proof transfer using only genuine-equality models on each
side; both theories must prove their language's equality axioms. -/
theorem provable_iff_of_eq_model_lifts
    [L₁.Eq] [L₂.Eq] [𝗘𝗤 L₁ ⪯ T] [𝗘𝗤 L₂ ⪯ U]
    (forward : ∀ (M : Type u) [Nonempty M] [Structure L₂ M]
      [Structure.Eq L₂ M], M↓[L₂] ⊧* U →
      ∃ N : SmallStruc L₁, N ⊧* T ∧ (N ⊧ φ ↔ M↓[L₂] ⊧ ψ))
    (backward : ∀ (N : Type u) [Nonempty N] [Structure L₁ N]
      [Structure.Eq L₁ N], N↓[L₁] ⊧* T →
      ∃ M : SmallStruc L₂, M ⊧* U ∧ (M ⊧ ψ ↔ N↓[L₁] ⊧ φ)) :
    (T ⊢ φ) ↔ (U ⊢ ψ) :=
  ⟨provable_of_eq_model_lift forward, provable_of_eq_model_lift backward⟩

/-- A supplied nonempty structure satisfying a concrete theory excludes an
LK proof of contradiction.  No consistency assumption is an input. -/
theorem consistent_of_structure
    (M : Struc.{v, u} L₁) (satisfies : M ⊧* T) :
    Entailment.Consistent T :=
  Theory.consistent_of_satisfiable ⟨M, satisfies⟩

/-- The same endpoint in the explicit `not provable false` form. -/
theorem no_proof_of_falsum_of_structure
    (M : Struc.{v, u} L₁) (satisfies : M ⊧* T) :
    T ⊬ (⊥ : Sentence L₁) :=
  Entailment.consistent_iff_unprovable_bot.mp
    (consistent_of_structure M satisfies)

end FregeanECA.LogicBridge
