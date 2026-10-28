import FregeanECA.Research.Z2Reverse.InternalCombinedConfluence

/-! Lift a strong mixed fork to commutation of internally finite paths.
Both inductions use first-order definability and numeric path certificates.
The concrete mixed fork remains an explicit premise. -/

namespace FregeanECA.Research.Z2Reverse.InternalCommutationLift
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalPaths InternalCombinedConfluence
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def StrongFork (R S : V → V → Prop) : Prop :=
  ∀ x y z, R x y → S x z → ∃ w, Reach S y w ∧ R z w

theorem edge_against_path (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S)
    (fork : StrongFork R S) :
    ∀ x z, Reach S x z → ∀ y, R x y → ∃ w, Reach S y w ∧ R z w := by
  let := hR
  let := reach_definable S hS
  have hP : Language.DefinableRel ℒₒᵣ
      (fun x z : V => ∀ y, R x y → ∃ w, Reach S y w ∧ R z w) := by definability
  refine reach_induction S hS hP ?_ ?_
  · intro x y edge
    exact ⟨y, reach_refl S y, edge⟩
  · intro x z z' first ih y edge
    obtain ⟨corner, fromY, fromZ⟩ := fork x y z edge first
    obtain ⟨common, fromCorner, fromEnd⟩ := ih corner fromZ
    exact ⟨common, reach_trans S hS fromY fromCorner, fromEnd⟩

theorem commute_of_strongFork (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S)
    (fork : StrongFork R S) : Commute R S := by
  let := reach_definable R hR
  let := reach_definable S hS
  have hP : Language.DefinableRel ℒₒᵣ
      (fun x y : V => ∀ z, Reach S x z → ∃ w, Reach S y w ∧ Reach R z w) := by definability
  have all : ∀ x y, Reach R x y → ∀ z, Reach S x z →
      ∃ w, Reach S y w ∧ Reach R z w := by
    refine reach_induction R hR hP ?_ ?_
    · intro x z path
      exact ⟨z, path, reach_refl R z⟩
    · intro x y y' first ih z path
      obtain ⟨corner, fromY, fromZ⟩ := edge_against_path R S hR hS fork x z path y first
      obtain ⟨common, fromEnd, fromCorner⟩ := ih corner fromY
      exact ⟨common, fromEnd, reach_trans R hR (reach_single fromZ) fromCorner⟩
  intro x y z left right
  exact all x y left z right

end FregeanECA.Research.Z2Reverse.InternalCommutationLift
