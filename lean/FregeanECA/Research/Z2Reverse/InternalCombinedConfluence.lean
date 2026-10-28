import FregeanECA.Research.Z2Reverse.InternalConfluence

/-!
Hindley-Rosen lifting for arithmetic reductions and internally coded paths.
The two component confluence and commutation hypotheses remain explicit.
This module does not assume or assert their lambda-specific instances.
-/

namespace FregeanECA.Research.Z2Reverse.InternalCombinedConfluence

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalPaths InternalConfluence
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def Union (R S : V → V → Prop) (x y : V) : Prop := R x y ∨ S x y

def Block (R S : V → V → Prop) (x y : V) : Prop := Reach R x y ∨ Reach S x y

def Confluent (R : V → V → Prop) : Prop := Diamond (Reach R)

def Commute (R S : V → V → Prop) : Prop :=
  ∀ x y z, Reach R x y → Reach S x z → ∃ w, Reach S y w ∧ Reach R z w

omit [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem union_definable (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S) :
    Language.DefinableRel ℒₒᵣ (Union R S) := Language.Definable.or hR hS

theorem block_definable (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S) :
    Language.DefinableRel ℒₒᵣ (Block R S) :=
  Language.Definable.or (reach_definable R hR) (reach_definable S hS)

/-- Replace every edge of an internally finite path by an internally finite
path. Definable induction supplies the flattened path, even at nonstandard lengths. -/
theorem reach_bind (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S)
    (edges : ∀ x y, R x y → Reach S x y) :
    ∀ x y, Reach R x y → Reach S x y := by
  refine reach_induction R hR (reach_definable S hS) (reach_refl S) ?_
  intro x y z edge rest
  exact reach_trans S hS (edges x y edge) rest

theorem union_into_block {R S : V → V → Prop} {x y : V}
    (h : Union R S x y) : Block R S x y :=
  h.elim (fun h => Or.inl (reach_single h)) (fun h => Or.inr (reach_single h))

theorem block_into_union_reach {R S : V → V → Prop} {x y : V}
    (h : Block R S x y) : Reach (Union R S) x y :=
  h.elim (reach_mono (fun _ _ h => Or.inl h)) (reach_mono (fun _ _ h => Or.inr h))

theorem reach_block_iff (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S)
    (x y : V) : Reach (Block R S) x y ↔ Reach (Union R S) x y := by
  constructor
  · exact reach_bind _ _ (block_definable R S hR hS) (union_definable R S hR hS)
      (fun _ _ => block_into_union_reach) x y
  · exact reach_mono (fun _ _ => union_into_block)

theorem block_diamond (R S : V → V → Prop)
    (cr : Confluent R) (cs : Confluent S) (commute : Commute R S) :
    Diamond (Block R S) := by
  intro x y z left right
  rcases left with left | left <;> rcases right with right | right
  · obtain ⟨w, hy, hz⟩ := cr x y z left right
    exact ⟨w, Or.inl hy, Or.inl hz⟩
  · obtain ⟨w, hy, hz⟩ := commute x y z left right
    exact ⟨w, Or.inr hy, Or.inl hz⟩
  · obtain ⟨w, hz, hy⟩ := commute x z y right left
    exact ⟨w, Or.inl hy, Or.inr hz⟩
  · obtain ⟨w, hy, hz⟩ := cs x y z left right
    exact ⟨w, Or.inr hy, Or.inr hz⟩

theorem union_confluent (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S)
    (cr : Confluent R) (cs : Confluent S) (commute : Commute R S) :
    Confluent (Union R S) := by
  intro x y z left right
  obtain ⟨w, hy, hz⟩ := reach_confluent (Block R S) (block_definable R S hR hS)
    (block_diamond R S cr cs commute) x y ((reach_block_iff R S hR hS x y).mpr left)
    z ((reach_block_iff R S hR hS x z).mpr right)
  exact ⟨w, (reach_block_iff R S hR hS y w).mp hy,
    (reach_block_iff R S hR hS z w).mp hz⟩

theorem union_conversion_common (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S)
    (cr : Confluent R) (cs : Confluent S) (commute : Commute R S)
    (x y : V) (conversion : Convert (Union R S) x y) :
    ∃ w, Reach (Union R S) x w ∧ Reach (Union R S) y w := by
  have blocks : Convert (Block R S) x y :=
    reach_mono (fun _ _ h => h.elim
      (fun h => Or.inl (union_into_block h)) (fun h => Or.inr (union_into_block h))) conversion
  obtain ⟨w, hx, hy⟩ := convert_has_common_reduct (Block R S)
    (block_definable R S hR hS) (block_diamond R S cr cs commute) x y blocks
  exact ⟨w, (reach_block_iff R S hR hS x w).mp hx,
    (reach_block_iff R S hR hS y w).mp hy⟩

/-- This notion allows reflexive parallel-reduction steps. -/
def Stationary (R : V → V → Prop) (x : V) : Prop := ∀ y, R x y → x = y

theorem stationary_reach_eq (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R) :
    ∀ x y, Reach R x y → Stationary R x → x = y := by
  let := hR
  have hP : Language.DefinableRel ℒₒᵣ (fun x y : V => Stationary R x → x = y) := by
    unfold Stationary
    definability
  refine reach_induction R hR hP ?_ ?_
  · intro x _; rfl
  · intro x y z edge ih h
    have same := h y edge
    subst y
    exact ih h

theorem union_stationary_conversion_iff (R S : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (hS : Language.DefinableRel ℒₒᵣ S)
    (cr : Confluent R) (cs : Confluent S) (commute : Commute R S)
    {x y : V} (hx : Stationary (Union R S) x) (hy : Stationary (Union R S) y) :
    Convert (Union R S) x y ↔ x = y := by
  constructor
  · intro h
    obtain ⟨w, fromX, fromY⟩ := union_conversion_common R S hR hS cr cs commute x y h
    exact (stationary_reach_eq _ (union_definable R S hR hS) x w fromX hx).trans
      (stationary_reach_eq _ (union_definable R S hR hS) y w fromY hy).symm
  · rintro rfl
    exact convert_refl _ x

end FregeanECA.Research.Z2Reverse.InternalCombinedConfluence

#print axioms FregeanECA.Research.Z2Reverse.InternalCombinedConfluence.union_confluent
#print axioms FregeanECA.Research.Z2Reverse.InternalCombinedConfluence.union_conversion_common
#print axioms FregeanECA.Research.Z2Reverse.InternalCombinedConfluence.union_stationary_conversion_iff
