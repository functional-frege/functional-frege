import FregeanECA.Research.Z2Reverse.InternalPaths

/-!
Diamond lifting and Church-Rosser for internally coded paths in PA models.

The only reduction hypothesis is a one-step diamond. Confluence is derived
using first-order definable induction over numeric path certificates, including
certificates of nonstandard length. This is generic infrastructure: the local
diamond for a particular lambda reduction still has to be proved separately.
-/

namespace FregeanECA.Research.Z2Reverse.InternalConfluence

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalPAInduction InternalPaths
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def Diamond (R : V → V → Prop) : Prop :=
  ∀ source left right, R source left → R source right →
    ∃ common, R left common ∧ R right common

/-- Move one edge past an internally finite path, leaving one edge on its far side. -/
theorem strip (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    (diamond : Diamond R) :
    ∀ source right, Reach R source right → ∀ left, R source left →
      ∃ common, Reach R left common ∧ R right common := by
  let := hR
  let := reach_definable R hR
  have hInvariant : Language.DefinableRel ℒₒᵣ (fun source right : V =>
      ∀ left, R source left → ∃ common, Reach R left common ∧ R right common) :=
    by definability
  refine reach_induction R hR hInvariant ?_ ?_
  · intro source left edge
    exact ⟨left, reach_refl R left, edge⟩
  · intro source next right edge ih left first
    obtain ⟨corner, fromLeft, fromNext⟩ := diamond source left next first edge
    obtain ⟨common, fromCorner, fromRight⟩ := ih corner fromNext
    exact ⟨common, reach_trans R hR (reach_single fromLeft) fromCorner, fromRight⟩

/-- A local diamond implies confluence for all internally finite numeric paths. -/
theorem reach_confluent (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    (diamond : Diamond R) :
    ∀ source left, Reach R source left → ∀ right, Reach R source right →
      ∃ common, Reach R left common ∧ Reach R right common := by
  let := reach_definable R hR
  have hInvariant : Language.DefinableRel ℒₒᵣ (fun source left : V =>
      ∀ right, Reach R source right →
        ∃ common, Reach R left common ∧ Reach R right common) := by definability
  refine reach_induction R hR hInvariant ?_ ?_
  · intro source right path
    exact ⟨right, path, reach_refl R right⟩
  · intro source next left edge ih right path
    obtain ⟨corner, fromNext, fromRight⟩ := strip R hR diamond source right path next edge
    obtain ⟨common, fromLeft, fromCorner⟩ := ih corner fromNext
    exact ⟨common, fromLeft, reach_trans R hR (reach_single fromRight) fromCorner⟩

/-- An internally finite zigzag has a common reduct, derived from the local diamond. -/
theorem convert_has_common_reduct (R : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (diamond : Diamond R) :
    ∀ left right, Convert R left right →
      ∃ common, Reach R left common ∧ Reach R right common := by
  let := reach_definable R hR
  have hInvariant : Language.DefinableRel ℒₒᵣ (fun left right : V =>
      ∃ common, Reach R left common ∧ Reach R right common) := by definability
  refine reach_induction (fun a b => R a b ∨ R b a)
    (symmetric_step_definable R hR) hInvariant ?_ ?_
  · intro x
    exact ⟨x, reach_refl R x, reach_refl R x⟩
  · intro left middle right edge ih
    obtain ⟨common, fromMiddle, fromRight⟩ := ih
    rcases edge with forward | backward
    · exact ⟨common, reach_trans R hR (reach_single forward) fromMiddle, fromRight⟩
    · obtain ⟨joined, fromLeft, fromCommon⟩ :=
        reach_confluent R hR diamond middle left (reach_single backward) common fromMiddle
      exact ⟨joined, fromLeft, reach_trans R hR fromRight fromCommon⟩

theorem conversion_iff_common_reduct (R : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (diamond : Diamond R) (left right : V) :
    Convert R left right ↔ ∃ common, Reach R left common ∧ Reach R right common := by
  constructor
  · exact convert_has_common_reduct R hR diamond left right
  · rintro ⟨common, fromLeft, fromRight⟩
    have leftConversion : Convert R left common :=
      reach_mono (fun _ _ h => Or.inl h) fromLeft
    have rightConversion : Convert R right common :=
      reach_mono (fun _ _ h => Or.inl h) fromRight
    exact convert_trans R hR leftConversion (convert_symm R hR rightConversion)

def Normal (R : V → V → Prop) (x : V) : Prop := ∀ y, ¬ R x y

/-- A normal vertex has no nontrivial coded forward path. -/
theorem normal_reach_eq {R : V → V → Prop} {x y : V}
    (normal : Normal R x) (path : Reach R x y) : x = y := by
  obtain ⟨code, cert⟩ := path
  rcases nil_or_adjoin code with rfl | ⟨a, tail, rfl⟩
  · exact False.elim (cert.nonempty rfl)
  · have hx : a = x := by simpa using cert.head
    subst a
    rcases certificate_adjoin_cases cert with ⟨_, same⟩ | ⟨edge, _⟩
    · exact same
    · exact False.elim (normal _ edge)

/-- Distinct normal vertices cannot be joined by an internally finite conversion. -/
theorem normal_forms_convert_iff (R : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) (diamond : Diamond R)
    {left right : V} (leftNormal : Normal R left) (rightNormal : Normal R right) :
    Convert R left right ↔ left = right := by
  constructor
  · intro conversion
    obtain ⟨common, fromLeft, fromRight⟩ :=
      convert_has_common_reduct R hR diamond left right conversion
    exact (normal_reach_eq leftNormal fromLeft).trans (normal_reach_eq rightNormal fromRight).symm
  · rintro rfl
    exact convert_refl R left

end FregeanECA.Research.Z2Reverse.InternalConfluence
