import FregeanECA.Research.Z2Reverse.InternalCombinators
import FregeanECA.Research.Z2Reverse.InternalEtaPaths

/-!
Congruence of internally coded beta-eta conversion and its concrete quotient
interface. Confluence and nontriviality are not prerequisites for congruence;
they remain separate obligations when constructing the nontrivial ECA model.
-/
namespace FregeanECA.Research.Z2Reverse.InternalConversionCongruence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalLambdaCode InternalLambdaScope InternalParallelBeta InternalEtaReduction
open InternalPaths InternalTermQuotient
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem union_definable (n : V) : Language.DefinableRel ℒₒᵣ
    (fun s t => Parallel n s t ∨ Step n s t) := by
  apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
  definability

theorem map_convert (R S : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    (hS : Language.DefinableRel ℒₒᵣ S) (f : V → V)
    (hf : Language.DefinableFunction₁ ℒₒᵣ f)
    (edge : ∀ x y, R x y → S (f x) (f y))
    {x y : V} (h : Convert R x y) : Convert S (f x) (f y) :=
  map_reach _ _ (symmetric_step_definable R hR) (symmetric_step_definable S hS)
    f hf (fun _ _ h => h.elim (fun h => Or.inl (edge _ _ h))
      (fun h => Or.inr (edge _ _ h))) x y h

theorem convert_app_left {n s t q : V}
    (h : Convert (fun a b => Parallel n a b ∨ Step n a b) s t) (hq : IsScoped n q) :
    Convert (fun a b => Parallel n a b ∨ Step n a b) (app s q) (app t q) := by
  apply map_convert _ _ (union_definable n) (union_definable n) (fun a => app a q) ?_ ?_ h
  · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
  · intro a b edge
    rcases edge with hb | he
    · exact Or.inl (hb.app (Parallel.refl n q hq))
    · exact Or.inr (he.app_left hq)

theorem convert_app_right {n s t q : V}
    (h : Convert (fun a b => Parallel n a b ∨ Step n a b) s t) (hq : IsScoped n q) :
    Convert (fun a b => Parallel n a b ∨ Step n a b) (app q s) (app q t) := by
  apply map_convert _ _ (union_definable n) (union_definable n) (fun a => app q a) ?_ ?_ h
  · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
  · intro a b edge
    rcases edge with hb | he
    · exact Or.inl ((Parallel.refl n q hq).app hb)
    · exact Or.inr (he.app_right hq)

theorem convert_app_congr {n s s' t t' : V}
    (hs : Convert (fun a b => Parallel n a b ∨ Step n a b) s s')
    (ht : Convert (fun a b => Parallel n a b ∨ Step n a b) t t')
    (hs' : IsScoped n s') (ht0 : IsScoped n t) :
    Convert (fun a b => Parallel n a b ∨ Step n a b) (app s t) (app s' t') :=
  convert_trans _ (union_definable n) (convert_app_left hs ht0) (convert_app_right ht hs')

theorem convert_lam {n s t : V}
    (h : Convert (fun a b => Parallel (n + 1) a b ∨ Step (n + 1) a b) s t) :
    Convert (fun a b => Parallel n a b ∨ Step n a b) (lam s) (lam t) := by
  apply map_convert _ _ (union_definable _) (union_definable _) InternalLambdaCode.lam ?_ ?_ h
  · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
  · intro a b edge
    exact edge.elim (fun h => Or.inl h.lam) (fun h => Or.inr h.lam)

/-- The concrete numeric conversion relation required by the term quotient. -/
def conversion : InternalTermQuotient.Conversion V where
  relation := Convert (fun a b => Parallel 0 a b ∨ Step 0 a b)
  equivalence := convert_equivalence _ (union_definable 0)
  app_congr := fun _ _ _ _ _ hs' ht _ h₁ h₂ => convert_app_congr h₁ h₂ hs' ht

theorem K_convert (x y : V) (hx : IsScoped 0 x) (hy : IsScoped 0 y) :
    conversion.relation (app (app constantK x) y) x :=
  reach_mono (fun _ _ h => Or.inl (Or.inl h)) (InternalCombinators.K_reduces x y hx hy)

theorem S_convert (x y z : V) (hx : IsScoped 0 x) (hy : IsScoped 0 y) (hz : IsScoped 0 z) :
    conversion.relation (app (app (app constantS x) y) z) (app (app x z) (app y z)) :=
  reach_mono (fun _ _ h => Or.inl (Or.inl h)) (InternalCombinators.S_reduces x y z hx hy hz)


/-- The concrete K equation descends to the quotient. -/
theorem quotient_K (x y : (conversion (V := V)).Object) :
    conversion.application (conversion.application (conversion.decode constantK) x) y = x := by
  refine Quotient.inductionOn x ?_
  intro x
  refine Quotient.inductionOn y ?_
  intro y
  apply Quotient.sound
  change conversion.relation (app (app (normalize constantK) x.val) y.val) x.val
  rw [normalize_of_scoped constantK constantK_scoped]
  exact K_convert x.val y.val x.property y.property

/-- The concrete S equation descends to the quotient. -/
theorem quotient_S (x y z : (conversion (V := V)).Object) :
    conversion.application (conversion.application (conversion.application
      (conversion.decode constantS) x) y) z =
    conversion.application (conversion.application x z) (conversion.application y z) := by
  refine Quotient.inductionOn x ?_
  intro x
  refine Quotient.inductionOn y ?_
  intro y
  refine Quotient.inductionOn z ?_
  intro z
  apply Quotient.sound
  change conversion.relation (app (app (app (normalize constantS) x.val) y.val) z.val)
    (app (app x.val z.val) (app y.val z.val))
  rw [normalize_of_scoped constantS constantS_scoped]
  exact S_convert x.val y.val z.val x.property y.property z.property

end FregeanECA.Research.Z2Reverse.InternalConversionCongruence
