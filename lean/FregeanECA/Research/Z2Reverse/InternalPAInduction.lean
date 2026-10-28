import FregeanECA.Research.Z2Reverse.InternalLambdaScope

/-!
First-order definable induction over internal lambda terms in PA models.

The predicate may have arbitrary first-order quantifier complexity and finitely
many parameters from the arithmetic model. Its definability witness is essential:
no induction for arbitrary external predicates on a nonstandard model is assumed.
Term codes, variable indices, and binder depths all range over the model itself.
This module does not establish substitution, confluence, or a reverse interpretation.
-/

namespace FregeanECA.Research.Z2Reverse.InternalPAInduction

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalLambdaCode InternalLambdaScope
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V]

/-- Forgetting a hierarchy bound retains first-order definability. -/
theorem definable_of_hierarchy {k : Nat} {P : (Fin k → V) → Prop}
    {Γ : HierarchySymbol} (hP : Γ.Definable P) : Language.Definable ℒₒᵣ P := by
  rcases hP with ⟨φ, hφ⟩
  exact ⟨φ.val, hφ.df⟩

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- PA induction for any first-order definable predicate, with parameters. -/
@[elab_as_elim] theorem succ_induction {P : V → Prop}
    (hP : Language.DefinablePred ℒₒᵣ P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗣𝗔)
  apply InductionScheme.succ_induction (C := Set.univ) (P := P) ?_ zero succ
  rcases hP with ⟨φ, hφ⟩
  have : Inhabited V := Classical.inhabited_of_nonempty'
  exact ⟨φ.enumerateFVar, (Rew.rewriteMap φ.idxOfFVar) ▹ φ, by trivial, by
    intro x
    simp [Semiformula.eval_rewriteMap, hφ.iff]⟩

/-- Strong induction on the model's arithmetic ordering for definable predicates. -/
@[elab_as_elim] theorem order_induction {P : V → Prop}
    (hP : Language.DefinablePred ℒₒᵣ P)
    (step : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  have hBound : Language.DefinablePred ℒₒᵣ (fun x : V => ∀ y < x, P y) :=
    Language.Definable.all (Language.Definable.imp
      (Language.Definable.lt.retraction ![0, 1]) (hP.retraction ![0]))
  have allBounds : ∀ x : V, ∀ y < x, P y := by
    refine succ_induction (P := fun x : V => ∀ y < x, P y) hBound ?_ ?_
    · simp
    · intro x ih y hy
      rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hy) with hlt | heq
      · exact ih y hlt
      · subst y
        exact step x ih
  intro x
  exact allBounds (x + 1) x (by simp)

/-- Structural induction over all internally finite raw lambda codes.
The proof uses arithmetic strong induction, not external syntax induction. -/
@[elab_as_elim] theorem term_induction {P : V → Prop}
    (hP : Language.DefinablePred ℒₒᵣ P)
    (hb : ∀ i, P (bvar i)) (hf : ∀ i, P (fvar i))
    (hl : ∀ s, IsTerm s → P s → P (lam s))
    (ha : ∀ s t, IsTerm s → IsTerm t → P s → P t → P (app s t)) :
    ∀ t, IsTerm t → P t := by
  have hTerm : Language.DefinablePred ℒₒᵣ (IsTerm (V := V)) :=
    definable_of_hierarchy InternalLambdaCode.term_definable
  refine order_induction (P := fun t => IsTerm t → P t)
    (Language.Definable.imp hTerm hP) ?_
  intro t ih ht
  rcases (InternalLambdaCode.case_iff t).mp ht with
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, u, hs, hu, rfl⟩
  · exact hb i
  · exact hf i
  · exact hl s hs (ih s (body_lt_lam s) hs)
  · exact ha s u hs hu (ih s (left_lt_app s u) hs) (ih u (right_lt_app s u) hu)

/-- Induction with a model-valued binder depth that increases beneath lambda.
The entire relation between depth and term must be first-order definable. -/
theorem scoped_induction {P : V → V → Prop}
    (hP : Language.DefinableRel ℒₒᵣ P)
    (hb : ∀ depth i, i < depth → P depth (bvar i))
    (hf : ∀ depth i, P depth (fvar i))
    (hl : ∀ depth s, IsScoped (depth + 1) s → P (depth + 1) s →
      P depth (lam s))
    (ha : ∀ depth s t, IsScoped depth s → IsScoped depth t →
      P depth s → P depth t → P depth (app s t)) :
    ∀ depth t, IsScoped depth t → P depth t := by
  have hScoped : Language.DefinableRel ℒₒᵣ (IsScoped (V := V)) :=
    definable_of_hierarchy InternalLambdaScope.scoped_definable
  have hAll : Language.DefinablePred ℒₒᵣ
      (fun t => ∀ depth, IsScoped depth t → P depth t) :=
    Language.Definable.all (Language.Definable.imp hScoped hP)
  suffices all : ∀ t, IsTerm t → ∀ depth, IsScoped depth t → P depth t by
    intro depth t ht
    exact all t ht.term depth ht
  refine term_induction (P := fun t => ∀ depth, IsScoped depth t → P depth t)
    hAll ?_ ?_ ?_ ?_
  · intro i depth hi
    exact hb depth i ((isScoped_bvar_iff depth i).mp hi)
  · intro i depth _
    exact hf depth i
  · intro s _ ih depth hs
    have hsBody := (isScoped_lam_iff depth s).mp hs
    exact hl depth s hsBody (ih (depth + 1) hsBody)
  · intro s t _ _ ihs iht depth hst
    obtain ⟨hs, ht⟩ := (isScoped_app_iff depth s t).mp hst
    exact ha depth s t hs ht (ihs depth hs) (iht depth ht)

end FregeanECA.Research.Z2Reverse.InternalPAInduction
