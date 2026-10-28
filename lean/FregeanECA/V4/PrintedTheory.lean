import FregeanECA.V3.Cleaner
import FregeanECA.V3.PaperResults
import FregeanECA.V3.Nontriviality

/-!
The theory exactly as printed in the paper: A1, A2, A3 = functional Basic
Law V, A4, A5 = T ≠ F for Church's truth values, together with the same
defining clauses for application and K/S.

`V3.Cleaner` encodes A3 as injective abstraction, ∀f g (δf = δg ↔ f = g), and
A5 as nontriviality, ∃x y (x ≠ y). The paper prints A3 as functional Basic
Law V, ∀f g (δf = δg ↔ ∀x f(x) = g(x)), and A5 as T ≠ F, where T = K and
F = K·I are the abstracts of the two projections. Given A4 the two forms of
A3 are interderivable (the remark after Proposition 2.3); given the K and S
laws the two forms of A5 are interderivable (the remark on A5 in Section
2.4). This module states the printed axiom set literally and proves that it
has exactly the same models (`axioms_iff_cleaner`) and exactly the same
theorems (`provability_iff`) as `V3.Cleaner.theory`. The V4 certificate then
states every endpoint for the printed theory. The one-object countermodel for
the independence of A5 is repeated for the printed axioms.
-/
namespace FregeanECA.V4.Printed

open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2
open scoped FFL.FirstOrder

universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- A3 as printed: functional Basic Law V, ∀f g (δf = δg ↔ ∀x f(x) = g(x)). -/
abbrev A3 : Formula := lawV

/-- Church's truth values in the encoded term language: T = K and
F = K·I with I = S·K·K. -/
def churchTrue : Term := .constantK
def churchFalse : Term :=
  .app .constantK (.app (.app .constantS .constantK) .constantK)

/-- A5 as printed: T ≠ F. -/
def A5 : Formula := notF (.equal churchTrue churchFalse)

/-- The five printed axioms: A1, A2 and A4 are literally those of
`V3.Cleaner`; A3 is functional Basic Law V; A5 is T ≠ F. -/
inductive CoreAxiom : Formula → Prop where
  | a1 (n : Nat) (p : Formula) : CoreAxiom (V3.Cleaner.A1 n p)
  | a2 (n : Nat) (t : V3.Cleaner.ApplicationTerm) : CoreAxiom (V3.Cleaner.A2 n t)
  | a3 : CoreAxiom A3
  | a4 : CoreAxiom V3.Cleaner.A4
  | a5 : CoreAxiom A5

def Axiom (p : Formula) : Prop := CoreAxiom p ∨ V3.Cleaner.DefinitionAxiom p

/-- The printed theory. -/
abbrev theory := Encoded.theory Axiom

/-- The identity combinator I = S·K·K in a model. -/
def identityObject (M : Interpretation D F R) : D :=
  M.applicative.apply (M.applicative.apply M.applicative.constantS M.applicative.constantK)
    M.applicative.constantK

theorem A5_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    A5.truth M o f r ↔
      M.applicative.constantK ≠ M.applicative.apply M.applicative.constantK (identityObject M) :=
  Iff.rfl

/-! ### A3: functional Basic Law V versus injective abstraction -/

/-- Given A4, functional Basic Law V makes abstraction injective. -/
theorem injective_of_lawV (M : Interpretation D F R)
    (lv : Valid M lawV) (ext : Valid M functionExtensionality) :
    Valid M V3.Cleaner.A3 := by
  intro o f r
  have hv := (lawV_truth M o f r).mp (lv o f r)
  have he := (functionExtensionality_truth M o f r).mp (ext o f r)
  apply (V3.Cleaner.A3_truth M o f r).mpr
  intro a b
  exact ⟨fun hab => he a b ((hv a b).mp hab), congrArg M.delta⟩

/-- Given A4, injective abstraction yields functional Basic Law V. -/
theorem lawV_of_injective (M : Interpretation D F R)
    (inj : Valid M V3.Cleaner.A3) (ext : Valid M functionExtensionality) :
    Valid M lawV := by
  intro o f r
  have hi := (V3.Cleaner.A3_truth M o f r).mp (inj o f r)
  have he := (functionExtensionality_truth M o f r).mp (ext o f r)
  apply (lawV_truth M o f r).mpr
  intro a b
  constructor
  · intro eqd
    have eqf := (hi a b).mp eqd
    subst eqf
    exact fun _ => rfl
  · intro pointwise
    exact congrArg M.delta (he a b pointwise)

/-! ### A5: distinct truth values versus nontriviality -/

/-- T ≠ F exhibits two distinct objects. -/
theorem nontriviality_of_A5 (M : Interpretation D F R) (h : Valid M A5) :
    Valid M nontriviality := by
  intro o f r
  exact (nontriviality_truth M o f r).mpr ⟨_, _, (A5_truth M o f r).mp (h o f r)⟩

/-- Given the K and S laws, two distinct objects force T ≠ F: if K = K·I then
every x equals K·x·y = (K·I)·x·y = I·y = y. -/
theorem A5_of_nontriviality (M : Interpretation D F R)
    (hn : Valid M nontriviality) (hk : Valid M kLaw) (hs : Valid M sLaw) :
    Valid M A5 := by
  intro o f r
  apply (A5_truth M o f r).mpr
  intro heq
  obtain ⟨a, b, hab⟩ := (nontriviality_truth M o f r).mp (hn o f r)
  have k := (kLaw_truth M o f r).mp (hk o f r)
  have s := (sLaw_truth M o f r).mp (hs o f r)
  apply hab
  have step : M.applicative.apply (M.applicative.apply M.applicative.constantK a) b =
      M.applicative.apply (M.applicative.apply
        (M.applicative.apply M.applicative.constantK (identityObject M)) a) b := by
    rw [← heq]
  calc a = M.applicative.apply (M.applicative.apply M.applicative.constantK a) b := (k a b).symm
    _ = M.applicative.apply (M.applicative.apply
          (M.applicative.apply M.applicative.constantK (identityObject M)) a) b := step
    _ = M.applicative.apply (identityObject M) b := by rw [k]
    _ = M.applicative.apply (M.applicative.apply M.applicative.constantK b)
          (M.applicative.apply M.applicative.constantK b) := s _ _ _
    _ = b := k _ _

/-! ### Same models, same theorems -/

/-- The printed core axioms imply the encoded ones (no defining clause is
needed in this direction). -/
theorem core_to_cleaner (M : Interpretation D F R)
    (h : ∀ p, CoreAxiom p → Valid M p) : ∀ p, V3.Cleaner.CoreAxiom p → Valid M p := by
  intro p hp
  cases hp with
  | a1 n body => exact h _ (.a1 n body)
  | a2 n t => exact h _ (.a2 n t)
  | a3 => exact injective_of_lawV M (h _ .a3) (h _ .a4)
  | a4 => exact h _ .a4
  | a5 => exact nontriviality_of_A5 M (h _ .a5)

/-- The printed axiom set and the encoded one have the same models. -/
theorem axioms_iff_cleaner (M : Interpretation D F R) :
    (∀ p, Axiom p → Valid M p) ↔ (∀ p, V3.Cleaner.Axiom p → Valid M p) := by
  constructor
  · intro h p hp
    rcases hp with hp | hp
    · exact core_to_cleaner M (fun q hq => h q (Or.inl hq)) p hp
    · exact h _ (Or.inr hp)
  · intro h p hp
    rcases hp with hp | hp
    · cases hp with
      | a1 n body => exact h _ (Or.inl (.a1 n body))
      | a2 n t => exact h _ (Or.inl (.a2 n t))
      | a3 => exact lawV_of_injective M (h _ (Or.inl .a3)) (h _ (Or.inl .a4))
      | a4 => exact h _ (Or.inl .a4)
      | a5 =>
          exact A5_of_nontriviality M (h _ (Or.inl .a5)) (h _ (Or.inr .k)) (h _ (Or.inr .s))
    · exact h _ (Or.inr hp)

/-- Every sentence of the encoded language is derivable from the printed
theory exactly when it is derivable from `V3.Cleaner.theory`. -/
theorem provability_iff (σ : Sentence language) :
    (theory ⊢ σ) ↔ (V3.Cleaner.theory ⊢ σ) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    have := sorts_of_model h
    have native := (model_iff_valid (extractedRealization M) V3.Cleaner.Axiom).mp h
    exact ⟨M↓[language], (model_iff_valid (extractedRealization M) Axiom).mpr
      ((axioms_iff_cleaner (extracted M)).mpr native), Iff.rfl⟩
  · intro M _ _ _ h
    have := sorts_of_model h
    have native := (model_iff_valid (extractedRealization M) Axiom).mp h
    exact ⟨M↓[language], (model_iff_valid (extractedRealization M) V3.Cleaner.Axiom).mpr
      ((axioms_iff_cleaner (extracted M)).mp native), Iff.rfl⟩

theorem consistency_iff :
    Entailment.Consistent theory ↔ Entailment.Consistent V3.Cleaner.theory := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr (provability_iff (⊥ : Sentence language))

/-- The printed A3 is derivable (it is an axiom); recorded for the
bi-interpretability certificate, where A3 is one of the isomorphism sentences. -/
theorem lawV_provable : theory ⊢ sentence A3 :=
  (provability_iff _).mpr
    (V3.PaperResults.provable_of_valid _ (fun M h =>
      lawV_of_injective M (h _ (Or.inl .a3)) (h _ (Or.inl .a4))))

/-! ### Independence of A5 from the printed A1–A4 -/

inductive FirstFour : Formula → Prop where
  | a1 (n : Nat) (p : Formula) : FirstFour (V3.Cleaner.A1 n p)
  | a2 (n : Nat) (t : V3.Cleaner.ApplicationTerm) : FirstFour (V3.Cleaner.A2 n t)
  | a3 : FirstFour A3
  | a4 : FirstFour V3.Cleaner.A4

def FirstFourAxiom (p : Formula) : Prop := FirstFour p ∨ V3.Cleaner.DefinitionAxiom p
abbrev firstFourTheory := Encoded.theory FirstFourAxiom

theorem singleton_satisfies_first_four :
    ∀ p, FirstFourAxiom p → Valid V3.Nontriviality.model p := by
  intro p hp
  rcases hp with hp | hp
  · cases hp with
    | a1 n body =>
        exact V3.Nontriviality.singleton_satisfies_first_four _ (Or.inl (.a1 n body))
    | a2 n t =>
        exact V3.Nontriviality.singleton_satisfies_first_four _ (Or.inl (.a2 n t))
    | a3 =>
        intro o f r
        apply (lawV_truth V3.Nontriviality.model o f r).mpr
        exact fun _ _ => ⟨fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    | a4 =>
        exact V3.Nontriviality.singleton_satisfies_first_four _ (Or.inl .a4)
  · exact V3.Nontriviality.singleton_satisfies_first_four _ (Or.inr hp)

/-- In the one-object structure T = F. -/
theorem singleton_refutes_A5 : ¬ Valid V3.Nontriviality.model A5 := by
  intro h
  exact (A5_truth V3.Nontriviality.model (fun _ => ()) (fun _ => ()) (fun _ _ _ => False)).mp
    (h _ _ _) (Subsingleton.elim _ _)

/-- `prop:nontriviality`: the one-object structure satisfies the printed
A1–A4 and the defining clauses, and refutes the printed A5. -/
theorem countermodel :
    (∀ p, FirstFourAxiom p → Valid V3.Nontriviality.model p) ∧
      ¬ Valid V3.Nontriviality.model A5 :=
  ⟨singleton_satisfies_first_four, singleton_refutes_A5⟩

/-- `prop:nontriviality`: the printed A5 is not derivable from the printed A1–A4. -/
theorem A5_not_provable : ¬ (firstFourTheory ⊢ sentence A5) := by
  intro proof
  have satisfies :=
    taggedModel_valid V3.Nontriviality.model FirstFourAxiom singleton_satisfies_first_four
  have truth := Theory.Proof.sound proof satisfies
  exact singleton_refutes_A5 ((taggedModel_truth V3.Nontriviality.model A5).mp truth)

end FregeanECA.V4.Printed

#print axioms FregeanECA.V4.Printed.provability_iff
#print axioms FregeanECA.V4.Printed.consistency_iff
#print axioms FregeanECA.V4.Printed.A5_not_provable
