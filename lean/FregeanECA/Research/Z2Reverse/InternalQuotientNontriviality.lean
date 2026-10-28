import FregeanECA.Research.Z2Reverse.InternalQuotientAlgebra
import FregeanECA.Research.Z2Reverse.InternalExtensionality
import FregeanECA.Research.Z2Reverse.InternalBetaEtaCommutation
import FregeanECA.Research.Z2Reverse.InternalEtaConfluence

/-!
Concrete separation of free names in the quotient of internal lambda codes.
The proof derives combined Church-Rosser from the two checked confluence
proofs and their checked commutation; numeric path lengths are unrestricted.
-/
namespace FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalLambdaCode InternalLambdaScope InternalParallelBeta InternalEtaReduction
open InternalPaths InternalTermQuotient InternalConversionCongruence InternalQuotientAlgebra
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem beta_confluent (n : V) : InternalCombinedConfluence.Confluent (Parallel n) := by
  intro s left right first second
  exact InternalConfluence.reach_confluent (Parallel n)
    (InternalCombinators.parallel_fo_definable n)
    (fun _ _ _ h₁ h₂ => parallel_diamond h₁ h₂) s left first right second

theorem eta_confluent (n : V) : InternalCombinedConfluence.Confluent (Step n) :=
  fun _ _ _ h₁ h₂ => InternalEtaReduction.eta_confluent h₁ h₂

/-- Church-Rosser for the concrete union, with no confluence assumptions. -/
theorem betaeta_church_rosser (n x y : V)
    (h : Convert (fun a b => Parallel n a b ∨ Step n a b) x y) :
    ∃ common, Reach (fun a b => Parallel n a b ∨ Step n a b) x common ∧
      Reach (fun a b => Parallel n a b ∨ Step n a b) y common :=
  InternalCombinedConfluence.union_conversion_common (Parallel n) (Step n)
    (InternalCombinators.parallel_fo_definable n) (InternalEtaReduction.step_firstOrder_at n)
    (beta_confluent n) (eta_confluent n) (InternalBetaEtaCommutation.commute n) x y h

theorem parallel_fvar_stationary (n i : V) :
    InternalCombinedConfluence.Stationary (Parallel n) (fvar i) := by
  intro t h
  rcases parallel_cases h with ⟨j, _, eq, _⟩ | ⟨j, eq, out⟩ |
    ⟨a, a', b, b', eq, _⟩ | ⟨a, a', eq, _⟩ | ⟨a, a', b, b', eq, _⟩
  · exact False.elim (bvar_ne_fvar j i eq.symm)
  · exact eq.trans out.symm
  · exact False.elim (fvar_ne_app _ _ _ eq)
  · exact False.elim (fvar_ne_lam _ _ eq)
  · exact False.elim (fvar_ne_app _ _ _ eq)

theorem fvar_stationary (n i : V) :
    InternalCombinedConfluence.Stationary
      (InternalCombinedConfluence.Union (Parallel n) (Step n)) (fvar i) := by
  intro t h
  rcases h with hb | he
  · exact parallel_fvar_stationary n i t hb
  · exact False.elim (no_step_fvar n i t he)

/-- Every source-model number remains a distinct free name modulo conversion. -/
theorem free_names_convert_iff (n i j : V) :
    Convert (fun a b => Parallel n a b ∨ Step n a b) (fvar i) (fvar j) ↔ i = j :=
  (InternalCombinedConfluence.union_stationary_conversion_iff (Parallel n) (Step n)
    (InternalCombinators.parallel_fo_definable n) (InternalEtaReduction.step_firstOrder_at n)
    (beta_confluent n) (eta_confluent n) (InternalBetaEtaCommutation.commute n)
    (fvar_stationary n i) (fvar_stationary n j)).trans (fvar_inj i j)

theorem free_names_separated : FreeNamesSeparated (V := V) := by
  intro h
  have impossible : (0 : V) = 1 := (free_names_convert_iff 0 0 1).mp h
  exact zero_ne_one impossible

theorem free_name_decode_injective :
    Function.Injective (fun i : V => conversion.decode (fvar i)) := by
  intro i j same
  apply (free_names_convert_iff 0 i j).mp
  change conversion.relation (fvar i) (fvar j)
  have rel := (conversion.decode_eq_iff (fvar i) (fvar j)).mp same
  simpa only [normalize_of_scoped (fvar i) (isScoped_fvar 0 i),
    normalize_of_scoped (fvar j) (isScoped_fvar 0 j)] using rel

/-- The internally constructed quotient is nontrivial without supplied separation. -/
theorem quotient_nontrivial : ∃ x y : Object (V := V), x ≠ y :=
  nontrivial_of_free_names free_names_separated

/-- All four ECA conditions for the internally constructed quotient, with
no supplied algebra, extensionality or separation hypotheses. -/
theorem eca : Pure.ECAConditions (interpretation (V := V)) :=
  eca_of_codes (fun _ _ hs ht h => InternalExtensionality.extensional hs ht h)
    free_names_separated

end FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality
