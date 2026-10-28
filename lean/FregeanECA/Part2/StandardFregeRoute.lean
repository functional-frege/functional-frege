import FregeanECA.Part2.FregeArithmeticTranslation
import FregeanECA.Part2.FregeArithmeticTheorem

/-! The standard Frege theorem instantiated in the actual Part II
interpretation of Frege Arithmetic. This does not reuse Z2 proof transfer.
The explicit encoded Z2 endpoint is a further stage of this route. -/

namespace FregeanECA.Part2.StandardFregeRoute
open Positive Arithmetic FregeArithmeticInterpretation
universe u v
variable {D : Type u} {R : Nat → Type v}

/-- Part II's interpreted HP structure satisfies the standard Fregean
relational Peano laws, with Fregean zero and successor. -/
theorem interpreted_frege_peano (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N) :
    FregeArithmetic.FregePeanoLaws (interpretedModel M full domain)
      (interpreted_full_comprehension M full domain) :=
  FregeArithmetic.hume_implies_frege_peano _ (interpreted_full_conditions M full domain)

/-- The source number domain and all HP premises are constructed from the
actual Part II axioms. No Fregean Peano-law premise is assumed. -/
theorem part_two_has_frege_peano (M : Positive.Interpretation D R)
    (full : FullTSConditions M) :
    ∃ N : R 0, ∃ domain : PeanoDomain M N,
      FregeArithmetic.FregePeanoLaws
        (interpretedModel M full.full_comprehension domain)
        (interpreted_full_comprehension M full.full_comprehension domain) := by
  obtain ⟨N, domain⟩ := full_ts_has_peano_domain M full
  exact ⟨N, domain, interpreted_frege_peano M full.full_comprehension domain⟩

end FregeanECA.Part2.StandardFregeRoute

#print axioms FregeanECA.Part2.StandardFregeRoute.part_two_has_frege_peano
