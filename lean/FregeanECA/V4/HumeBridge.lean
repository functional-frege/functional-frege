import FregeanECA.V3.Cleaner
import FregeanECA.V3.RelationalComprehension
import FregeanECA.V2.Theorems
import FregeanECA.Part2.HumeInternal
import FregeanECA.Part2.FregeArithmeticProofTransfer
import FregeanECA.Part2.Hume

/-!
Hume's Principle on the number domain, transferred to the literal V3/V4
theories: FF in its encoded presentation (`V3.Cleaner.theory`; the V4
certificate restates every result for the printed A1--A6) and NECA + RC
(`V3.RelationalComprehension.theory`).

The underlying results were proved for the inherited Part II presentations
(`Part2.fullFunctionalTheory`, `Part2.fullAlgebraTheory`). The bridges used
here are the already certified provability equivalences
`V3.Cleaner.provability_iff_fullFE`,
`FunctionExtensionality.original_proof_in_extension`,
`V3.RelationalComprehension.closure_provability` and
`V2.combined_full_original_provability`. No new mathematical axiom and no
new model construction is introduced in this file.
-/
namespace FregeanECA.V4.HumeBridge

open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2
open scoped FFL.FirstOrder

/-- `thm:hume` for FF: the closed sentence `exists N (Nat(N) and UC_N and HP_N)`
is derivable from FF (encoded presentation). -/
theorem internal_hume_cleaner :
    V3.Cleaner.theory ⊢ sentence HumeInternal.internalHumeSentence.functional :=
  (V3.Cleaner.provability_iff_fullFE _).mpr
    (FunctionExtensionality.original_proof_in_extension _
      HumeInternal.internal_hume_provable_fregean)

/-- `thm:hume` for NECA + RC. -/
theorem internal_hume_algebra :
    V3.RelationalComprehension.theory ⊢
      sentence HumeInternal.internalHumeSentence.functional :=
  (V3.RelationalComprehension.closure_provability _).mpr
    ((V2.combined_full_original_provability _).mpr
      HumeInternal.internal_hume_provable)

/-- `cor:frege-theorem` for FF: every Z2 proof transfers through the fixed
Hume-route translation `FregeArithmeticProofTransfer.interpret`. -/
theorem via_hume_Z2_to_cleaner (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    V3.Cleaner.theory ⊢ sentence (FregeArithmeticProofTransfer.interpret p).functional :=
  (V3.Cleaner.provability_iff_fullFE _).mpr
    (FunctionExtensionality.original_proof_in_extension _
      (FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer_fregean p proof))

/-- `cor:frege-theorem` for NECA + RC. -/
theorem via_hume_Z2_to_algebra (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    V3.RelationalComprehension.theory ⊢
      sentence (FregeArithmeticProofTransfer.interpret p).functional :=
  (V3.RelationalComprehension.closure_provability _).mpr
    ((V2.combined_full_original_provability _).mpr
      (FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer p proof))

/-- `prop:hume-expansion`: the full-relation model on the carrier `Nat`
satisfies the encoded FF axioms (`V3.Cleaner.Axiom`) and NECA + RC, and its cardinality
map obeys Hume's Principle on the entire object domain. -/
theorem whole_domain_hume_model :
    (∀ p, V3.Cleaner.Axiom p → Valid Hume.functional p) ∧
    (∀ p, V3.RelationalComprehension.Axiom p → Valid Hume.functional p) ∧
    ∀ P Q : Hume.Relation 0,
      Hume.relationNumber P = Hume.relationNumber Q ↔ Hume.ModelEquinumerous P Q := by
  obtain ⟨ts, _, hp⟩ := Hume.part_two_has_hume_expansion
  refine ⟨?_, ?_, hp⟩
  · exact (V3.Cleaner.axioms_iff_fullFE Hume.functional).mpr
      (FunctionExtensionality.copy_satisfies_full_FE Hume.specification ts)
  · rw [V2.withECA_valid_iff]
    refine ⟨?_, (V2.fc_comprehension_axioms_iff Hume.functional).mpr ts.full_comprehension⟩
    apply eca_axioms_of_conditions
    exact ⟨ts.combinatory.constant, ts.combinatory.distribute, ts.extensional, ts.nontrivial⟩

end FregeanECA.V4.HumeBridge

#print axioms FregeanECA.V4.HumeBridge.internal_hume_cleaner
#print axioms FregeanECA.V4.HumeBridge.internal_hume_algebra
#print axioms FregeanECA.V4.HumeBridge.via_hume_Z2_to_cleaner
#print axioms FregeanECA.V4.HumeBridge.via_hume_Z2_to_algebra
#print axioms FregeanECA.V4.HumeBridge.whole_domain_hume_model
