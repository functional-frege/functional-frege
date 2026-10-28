import FregeanECA.Research.Z2Reverse.ArithmeticLanguage
import FregeanECA.Research.Z2Reverse.NativeOrder

/-!
The native arithmetic reduct of a Z2 model satisfies Foundation's actual
PA-minus axioms and complete induction scheme. Thus the existing arithmetic
coding library can be used without assuming that the number carrier is Nat.
This arithmetic reduct theorem does not by itself interpret the target ECA.
-/

namespace FregeanECA.Research.Z2Reverse.ArithmeticLanguage

open FFL FFL.FirstOrder ArithmeticModel
universe u v
variable {N : Type u} {S : Type v}
variable (A : ArithmeticStructure N S) (model : ModelsZ2 A) (sets : Nat → S)

include model sets

/-- Every literal PA-minus axiom is obtained from the source Z2 model. -/
theorem models_paMinus :
    letI := oRingStructure A
    N↓[ℒₒᵣ] ⊧* Arithmetic.PeanoMinus := by
  let := oRingStructure A
  have zero_def : (0 : N) = A.zero := rfl
  have one_def : (1 : N) = A.successor A.zero := rfl
  have add_def : ∀ x y : N, x + y = A.add x y := fun _ _ => rfl
  have mul_def : ∀ x y : N, x * y = A.multiply x y := fun _ _ => rfl
  have lt_def : ∀ x y : N, (x < y) ↔ strictOrder A x y := fun _ _ => Iff.rfl
  constructor
  intro sentence ax
  cases ax with
  | equal p hp =>
      have equality : N↓[ℒₒᵣ] ⊧* (Theory.eqAxiom ℒₒᵣ) := inferInstance
      exact models_theory_iff.mp equality _ hp
  | addZero => simpa [models_iff, zero_def, add_def] using add_zero_right A model sets
  | addAssoc => simpa [models_iff, add_def] using add_assoc A model sets
  | addComm => simpa [models_iff, add_def] using add_comm A model sets
  | addEqOfLt =>
      simpa [models_iff, add_def, lt_def] using
        (fun x y (h : strictOrder A x y) => add_eq_of_lt A model sets h)
  | zeroLe =>
      simpa [models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT, zero_def, lt_def]
        using zero_le A model sets
  | zeroLtOne => simpa [models_iff, zero_def, one_def, lt_def] using zero_lt_one A model sets
  | oneLeOfZeroLt =>
      simpa [models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT, zero_def, one_def, lt_def]
        using one_le_of_zero_lt A model sets
  | addLtAdd =>
      simpa [models_iff, add_def, lt_def] using
        (fun x y z (h : strictOrder A x y) => strictOrder_add_right A model sets z h)
  | mulZero => simpa [models_iff, mul_def, zero_def] using multiply_zero_right A model sets
  | mulOne => simpa [models_iff, mul_def, one_def] using multiply_one_right A model sets
  | mulAssoc => simpa [models_iff, mul_def] using multiply_assoc A model sets
  | mulComm => simpa [models_iff, mul_def] using multiply_comm A model sets
  | mulLtMul => simpa [models_iff, mul_def, zero_def, lt_def] using strictOrder_mul_right A model sets
  | distr => simpa [models_iff, mul_def, add_def] using multiply_add_right A model sets
  | ltIrrefl => simpa [models_iff, lt_def] using strictOrder_irrefl A model sets
  | ltTrans =>
      simpa [models_iff, lt_def] using
        (fun x y z (xy : strictOrder A x y) (yz : strictOrder A y z) =>
          strictOrder_trans A model sets xy yz)
  | ltTri => simpa [models_iff, lt_def] using strictOrder_trichotomy A model sets

/-- The actual Foundation PA theory holds on this arbitrary source number
carrier, using the full induction scheme established by syntax translation. -/
theorem models_pa :
    letI := oRingStructure A
    N↓[ℒₒᵣ] ⊧* Arithmetic.Peano := by
  let := oRingStructure A
  exact Semantics.ModelsSet.union_iff.mpr
    ⟨models_paMinus A model sets, models_inductionScheme A model sets⟩

/-- In particular, Foundation's internally coded arithmetic development has
its required I-sigma-one model hypothesis on the same source carrier. -/
theorem models_iSigmaOne :
    letI := oRingStructure A
    N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := by
  let := oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.Peano := models_pa A model sets
  infer_instance

end FregeanECA.Research.Z2Reverse.ArithmeticLanguage
