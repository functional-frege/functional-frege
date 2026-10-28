import FregeanECA.Part2.FregeArithmeticRecursion
import FregeanECA.Part2.ArithmeticEncoding

/-! The standard Frege route from generic HP and full source comprehension
to every Z2 axiom and the validity of every actual Z2 proof. The former
adapter-comprehension obligation is discharged by an explicit source-language
graph translation. No earlier Z2_proof_transfer theorem or ECA-derived
Peano-domain construction is invoked. Conditional interfaces remain below
for inspecting the composition. -/

namespace FregeanECA.Part2.FregeArithmeticZ2
open FFL FFL.FirstOrder
universe u v
variable {D : Type u} {R : Nat → Type v}

noncomputable def arithmetic_given_comprehension
    (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (comprehension : HasFullComprehension (FregeArithmeticRecursion.model M full)) :
    Arithmetic.FullArithmetic (FregeArithmeticRecursion.model M full)
      (FregeArithmeticRecursion.naturalPredicate M full) :=
  Classical.choice (FregeArithmeticRecursion.arithmetic_of_adapter_comprehension M full comprehension)

/-- Every ordinary Z2 axiom, including full comprehension and extensionality,
holds on the HP-derived number carrier once adapter comprehension is supplied. -/
theorem all_axioms_given_comprehension
    (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (comprehension : HasFullComprehension (FregeArithmeticRecursion.model M full)) :
    ∀ p, SecondOrderArithmetic.Axiom p →
      SecondOrderArithmetic.Valid
        (SecondOrderArithmetic.arithmeticOperations (arithmetic_given_comprehension M full comprehension)) p :=
  SecondOrderArithmetic.all_axioms_valid _ comprehension

/-- This uses the actual Foundation proof relation of Z2; the conclusion is
truth of its fixed arithmetic interpretation, not an assumed soundness rule. -/
theorem proof_truth_given_comprehension
    (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (comprehension : HasFullComprehension (FregeArithmeticRecursion.model M full))
    (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    SecondOrderArithmetic.Valid
      (SecondOrderArithmetic.arithmeticOperations (arithmetic_given_comprehension M full comprehension)) p :=
  ArithmeticEncoding.arithmetic_proof_truth _ comprehension p proof

/-- Arithmetic operations on the HP-derived carrier, with all adapter
comprehension and graph-availability obligations discharged. -/
noncomputable def arithmetic
    (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) :
    Arithmetic.FullArithmetic (FregeArithmeticRecursion.model M full)
      (FregeArithmeticRecursion.naturalPredicate M full) :=
  arithmetic_given_comprehension M full (FregeArithmeticRecursion.model_has_full_comprehension M full)

/-- Generic HP plus full comprehension interprets every Z2 axiom, including
its full comprehension scheme, on the standard Frege-number domain. -/
theorem hume_implies_Z2_axioms
    (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) :
    ∀ p, SecondOrderArithmetic.Axiom p →
      SecondOrderArithmetic.Valid (SecondOrderArithmetic.arithmeticOperations (arithmetic M full)) p :=
  all_axioms_given_comprehension M full (FregeArithmeticRecursion.model_has_full_comprehension M full)

/-- Every actual Foundation Z2 proof is true in the interpretation built
inside any generic HP model. The only model hypotheses are HP and full
comprehension in the specified source grammar. -/
theorem hume_proof_truth
    (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    SecondOrderArithmetic.Valid (SecondOrderArithmetic.arithmeticOperations (arithmetic M full)) p :=
  proof_truth_given_comprehension M full
    (FregeArithmeticRecursion.model_has_full_comprehension M full) p proof

/-- The preceding construction is also an actual model of the encoded Z2
theory, rather than only a collection of informal arithmetic operations. -/
theorem hume_constructs_Z2_model
    (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) :
    ArithmeticEncoding.taggedModel (SecondOrderArithmetic.arithmeticOperations (arithmetic M full))
      ⊧* ArithmeticEncoding.theory :=
  ArithmeticEncoding.arithmetic_taggedModel_valid (arithmetic M full)
    (FregeArithmeticRecursion.model_has_full_comprehension M full)

end FregeanECA.Part2.FregeArithmeticZ2
