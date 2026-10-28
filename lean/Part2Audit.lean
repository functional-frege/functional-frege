import FregeanECA.Part2.Models
import FregeanECA.Part2.Arithmetic
import FregeanECA.Part2.ArithmeticFromFull
import FregeanECA.Part2.Theorems
import FregeanECA.Part2.Consequences
import FregeanECA.Part2.ArithmeticInterpretation
import FregeanECA.Part2.GeneratedRelations
import FregeanECA.Part2.ArithmeticGraphs
import FregeanECA.Part2.OracleCountermodel
import FregeanECA.ComputationalAbstraction
import FregeanECA.Part2.Hume
import FregeanECA.Certificate
import FregeanECA.Part2.HumeCounting
import FregeanECA.Part2.ArithmeticModelInterpretation
import FregeanECA.Certificates.PartOne
import FregeanECA.Certificates.PartTwo
import FregeanECA.Certificates.HumeRoute
import FregeanECA.Part2.HumeFinite
import FregeanECA.Part2.HumeBijections

-- Full classical relation comprehension and its exact closure schema.
#print axioms FregeanECA.Part2.classical_closure_iff_full_comprehension
#print axioms FregeanECA.Part2.full_comprehension_implies_classical_closure

-- Concrete full-schema models; computational A2 has not been enlarged.
#print axioms FregeanECA.Part2.fullRelations_comprehend_all_formulas
#print axioms FregeanECA.Part2.copyExpansion_comprehends_all_functional_formulas
#print axioms FregeanECA.Part2.duplicateExpansion_comprehends_all_functional_formulas
#print axioms FregeanECA.Part2.fullRelations_satisfies_full_TS
#print axioms FregeanECA.Part2.copyExpansion_satisfies_full_TF
#print axioms FregeanECA.Part2.duplicateExpansion_satisfies_full_TF
#print axioms FregeanECA.Part2.openSpecification_satisfies_full_TS
#print axioms FregeanECA.Part2.openFunctional_satisfies_full_TF
#print axioms FregeanECA.Part2.openDuplicate_satisfies_full_TF
#print axioms FregeanECA.Part2.full_comprehension_has_a_model_without_FE
#print axioms FregeanECA.Part2.full_comprehension_excludes_unrestricted_predicate_representation

-- The least inductive domain; complete arithmetic endpoints follow below.
#print axioms FregeanECA.Part2.Arithmetic.successor_injective
#print axioms FregeanECA.Part2.Arithmetic.zero_not_successor
#print axioms FregeanECA.Part2.Arithmetic.numeral_injective
#print axioms FregeanECA.Part2.Arithmetic.least_inductive_formula_truth
#print axioms FregeanECA.Part2.Arithmetic.least_inductive_domain
#print axioms FregeanECA.Part2.Arithmetic.represented_formula_induction
#print axioms FregeanECA.Part2.Arithmetic.peano_domain_checkpoint
#print axioms FregeanECA.Part2.Arithmetic.full_comprehension_supplies_least_instance
#print axioms FregeanECA.Part2.Arithmetic.positive_closure_supplies_unary_intersections
#print axioms FregeanECA.Part2.Arithmetic.full_ts_has_peano_domain
#print axioms FregeanECA.Part2.Arithmetic.open_specification_has_peano_domain

-- Literal classical comprehension and C/Q schemas, model correspondence,
-- Foundation LK proof equivalence, and the single-model consistency route.
#print axioms FregeanECA.Part2.fullRelationalComprehension_truth
#print axioms FregeanECA.Part2.full_functional_axioms_iff_conditions
#print axioms FregeanECA.Part2.full_relational_axioms_iff_conditions
#print axioms FregeanECA.Part2.algebra_axioms_iff_conditions
#print axioms FregeanECA.Part2.full_applicative_implies_full_copy
#print axioms FregeanECA.Part2.full_tf_reduct_satisfies_full_ts
#print axioms FregeanECA.Part2.full_ts_expansion_satisfies_full_tf
#print axioms FregeanECA.Part2.algebra_comprehension_provability
#print axioms FregeanECA.Part2.full_functional_algebra_provability
#print axioms FregeanECA.Part2.full_functional_proof_interprets
#print axioms FregeanECA.Part2.full_consistency_equivalence
#print axioms FregeanECA.Part2.full_algebra_model
#print axioms FregeanECA.Part2.full_algebra_consistent
#print axioms FregeanECA.Part2.full_functional_consistent
#print axioms FregeanECA.Part2.full_neither_theory_proves_false

-- Complete arithmetic graph construction, full source syntax, and actual
-- Foundation proof transfer under the canonical arithmetic interpretation.
#print axioms FregeanECA.Part2.Arithmetic.full_has_least_addition
#print axioms FregeanECA.Part2.Arithmetic.addition_inversion
#print axioms FregeanECA.Part2.Arithmetic.addition_total_unique
#print axioms FregeanECA.Part2.Arithmetic.full_has_least_multiplication
#print axioms FregeanECA.Part2.Arithmetic.multiplication_inversion
#print axioms FregeanECA.Part2.Arithmetic.multiplication_total_unique
#print axioms FregeanECA.Part2.Arithmetic.full_ts_has_arithmetic
#print axioms FregeanECA.Part2.SecondOrderArithmetic.Formula.translation_preserves_truth
#print axioms FregeanECA.Part2.SecondOrderArithmetic.source_formula_comprehension
#print axioms FregeanECA.Part2.SecondOrderArithmetic.source_formula_induction
#print axioms FregeanECA.Part2.SecondOrderArithmetic.all_axioms_valid
#print axioms FregeanECA.Part2.SecondOrderArithmetic.full_ts_interprets_all_Z2_axioms
#print axioms FregeanECA.Part2.SecondOrderArithmetic.open_specification_interprets_all_Z2_axioms
#print axioms FregeanECA.Part2.SecondOrderArithmetic.guarded_translation_of_valid
#print axioms FregeanECA.Part2.ArithmeticEncoding.sentence_truth
#print axioms FregeanECA.Part2.ArithmeticEncoding.arithmetic_taggedModel_valid
#print axioms FregeanECA.Part2.ArithmeticEncoding.arithmetic_proof_truth
#print axioms FregeanECA.Part2.ArithmeticInterpretation.definitions_truth
#print axioms FregeanECA.Part2.ArithmeticInterpretation.definitions_exist
#print axioms FregeanECA.Part2.ArithmeticInterpretation.Z2_proof_transfer
#print axioms FregeanECA.Part2.ArithmeticInterpretation.Z2_proof_transfer_fregean
#print axioms FregeanECA.Part2.ArithmeticInterpretation.interpretation_preserves_falsum

-- Generated relation expressions independently satisfy the literal B+C axioms.
#print axioms FregeanECA.Part2.Generated.open_satisfies_literal_complemented_axioms

-- The concrete first-order-definable countermodel below also refutes Q.
#print axioms FregeanECA.Part2.Generated.specification_with_complements
#print axioms FregeanECA.Part2.Generated.satisfies_literal_complemented_axioms

-- Preservation of Part I and the displayed external consistency implication.
#print axioms FregeanECA.Part2.preserves_part_one_functional
#print axioms FregeanECA.Part2.preserves_part_one_algebraic
#print axioms FregeanECA.Part2.full_relative_consistency

-- Actual coded syntax, finite available tables, and the unconditional
-- ECA+B1--B5+C countermodel to predicate projection.
#print axioms FregeanECA.Part2.NaturalECA.natural_extensional_combinatory_algebra
#print axioms FregeanECA.Part2.Oracle.fixedPoint_truth
#print axioms FregeanECA.Part2.Oracle.no_relation_correct_on_sentence_codes
#print axioms FregeanECA.Part2.Oracle.finite_definable_tables_correct
#print axioms FregeanECA.Part2.Oracle.satisfactionMatrix_truth
#print axioms FregeanECA.Part2.Oracle.exists_definable_tables_iff
#print axioms FregeanECA.Part2.Oracle.target_satisfaction_on_sentence_codes
#print axioms FregeanECA.Part2.Oracle.definable_model_fails_predicate_projection
#print axioms FregeanECA.Part2.Oracle.definable_model_fails_full_comprehension
#print axioms FregeanECA.Part2.Oracle.complemented_specification_without_predicate_projection
#print axioms FregeanECA.Part2.Oracle.literal_complemented_specification_without_predicate_projection

-- Exact canonical computational abstraction; open inputs, not a theory-level
-- equation completeness or observational-equivalence assertion.
#print axioms FregeanECA.ComputationalAbstraction.range_equality_iff_same_values
#print axioms FregeanECA.ComputationalAbstraction.canonical_abstraction_exact
#print axioms FregeanECA.ComputationalAbstraction.beta_eta_iff_same_values
#print axioms FregeanECA.ComputationalAbstraction.beta_eta_iff_same_values_on_terms
#print axioms FregeanECA.ComputationalAbstraction.canonical_fregean_ranges_exact

-- Hume's Principle as an explicit full-model expansion by a new cross-sort
-- abstraction; binary bijection witnesses belong to the model's relation sort.
#print axioms FregeanECA.Part2.Hume.equinumerous_iff_equiv
#print axioms FregeanECA.Part2.Hume.humes_principle
#print axioms FregeanECA.Part2.Hume.model_equinumerous_iff
#print axioms FregeanECA.Part2.Hume.model_humes_principle
#print axioms FregeanECA.Part2.Hume.every_bijection_graph_is_available
#print axioms FregeanECA.Part2.Hume.part_two_has_hume_expansion

-- Single readable certificate, including the exact scope of both additions.
#print axioms FregeanECA.Certificate.canonical_computation
#print axioms FregeanECA.Certificate.hume_model_expansion
#print axioms FregeanECA.Certificate.checked_certificate

-- Genuine Part II pure-language conservativity and actual Foundation
-- provability of the fixed translated equation iff beta-eta conversion.
#print axioms FregeanECA.Part2.bare_eca_full_algebra_provability
#print axioms FregeanECA.Part2.bare_eca_full_functional_provability
#print axioms FregeanECA.LambdaInterpretation.meaning_rename
#print axioms FregeanECA.LambdaInterpretation.meaning_subst
#print axioms FregeanECA.LambdaInterpretation.conversion_sound
#print axioms FregeanECA.LambdaInterpretation.canonical_meaning
#print axioms FregeanECA.LambdaInterpretation.translation_value
#print axioms FregeanECA.LambdaInterpretation.canonical_equation_reflects_conversion
#print axioms FregeanECA.LambdaInterpretation.pointwise_iff_equation
#print axioms FregeanECA.Part2.ProgramEquations.bare_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.bare_pointwise_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.full_functional_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.full_algebra_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.full_functional_pointwise_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.full_algebra_pointwise_program_equation_iff
#print axioms FregeanECA.Certificate.native_program_equations
#print axioms FregeanECA.Certificate.native_pointwise_equations

-- Stable internal HP infrastructure on arbitrary represented Peano domains.
-- These commands report foundational axiom dependencies; they do not check
-- exclusion of particular named theorem dependencies.
#print axioms FregeanECA.Part2.HumeOrder.least_available_member
#print axioms FregeanECA.Part2.HumeCounting.full_has_count_graph
#print axioms FregeanECA.Part2.HumeCounting.predicate_cardinality_cases
#print axioms FregeanECA.Part2.HumeFinite.injection_bound
#print axioms FregeanECA.Part2.HumeFinite.bijection_bounds_equal
#print axioms FregeanECA.Part2.HumeFinite.no_natural_injection
#print axioms FregeanECA.Part2.HumeBijections.finite_size_unique
#print axioms FregeanECA.Part2.HumeBijections.not_finite_of_enumerable

-- Internal HP: actual closed-sentence derivations, available relation witnesses,
-- and comprehension for the explicitly defined abstraction-graph expansion.
#print axioms FregeanECA.Part2.HumeInternal.code_total_unique
#print axioms FregeanECA.Part2.HumeInternal.humes_principle
#print axioms FregeanECA.Part2.HumeInternal.internal_hume_formulas
#print axioms FregeanECA.Part2.HumeInternal.internal_hume_sentence_valid
#print axioms FregeanECA.Part2.HumeInternal.internal_hume_provable
#print axioms FregeanECA.Part2.HumeInternal.internal_hume_provable_fregean
#print axioms FregeanECA.Part2.HumeInternal.ExpandedFormula.eliminate_truth
#print axioms FregeanECA.Part2.HumeInternal.expanded_comprehension
#print axioms FregeanECA.Certificate.internal_hume
#print axioms FregeanECA.Certificate.internal_hume_semantics
#print axioms FregeanECA.Certificate.internal_hume_comprehension

-- Standard generic Frege theorem and its completed route to all Z2 axioms.
#print axioms FregeanECA.Part2.FregeArithmetic.natural_has_successor_candidate
#print axioms FregeanECA.Part2.FregeArithmetic.hume_implies_frege_peano
#print axioms FregeanECA.Part2.FregeArithmeticDefinable.full_comprehension_of_graph
#print axioms FregeanECA.Part2.FregeArithmeticAdapter.arithmetic_on_inductive_carrier
#print axioms FregeanECA.Part2.FregeArithmeticRecursion.model_has_full_comprehension
#print axioms FregeanECA.Part2.FregeArithmeticRecursion.hume_supplies_arithmetic
#print axioms FregeanECA.Part2.FregeArithmeticZ2.hume_implies_Z2_axioms
#print axioms FregeanECA.Part2.FregeArithmeticZ2.hume_proof_truth
#print axioms FregeanECA.Part2.FregeArithmeticZ2.hume_constructs_Z2_model
#print axioms FregeanECA.Certificate.standard_hume_to_Z2
#print axioms FregeanECA.Part2.ArithmeticModelInterpretation.interpreted_proof_truth
#print axioms FregeanECA.Part2.FregeArithmeticProofTransfer.source_formula_valid
#print axioms FregeanECA.Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer
#print axioms FregeanECA.Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer_fregean
#print axioms FregeanECA.Certificate.arithmetic_via_hume
#print axioms FregeanECA.Part2.FregeArithmeticProofTransfer.interpretation_preserves_falsum
#print axioms FregeanECA.Certificate.hume_translation_preserves_false
#print axioms FregeanECA.Certificates.PartOne.checked
#print axioms FregeanECA.Certificates.PartTwo.checked
#print axioms FregeanECA.Certificates.HumeRoute.checked
