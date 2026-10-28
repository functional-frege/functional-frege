import Frege.BetaEtaCommutation

/-!
# Confluence of the actual beta–eta reduction relation

A block consists of finitely many beta steps or finitely many eta steps.
Beta confluence, eta confluence and their commutation give a diamond for
blocks. Every ordinary beta–eta step is a block, and every block is an
ordinary finite beta–eta reduction. Thus the diamond argument applies to
the precise reduction relation used in `BetaEtaConversion.lean`.

This proof does not assume that the starting term has a normal form.
-/

namespace Frege.OpenLambda

/-- A block contains only beta contractions or only eta contractions. -/
def ReductionBlock (left right : Term n) : Prop :=
  Program.Steps left right ∨ EtaSteps left right

theorem reduction_blocks_have_a_diamond : Relations.Diamond (@ReductionBlock n) := by
  intro source left right first second
  rcases first with betaFirst | etaFirst
  · rcases second with betaSecond | etaSecond
    · obtain ⟨common, fromLeft, fromRight⟩ := Program.beta_reduction_is_confluent betaFirst betaSecond
      exact ⟨common, .inl fromLeft, .inl fromRight⟩
    · obtain ⟨common, fromLeft, fromRight⟩ := finite_beta_and_eta_reductions_commute betaFirst etaSecond
      exact ⟨common, .inr fromLeft, .inl fromRight⟩
  · rcases second with betaSecond | etaSecond
    · obtain ⟨common, fromRight, fromLeft⟩ := finite_beta_and_eta_reductions_commute betaSecond etaFirst
      exact ⟨common, .inl fromLeft, .inr fromRight⟩
    · obtain ⟨common, fromLeft, fromRight⟩ := eta_reduction_is_confluent etaFirst etaSecond
      exact ⟨common, .inr fromLeft, .inr fromRight⟩

theorem BetaEtaStep.toBlock {left right : Term n} (step : BetaEtaStep left right) :
    ReductionBlock left right := by
  induction step with
  | beta body argument => exact .inl (.next (.beta body argument) (.refl _))
  | eta term => exact .inr (.single (.eta term))
  | left _ proof =>
      rcases proof with betaPath | etaPath
      · exact .inl (betaPath.appLeft _)
      · exact .inr (EtaSteps.appLeft etaPath _)
  | right _ proof =>
      rcases proof with betaPath | etaPath
      · exact .inl (betaPath.appRight _)
      · exact .inr (EtaSteps.appRight etaPath _)
  | underLam _ proof =>
      rcases proof with betaPath | etaPath
      · exact .inl betaPath.underLam
      · exact .inr (EtaSteps.underLam etaPath)

theorem BetaEtaSteps.toBlocks {left right : Term n} (path : BetaEtaSteps left right) :
    Relations.Path ReductionBlock left right := by
  induction path with
  | refl _ => exact .refl _
  | next step _ rest => exact .next step.toBlock rest

theorem beta_steps_are_beta_eta_steps {left right : Term n} (path : Program.Steps left right) :
    BetaEtaSteps left right := by
  induction path with
  | refl _ => exact .refl _
  | next step _ rest => exact .next (beta_step_is_a_beta_eta_step step) rest

theorem a_block_is_a_finite_beta_eta_reduction {left right : Term n} (block : ReductionBlock left right) :
    BetaEtaSteps left right := by
  rcases block with betaPath | etaPath
  · exact beta_steps_are_beta_eta_steps betaPath
  · exact EtaSteps.toBetaEta etaPath

theorem a_block_path_is_a_finite_beta_eta_reduction {left right : Term n}
    (path : Relations.Path ReductionBlock left right) : BetaEtaSteps left right := by
  induction path with
  | refl _ => exact .refl _
  | next block _ rest => exact (a_block_is_a_finite_beta_eta_reduction block).trans rest

/-- Two finite beta–eta reductions from one term always have a common continuation. -/
theorem beta_eta_reduction_is_confluent {source left right : Term n}
    (first : BetaEtaSteps source left) (second : BetaEtaSteps source right) :
    ∃ common, BetaEtaSteps left common ∧ BetaEtaSteps right common := by
  obtain ⟨common, fromLeft, fromRight⟩ := Relations.a_diamond_relation_is_confluent
    reduction_blocks_have_a_diamond first.toBlocks second.toBlocks
  exact ⟨common, a_block_path_is_a_finite_beta_eta_reduction fromLeft,
    a_block_path_is_a_finite_beta_eta_reduction fromRight⟩

end Frege.OpenLambda
