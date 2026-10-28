import Frege.BetaEtaConversion

/-!
# Which surrounding variables can a term use?

`Supported allowed term` says that every local variable occurring in `term`
satisfies the predicate `allowed`. A lambda introduces its own permitted
variable; free names impose no condition on the local context.

Beta and eta contraction preserve support. Consequently, reducing a term
that does not use a newly introduced variable cannot start using it. This
is the side-condition argument needed to commute reductions with eta.
-/

namespace Frege.OpenLambda

def liftAllowed (allowed : Fin n → Prop) : Fin (n + 1) → Prop :=
  Fin.cases True allowed

/-- Every occurring local variable is permitted by `allowed`. -/
def Supported (allowed : Fin n → Prop) : Term n → Prop
  | .var index => allowed index
  | .coeff _ => True
  | .app left right => Supported allowed left ∧ Supported allowed right
  | .lam body => Supported (liftAllowed allowed) body

/-- Renaming transports the predicate that permits local variables. -/
theorem support_of_a_renamed_term (term : Term n) (rename : Fin n → Fin m)
    (allowed : Fin m → Prop) :
    Supported allowed (Program.rename rename term) ↔
      Supported (fun index => allowed (rename index)) term := by
  induction term generalizing m with
  | var index => rfl
  | coeff name => rfl
  | app left right leftProof rightProof =>
      simp only [Program.rename, Supported, leftProof rename allowed, rightProof rename allowed]
  | lam body bodyProof =>
      simp only [Program.rename, Supported, bodyProof (Program.liftRen rename) (liftAllowed allowed)]
      have maps : (fun index => liftAllowed allowed (Program.liftRen rename index)) =
          liftAllowed (fun index => allowed (rename index)) := by
        funext index
        refine Fin.cases ?_ (fun _ => ?_) index <;> rfl
      rw [maps]

/-- A permitted substitution cannot introduce a forbidden surrounding variable. -/
theorem substitution_preserves_support (term : Term n) (allowed : Fin n → Prop)
    (permitted : Supported allowed term) (replace : Fin n → Term m)
    (target : Fin m → Prop)
    (arguments : ∀ index, allowed index → Supported target (replace index)) :
    Supported target (Program.subst replace term) := by
  induction term generalizing m with
  | var index => exact arguments index permitted
  | coeff name => trivial
  | app left right leftProof rightProof =>
      exact ⟨leftProof allowed permitted.1 replace target arguments,
        rightProof allowed permitted.2 replace target arguments⟩
  | lam body bodyProof =>
      apply bodyProof (liftAllowed allowed) permitted (Program.liftSub replace) (liftAllowed target)
      intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · intro _; trivial
      · intro allowedIndex
        exact (support_of_a_renamed_term (replace index) Fin.succ (liftAllowed target)).2
          (arguments index allowedIndex)

/-- A substitution only depends on the variables that the term can use. -/
theorem supported_substitutions_agree (term : Term n) (allowed : Fin n → Prop)
    (permitted : Supported allowed term) (first second : Fin n → Term m)
    (agree : ∀ index, allowed index → first index = second index) :
    Program.subst first term = Program.subst second term := by
  induction term generalizing m with
  | var index => exact agree index permitted
  | coeff name => rfl
  | app left right leftProof rightProof =>
      simp only [Program.subst]
      exact congr (congrArg Program.app (leftProof allowed permitted.1 first second agree))
        (rightProof allowed permitted.2 first second agree)
  | lam body bodyProof =>
      apply congrArg Program.lam
      apply bodyProof (liftAllowed allowed) permitted (Program.liftSub first) (Program.liftSub second)
      intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · intro _; rfl
      · intro allowedIndex
        exact congrArg (Program.rename Fin.succ) (agree index allowedIndex)

/-- A beta or eta contraction introduces no surrounding variables. -/
theorem BetaEtaStep.preserves_support {left right : Term n}
    (step : BetaEtaStep left right) (allowed : Fin n → Prop)
    (permitted : Supported allowed left) : Supported allowed right := by
  induction step with
  | beta body argument =>
      apply substitution_preserves_support body (liftAllowed allowed) permitted.1
        (Program.single argument) allowed
      intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · intro _; exact permitted.2
      · intro allowedIndex; exact allowedIndex
  | eta term =>
      exact (support_of_a_renamed_term term Fin.succ (liftAllowed allowed)).1 permitted.1
  | left _ proof => exact ⟨proof allowed permitted.1, permitted.2⟩
  | right _ proof => exact ⟨permitted.1, proof allowed permitted.2⟩
  | underLam _ proof => exact proof (liftAllowed allowed) permitted

/-- The most recently added variable, index zero, does not occur. -/
def AvoidsNewest (term : Term (n + 1)) : Prop :=
  Supported (Fin.cases False (fun _ => True)) term

theorem every_term_uses_only_permitted_variables (term : Term n) :
    Supported (fun _ => True) term := by
  induction term with
  | var index => trivial
  | coeff name => trivial
  | app left right leftProof rightProof => exact ⟨leftProof, rightProof⟩
  | @lam n body bodyProof =>
      have maps : liftAllowed (fun _ : Fin n => True) = (fun _ => True) := by
        funext index
        refine Fin.cases ?_ (fun _ => ?_) index <;> rfl
      change Supported (liftAllowed _) body
      rw [maps]
      exact bodyProof

/-- Shifting an existing term beneath a binder leaves its new variable unused. -/
theorem a_weakened_term_avoids_the_new_variable (term : Term n) :
    AvoidsNewest (Program.rename Fin.succ term) := by
  apply (support_of_a_renamed_term term Fin.succ _).2
  exact every_term_uses_only_permitted_variables term

/-- Removing and restoring an unused variable changes nothing, for any filler. -/
theorem removing_an_unused_variable_and_restoring_it_changes_nothing
    (term : Term (n + 1)) (unused : AvoidsNewest term) (filler : Term n) :
    Program.rename Fin.succ (Program.beta term filler) = term := by
  rw [Program.beta, Program.rename_subst]
  calc
    Program.subst (fun index => Program.rename Fin.succ (Program.single filler index)) term =
        Program.subst Program.var term := by
      apply supported_substitutions_agree term _ unused
      intro index
      refine Fin.cases ?_ (fun _ => ?_) index
      · intro impossible; exact False.elim impossible
      · intro _; rfl
    _ = term := Program.subst_var term

/-- Substitution for a variable absent from a weakened term just removes the shift. -/
theorem substituting_into_a_weakened_term (term : Term n) (argument : Term n) :
    Program.beta (Program.rename Fin.succ term) argument = term := by
  simp only [Program.beta, Program.subst_rename]
  exact Program.subst_var term

/-- The beta contraction inside an eta expansion of a lambda returns that lambda. -/
theorem beta_inside_an_eta_expanded_lambda (body : Term (n + 1)) :
    Program.beta (Program.rename (Program.liftRen Fin.succ) body) (.var 0) = body := by
  simp only [Program.beta, Program.subst_rename]
  have maps : (fun index => Program.single (Program.var (Coeff := Nat) (n := n + 1) 0)
      (Program.liftRen Fin.succ index)) = Program.var := by
    funext index
    refine Fin.cases ?_ (fun _ => ?_) index <;> rfl
  rw [maps, Program.subst_var]

end Frege.OpenLambda
