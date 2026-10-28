import Frege.Programs

/-!
# Open lambda terms and abstraction of a free variable

`Program Nat n` is read here as pure lambda syntax: the `Nat` coefficients are
names of free variables, and `Fin n` indices are the variables available to
surrounding lambda binders. There are no Fregean constants or operations in
these terms. Keeping these two classes of variables separate avoids capture.

The simultaneous instantiation operation substitutes both kinds of variable.
Its main use below is to turn a selected free variable into a newly bound
variable, as required in the extensionality proof for the open term algebra.
-/

namespace Frege.OpenLambda

abbrev Term (locals : Nat) := Program Nat locals

/-- Substitute bound variables and free names simultaneously, avoiding capture. -/
def instantiate : {n m : Nat} → (Fin n → Term m) → (Nat → Term m) → Term n → Term m
  | _, _, bound, _, .var index => bound index
  | _, _, _, free, .coeff name => free name
  | _, _, bound, free, .app left right =>
      .app (instantiate bound free left) (instantiate bound free right)
  | _, _, bound, free, .lam body =>
      .lam (instantiate (Program.liftSub bound)
        (fun name => Program.rename Fin.succ (free name)) body)

/-- The names actually occurring free in a term, allowing harmless repetitions. -/
def freeNames : Term n → List Nat
  | .var _ => []
  | .coeff name => [name]
  | .app left right => freeNames left ++ freeNames right
  | .lam body => freeNames body

/-- Instantiations agreeing on all variables used in a term give the same result. -/
theorem instantiation_uses_only_the_free_names_that_occur
    (term : Term n) (bound : Fin n → Term m) (first second : Nat → Term m)
    (agree : ∀ name, name ∈ freeNames term → first name = second name) :
    instantiate bound first term = instantiate bound second term := by
  induction term generalizing m with
  | var index => rfl
  | coeff name => exact agree name (by simp [freeNames])
  | app left right leftProof rightProof =>
      simp only [instantiate]
      exact congr (congrArg Program.app
        (leftProof bound first second (fun name occurs => agree name (by simp [freeNames, occurs]))))
        (rightProof bound first second (fun name occurs => agree name (by simp [freeNames, occurs])))
  | lam body bodyProof =>
      exact congrArg Program.lam (bodyProof (Program.liftSub bound)
        (fun name => Program.rename Fin.succ (first name))
        (fun name => Program.rename Fin.succ (second name))
        (fun name occurs => congrArg (Program.rename Fin.succ) (agree name occurs)))

/-- With unchanged free names, simultaneous instantiation is ordinary renaming. -/
theorem instantiating_with_variables_is_renaming (term : Term n) (rename : Fin n → Fin m) :
    instantiate (fun index => .var (rename index)) Program.coeff term =
      Program.rename rename term := by
  induction term generalizing m with
  | var index => rfl
  | coeff name => rfl
  | app left right leftProof rightProof =>
      simp only [instantiate, Program.rename]
      exact congr (congrArg Program.app (leftProof rename)) (rightProof rename)
  | lam body bodyProof =>
      have lifted : Program.liftSub (fun index => Program.var (Coeff := Nat) (rename index)) =
          (fun index => Program.var (Program.liftRen rename index)) := by
        funext index
        refine Fin.cases ?_ (fun _ => ?_) index <;> rfl
      simp only [instantiate, Program.rename, lifted]
      exact congrArg Program.lam (bodyProof (Program.liftRen rename))

/-- A bound greater than every free name; it is computed from the finite syntax. -/
def freshBound : Term n → Nat
  | .var _ => 0
  | .coeff name => name + 1
  | .app left right => max (freshBound left) (freshBound right)
  | .lam body => freshBound body

theorem every_occurring_name_is_below_the_fresh_bound
    (term : Term n) (name : Nat) (occurs : name ∈ freeNames term) : name < freshBound term := by
  induction term with
  | var index => simp [freeNames] at occurs
  | coeff entry =>
      have same : name = entry := by simpa [freeNames] using occurs
      subst name
      exact Nat.lt_succ_self entry
  | app left right leftProof rightProof =>
      have either : name ∈ freeNames left ∨ name ∈ freeNames right := by
        simpa only [freeNames, List.mem_append] using occurs
      cases either with
      | inl inLeft => exact Nat.lt_of_lt_of_le (leftProof inLeft) (Nat.le_max_left _ _)
      | inr inRight => exact Nat.lt_of_lt_of_le (rightProof inRight) (Nat.le_max_right _ _)
  | lam body bodyProof => exact bodyProof occurs

theorem any_name_at_or_above_the_bound_is_fresh (term : Term n) (name : Nat)
    (largeEnough : freshBound term ≤ name) : name ∉ freeNames term := by
  intro occurs
  have below := every_occurring_name_is_below_the_fresh_bound term name occurs
  omega

/-- Promote the selected free name to the new bound variable zero. -/
def bindFreeName (name : Nat) (term : Term 0) : Term 1 :=
  instantiate Fin.elim0 (fun other => if other = name then .var 0 else .coeff other) term

/-- Binding a name absent from a term merely shifts that term beneath a binder. -/
theorem binding_a_fresh_name_only_weakens_the_term
    (term : Term 0) (name : Nat) (fresh : name ∉ freeNames term) :
    bindFreeName name term = Program.rename Fin.succ term := by
  have unchanged := instantiation_uses_only_the_free_names_that_occur term
    (m := 1) Fin.elim0 (fun other => if other = name then .var 0 else .coeff other)
    Program.coeff (by
      intro other occurs
      have different : other ≠ name := by
        intro same
        subst other
        exact fresh occurs
      simp only [different, if_false])
  have localMap : (Fin.elim0 : Fin 0 → Term 1) =
      (fun index => Program.var (Fin.succ index)) := by
    funext index
    exact Fin.elim0 index
  unfold bindFreeName
  rw [unchanged, localMap]
  exact instantiating_with_variables_is_renaming term Fin.succ

end Frege.OpenLambda
