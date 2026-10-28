import FregeanECA.Research.Z2Reverse.ArithmeticModel

/-!
Truth preservation and axiom extraction for arbitrary models of the existing
guarded Z2 theory. The source sets remain actual elements of the set sort;
neither standard numbers nor external subsets are introduced.
-/

namespace FregeanECA.Research.Z2Reverse.ArithmeticModel

open FFL FFL.FirstOrder Part2 ArithmeticEncoding
universe u
variable {M : Type u} [Structure language M]

private theorem values_one (a : Term n) (bound : Fin n → M) (free : Nat → M) :
    (fun i : Fin 1 => Semiterm.val bound free (![a] i)) = ![a.val bound free] := by
  funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem values_two (a b : Term n) (bound : Fin n → M) (free : Nat → M) :
    (fun i : Fin 2 => Semiterm.val bound free (![a,b] i)) =
      ![a.val bound free,b.val bound free] := by
  funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

private theorem eval_guard (kind : SortName) (a : Term n)
    (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (guard kind a) ↔ HasSort M kind (a.val bound free) := by
  change Structure.rel (L := language) (.sort kind) _ ↔ _
  rw [values_one]
  rfl

private theorem eval_implies (a b : Formula n) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (a 🡒 b) ↔
      (Semiformula.Eval bound free a → Semiformula.Eval bound free b) := by
  rw [LogicalConnective.HomClass.map_imply]; rfl

private theorem eval_eqn [Structure.Eq language M] (a b : Term n)
    (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (eqn a b) ↔ a.val bound free = b.val bound free := by
  change Structure.rel (L := language) .equal _ ↔ _
  rw [values_two]
  exact Structure.eq_lang (L := language) (M := M)

private theorem eval_and (a b : Formula n) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (.and a b) ↔
      Semiformula.Eval bound free a ∧ Semiformula.Eval bound free b := Iff.rfl

private theorem eval_forall (p : Formula (n+1)) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (.all p) ↔
      ∀ x, Semiformula.Eval (x :> bound) free p := Iff.rfl

private theorem eval_exists (p : Formula (n+1)) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (.exs p) ↔
      ∃ x, Semiformula.Eval (x :> bound) free p := Iff.rfl

/-- Every constructor of the native arithmetic grammar has the truth of its
existing guarded Foundation translation in any equality structure. -/
theorem formula_truth [Structure.Eq language M] (typing : SortCorrect M)
    (p : SecondOrderArithmetic.Formula) :
    ∀ {n} (m : Map n) (bound : Fin n → M) (free : Nat → M)
      (numbers : Nat → Number M) (sets : Nat → SetObject M),
      Maps m bound free numbers sets →
      (Semiformula.Eval bound free (formula m p) ↔
        truth (extracted M typing) numbers sets p) := by
  induction p with
  | equal a b =>
      intro n m bound free numbers sets h
      simp only [formula, truth, eval_eqn, term_value typing a h, term_value typing b h]
      exact Subtype.ext_iff.symm
  | member t i =>
      intro n m bound free numbers sets h
      change Structure.rel (L := language) .member _ ↔ _
      rw [values_two, term_value typing t h, h.sets]
      rfl
  | setEqual i j =>
      intro n m bound free numbers sets h
      simp only [formula, truth, eval_eqn, h.sets]
      exact Subtype.ext_iff.symm
  | falsum => intros; exact Iff.rfl
  | implies p q hp hq =>
      intro n m bound free numbers sets h
      exact (eval_implies _ _ _ _).trans (imp_congr (hp _ _ _ _ _ h) (hq _ _ _ _ _ h))
  | conjunction p q hp hq =>
      intro n m bound free numbers sets h
      exact and_congr (hp _ _ _ _ _ h) (hq _ _ _ _ _ h)
  | disjunction p q hp hq =>
      intro n m bound free numbers sets h
      exact or_congr (hp _ _ _ _ _ h) (hq _ _ _ _ _ h)
  | existsNumber p ih =>
      intro n m bound free numbers sets h
      simp only [formula, eval_exists, eval_and, eval_guard,
        Semiterm.val_bvar, Matrix.cons_val_zero, truth]
      constructor
      · rintro ⟨x, hx, holds⟩
        exact ⟨⟨x, hx⟩, (ih _ _ _ _ _ (h.bind_number ⟨x, hx⟩)).mp holds⟩
      · rintro ⟨x, holds⟩
        exact ⟨x.val, x.property, (ih _ _ _ _ _ (h.bind_number x)).mpr holds⟩
  | forallNumber p ih =>
      intro n m bound free numbers sets h
      simp only [formula, eval_forall, eval_implies, eval_guard,
        Semiterm.val_bvar, Matrix.cons_val_zero, truth]
      constructor
      · intro holds x
        exact (ih _ _ _ _ _ (h.bind_number x)).mp (holds x.val x.property)
      · intro holds x hx
        exact (ih _ _ _ _ _ (h.bind_number ⟨x, hx⟩)).mpr (holds ⟨x, hx⟩)
  | existsSet p ih =>
      intro n m bound free numbers sets h
      simp only [formula, eval_exists, eval_and, eval_guard,
        Semiterm.val_bvar, Matrix.cons_val_zero, truth]
      constructor
      · rintro ⟨X, hX, holds⟩
        exact ⟨⟨X, hX⟩, (ih _ _ _ _ _ (h.bind_set ⟨X, hX⟩)).mp holds⟩
      · rintro ⟨X, holds⟩
        exact ⟨X.val, X.property, (ih _ _ _ _ _ (h.bind_set X)).mpr holds⟩
  | forallSet p ih =>
      intro n m bound free numbers sets h
      simp only [formula, eval_forall, eval_implies, eval_guard,
        Semiterm.val_bvar, Matrix.cons_val_zero, truth]
      constructor
      · intro holds X
        exact (ih _ _ _ _ _ (h.bind_set X)).mp (holds X.val X.property)
      · intro holds X hX
        exact (ih _ _ _ _ _ (h.bind_set ⟨X, hX⟩)).mpr (holds ⟨X, hX⟩)

def encodedAssignment (numbers : Nat → Number M) (sets : Nat → SetObject M) (i : Nat) : M :=
  match variableSort i with
  | .number => (numbers (i / 2)).val
  | .set => (sets (i / 2)).val

@[simp] theorem encodedAssignment_number (numbers : Nat → Number M)
    (sets : Nat → SetObject M) (i : Nat) :
    encodedAssignment numbers sets (variableCode .number i) = (numbers i).val := by
  simp only [encodedAssignment, variableCode_sort, variableCode_index]

@[simp] theorem encodedAssignment_set (numbers : Nat → Number M)
    (sets : Nat → SetObject M) (i : Nat) :
    encodedAssignment numbers sets (variableCode .set i) = (sets i).val := by
  simp only [encodedAssignment, variableCode_sort, variableCode_index]

theorem encodedAssignment_maps (numbers : Nat → Number M) (sets : Nat → SetObject M) :
    Maps initialMap ![] (encodedAssignment numbers sets) numbers sets := by
  constructor <;> intro i <;> simp [initialMap]

theorem encodedAssignment_guarded (numbers : Nat → Number M) (sets : Nat → SetObject M)
    (i : Nat) : HasSort M (variableSort i) (encodedAssignment numbers sets i) := by
  cases kind : variableSort i with
  | number => simpa only [encodedAssignment, kind] using (numbers (i / 2)).property
  | set => simpa only [encodedAssignment, kind] using (sets (i / 2)).property

theorem freeGuards_truth (names : List Nat) (free : Nat → M) :
    Semiformula.Evalf free (freeGuards names) ↔
      ∀ i ∈ names, HasSort M (variableSort i) (free i) := by
  induction names with
  | nil => change True ↔ _; simp
  | cons i rest ih =>
      change (Semiformula.Evalf free (guard (variableSort i) (.fvar i)) ∧
        Semiformula.Evalf free (freeGuards rest)) ↔ _
      rw [eval_guard]
      simpa only [Semiterm.val_fvar, List.mem_cons, forall_eq_or_imp] using and_congr Iff.rfl ih

/-- Universal closure and its exact free-variable guards recover validity
for every genuine number/set assignment in the extracted structure. -/
theorem sentence_truth_forward [Nonempty M] [Structure.Eq language M]
    (typing : SortCorrect M) (p : SecondOrderArithmetic.Formula)
    (holds : (sentence p).Realize M) :
    ∀ numbers sets, truth (extracted M typing) numbers sets p := by
  rw [sentence, Semiformula.eval_univCl] at holds
  intro numbers sets
  have guarded : Semiformula.Evalf (encodedAssignment numbers sets)
      (freeGuards (formula initialMap p).freeVariables.toList) :=
    (freeGuards_truth _ _).mpr (fun i _ => encodedAssignment_guarded numbers sets i)
  have encoded := (eval_implies _ _ ![] _).mp (holds (encodedAssignment numbers sets)) guarded
  exact (formula_truth typing p _ _ _ _ _ (encodedAssignment_maps numbers sets)).mp encoded

/-- The actual guarded Z2 theory supplies every native Z2 axiom, including
the complete comprehension scheme, on its own number and set carriers. -/
theorem extracted_modelsZ2 [Nonempty M] [Structure.Eq language M]
    (model : M↓[language] ⊧* theory) :
    ModelsZ2 (extracted M (sortCorrect_of_model M model)) := by
  intro p hp
  exact sentence_truth_forward (sortCorrect_of_model M model) p
    (model.models_set (Or.inr ⟨p, hp, rfl⟩))

/-- Actual Foundation derivations of guarded arithmetic sentences are sound
in the native arithmetic structure extracted from the same source model. -/
theorem extracted_proof_truth [Nonempty M] [Structure.Eq language M]
    (model : M↓[language] ⊧* theory) (p : SecondOrderArithmetic.Formula)
    (proof : theory ⊢ sentence p) :
    ∀ numbers sets,
      truth (extracted M (sortCorrect_of_model M model)) numbers sets p :=
  sentence_truth_forward (sortCorrect_of_model M model) p
    (Theory.Proof.sound proof model)

end FregeanECA.Research.Z2Reverse.ArithmeticModel
