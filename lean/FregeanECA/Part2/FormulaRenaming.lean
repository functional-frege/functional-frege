import FregeanECA.Part2.SecondOrderArithmetic

/-! Capture-avoiding renaming of the free object variables in the actual
applicative formula grammar. Predicate parameters are unchanged. -/
namespace FregeanECA.Part2.FormulaRenaming
open Positive SecondOrderArithmetic
universe u v

def objects (map : Nat → Nat) : Applicative.Formula → Applicative.Formula
  | .equal a b => .equal (renameTerm map a) (renameTerm map b)
  | .relation n i args => .relation n i (fun j => renameTerm map (args j))
  | .relationEqual n i j => .relationEqual n i j
  | .falsum => .falsum
  | .implies p q => .implies (objects map p) (objects map q)
  | .conjunction p q => .conjunction (objects map p) (objects map q)
  | .disjunction p q => .disjunction (objects map p) (objects map q)
  | .existsObject p => .existsObject (objects (Functional.bindMap map) p)
  | .forallObject p => .forallObject (objects (Functional.bindMap map) p)
  | .existsPredicate n p => .existsPredicate n (objects map p)
  | .forallPredicate n p => .forallPredicate n (objects map p)

theorem push_renamed {D : Type u} (map : Nat → Nat) (o : ObjectAssignment D) (x : D) :
    (fun i => pushObject o x (Functional.bindMap map i)) =
      pushObject (fun i => o (map i)) x := by
  funext i
  cases i <;> rfl

theorem objects_truth {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) (p : Applicative.Formula) :
    ∀ map o r, (objects map p).truth M o r ↔ p.truth M (fun i => o (map i)) r := by
  induction p with
  | equal a b => intros; simp only [objects, Applicative.Formula.truth, renameTerm_value]
  | relation n i args => intros; simp only [objects, Applicative.Formula.truth, renameTerm_value]
  | relationEqual n i j => intros; rfl
  | falsum => intros; rfl
  | implies p q hp hq =>
    intro map o r; exact imp_congr (hp map o r) (hq map o r)
  | conjunction p q hp hq =>
    intro map o r; exact and_congr (hp map o r) (hq map o r)
  | disjunction p q hp hq =>
    intro map o r; exact or_congr (hp map o r) (hq map o r)
  | existsObject p hp =>
    intro map o r
    apply exists_congr
    intro x
    simpa only [push_renamed] using hp (Functional.bindMap map) (pushObject o x) r
  | forallObject p hp =>
    intro map o r
    apply forall_congr'
    intro x
    simpa only [push_renamed] using hp (Functional.bindMap map) (pushObject o x) r
  | existsPredicate n p hp =>
    intro map o r; exact exists_congr (fun P => hp map o (pushPredicate r n P))
  | forallPredicate n p hp =>
    intro map o r; exact forall_congr' (fun P => hp map o (pushPredicate r n P))

end FregeanECA.Part2.FormulaRenaming
