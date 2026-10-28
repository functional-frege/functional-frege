import FregeanECA.V2.Full

/-!
# Available sets as relations on a coded domain

This is the relation-domain component of a possible reverse interpretation.
`S` is an arbitrary *available* set sort. It is never replaced by a powerset.
The object domain is presented by a surjection from codes; consequently this
construction applies to a quotient of valid term codes without choosing a
canonical representative in the object language.

The final comprehension transfer is explicitly conditional on
`PullbackRepresentation`. In an interpretation in Z2, that obligation must be
proved using arithmetic formulas and the source comprehension scheme. The
present module does not establish arithmetic definability of term conversion,
tuple coding, or the translation of quantified formulas.
-/

namespace FregeanECA.Research.Z2Reverse.RelationCoding
open Positive Part2
universe u v w

/-- A presentation of objects by codes and of positive-arity tuples by codes.
No standardness or injectivity of the code domain is assumed. -/
structure Presentation (D : Type u) (C : Type v) where
  decode : C → D
  onto : Function.Surjective decode
  tuple : (arity : Nat) → (Fin (arity + 1) → C) → C

variable {D : Type u} {C : Type v} {S : Type w}

/-- Membership in the source's actual set sort. -/
abbrev Membership (C : Type v) (S : Type w) := S → C → Prop

namespace Presentation

noncomputable def representative (coding : Presentation D C) (x : D) : C :=
  Classical.choose (coding.onto x)

@[simp] theorem decode_representative (coding : Presentation D C) (x : D) :
    coding.decode (coding.representative x) = x :=
  Classical.choose_spec (coding.onto x)

def decodeTuple (coding : Presentation D C) {arity : Nat}
    (xs : Fin (arity + 1) → C) : Fin (arity + 1) → D :=
  fun i => coding.decode (xs i)

noncomputable def representatives (coding : Presentation D C) {arity : Nat}
    (xs : Fin (arity + 1) → D) : Fin (arity + 1) → C :=
  fun i => coding.representative (xs i)

@[simp] theorem decodeTuple_representatives (coding : Presentation D C) {arity : Nat}
    (xs : Fin (arity + 1) → D) :
    coding.decodeTuple (coding.representatives xs) = xs := by
  funext i
  exact coding.decode_representative (xs i)

/-- A source set may contain arbitrary irrelevant codes. Its tuple membership
must respect equality of the represented objects at the specified arity. -/
def Saturated (coding : Presentation D C) (member : Membership C S)
    (arity : Nat) (X : S) : Prop :=
  ∀ xs ys : Fin (arity + 1) → C,
    coding.decodeTuple xs = coding.decodeTuple ys →
    (member X (coding.tuple arity xs) ↔ member X (coding.tuple arity ys))

/-- Only source sets satisfying the quotient-invariance guard are quantified
over as target relations. This subtype adds no new source sets. -/
def Relation (coding : Presentation D C) (member : Membership C S) (arity : Nat) :=
  {X : S // coding.Saturated member arity X}

theorem relation_identity_iff (coding : Presentation D C) (member : Membership C S)
    (arity : Nat) (X Y : coding.Relation member arity) :
    X = Y ↔ X.val = Y.val :=
  Subtype.ext_iff

noncomputable def holds (coding : Presentation D C) (member : Membership C S)
    (arity : Nat) (X : coding.Relation member arity)
    (xs : Fin (arity + 1) → D) : Prop :=
  member X.val (coding.tuple arity (coding.representatives xs))

/-- Every representative tuple gives the same relation truth value. -/
theorem holds_decodeTuple (coding : Presentation D C) (member : Membership C S)
    (arity : Nat) (X : coding.Relation member arity)
    (xs : Fin (arity + 1) → C) :
    coding.holds member arity X (coding.decodeTuple xs) ↔
      member X.val (coding.tuple arity xs) := by
  exact X.property _ xs (coding.decodeTuple_representatives _)

/-- The chosen section is dispensable: membership is independent of every
coordinate's choice of code. -/
theorem holds_iff_representative (coding : Presentation D C) (member : Membership C S)
    (arity : Nat) (X : coding.Relation member arity)
    (xs : Fin (arity + 1) → D) (codes : Fin (arity + 1) → C)
    (represented : coding.decodeTuple codes = xs) :
    coding.holds member arity X xs ↔ member X.val (coding.tuple arity codes) := by
  rw [← represented]
  exact coding.holds_decodeTuple member arity X codes

/-- Guarded source-set quantification is exactly quantification over the
target relation domain, including formulas that inspect relation identity. -/
theorem exists_relation_iff (coding : Presentation D C) (member : Membership C S)
    (arity : Nat) (p : S → Prop) :
    (∃ X : coding.Relation member arity, p X.val) ↔
      ∃ X : S, coding.Saturated member arity X ∧ p X := by
  constructor
  · rintro ⟨X, h⟩; exact ⟨X.val, X.property, h⟩
  · rintro ⟨X, guard, h⟩; exact ⟨⟨X, guard⟩, h⟩

theorem forall_relation_iff (coding : Presentation D C) (member : Membership C S)
    (arity : Nat) (p : S → Prop) :
    (∀ X : coding.Relation member arity, p X.val) ↔
      ∀ X : S, coding.Saturated member arity X → p X := by
  constructor
  · intro h X guard; exact h ⟨X, guard⟩
  · intro h X; exact h X.val X.property

/-- Object quantifiers can be pulled back along the presentation, even when
many codes represent the same object. -/
theorem exists_object_iff (coding : Presentation D C) (p : D → Prop) :
    (∃ x, p x) ↔ ∃ c, p (coding.decode c) := by
  constructor
  · rintro ⟨x, h⟩
    obtain ⟨c, rfl⟩ := coding.onto x
    exact ⟨c, h⟩
  · rintro ⟨c, h⟩; exact ⟨coding.decode c, h⟩

theorem forall_object_iff (coding : Presentation D C) (p : D → Prop) :
    (∀ x, p x) ↔ ∀ c, p (coding.decode c) := by
  constructor
  · intro h c; exact h (coding.decode c)
  · intro h x
    obtain ⟨c, rfl⟩ := coding.onto x
    exact h c

/-- Install exactly the available saturated relations on an already
constructed applicative object domain. No computational laws are postulated. -/
noncomputable def interpretation (coding : Presentation D C) (member : Membership C S)
    (application : D → D → D) (k s : D) :
    Interpretation D (coding.Relation member) where
  apply := application
  constantK := k
  constantS := s
  satisfies := coding.holds member

variable (coding : Presentation D C) (member : Membership C S)
  (application : D → D → D) (k s : D)

/-- Operations on codes that realize the already constructed object
operations. Their existence and arithmetic definitions are separate tasks. -/
structure CodeOperations where
  apply : C → C → C
  constantK : C
  constantS : C
  apply_law : ∀ a b, coding.decode (apply a b) =
    application (coding.decode a) (coding.decode b)
  k_law : coding.decode constantK = k
  s_law : coding.decode constantS = s

def termCode (coding : Presentation D C) {application : D → D → D} {k s : D}
    (operations : coding.CodeOperations application k s)
    (objects : Nat → C) : Positive.Term → C
  | .var i => objects i
  | .constantK => operations.constantK
  | .constantS => operations.constantS
  | .app f x => operations.apply (coding.termCode operations objects f)
      (coding.termCode operations objects x)

theorem decode_termCode (operations : coding.CodeOperations application k s)
    (objects : Nat → C) (term : Positive.Term) :
    coding.decode (coding.termCode operations objects term) =
      term.value (coding.interpretation member application k s)
        (fun i => coding.decode (objects i)) := by
  induction term with
  | var i => rfl
  | constantK => exact operations.k_law
  | constantS => exact operations.s_law
  | app f x hf hx =>
      change coding.decode (operations.apply _ _) = application _ _
      rw [operations.apply_law, hf, hx]

/-- Semantic code expansion of the complete target grammar. Object equality
is equality after decoding, not equality of representatives. Predicate
identity remains identity of the available source sets. This definition is
not itself a formula of second-order arithmetic. -/
def codeTruth (coding : Presentation D C) (member : Membership C S)
    {application : D → D → D} {k s : D}
    (operations : coding.CodeOperations application k s)
    (objects : Nat → C) (predicates : PredicateAssignment (coding.Relation member)) :
    Applicative.Formula → Prop
  | .equal a b => coding.decode (coding.termCode operations objects a) =
      coding.decode (coding.termCode operations objects b)
  | .relation arity index args => member (predicates arity index).val
      (coding.tuple arity (fun i => coding.termCode operations objects (args i)))
  | .relationEqual arity a b => (predicates arity a).val = (predicates arity b).val
  | .falsum => False
  | .implies p q => coding.codeTruth member operations objects predicates p →
      coding.codeTruth member operations objects predicates q
  | .conjunction p q => coding.codeTruth member operations objects predicates p ∧
      coding.codeTruth member operations objects predicates q
  | .disjunction p q => coding.codeTruth member operations objects predicates p ∨
      coding.codeTruth member operations objects predicates q
  | .existsObject p => ∃ c : C,
      coding.codeTruth member operations (pushObject objects c) predicates p
  | .forallObject p => ∀ c : C,
      coding.codeTruth member operations (pushObject objects c) predicates p
  | .existsPredicate arity p => ∃ X : coding.Relation member arity,
      coding.codeTruth member operations objects (pushPredicate predicates arity X) p
  | .forallPredicate arity p => ∀ X : coding.Relation member arity,
      coding.codeTruth member operations objects (pushPredicate predicates arity X) p

theorem decode_pushObject (objects : Nat → C) (c : C) :
    (fun i => coding.decode (pushObject objects c i)) =
      pushObject (fun i => coding.decode (objects i)) (coding.decode c) := by
  funext i
  cases i <;> rfl

/-- Structural truth preservation for every target constructor, including
nested object and predicate binders, implication and relation identity. -/
theorem codeTruth_iff_truth (operations : coding.CodeOperations application k s)
    (formula : Applicative.Formula) :
    ∀ objects predicates,
      coding.codeTruth member operations objects predicates formula ↔
        formula.truth (coding.interpretation member application k s)
          (fun i => coding.decode (objects i)) predicates := by
  induction formula with
  | equal a b =>
      intro objects predicates
      simp only [codeTruth, Applicative.Formula.truth,
        coding.decode_termCode member application k s operations]
  | relation arity index args =>
      intro objects predicates
      have represented : coding.decodeTuple
          (fun i => coding.termCode operations objects (args i)) =
          (fun i => (args i).value (coding.interpretation member application k s)
            (fun j => coding.decode (objects j))) := by
        funext i
        exact coding.decode_termCode member application k s operations objects (args i)
      exact (coding.holds_iff_representative member arity (predicates arity index)
        _ _ represented).symm
  | relationEqual arity a b =>
      intro objects predicates
      exact (coding.relation_identity_iff member arity _ _).symm
  | falsum => intros; exact Iff.rfl
  | implies p q hp hq => intros; exact imp_congr (hp _ _) (hq _ _)
  | conjunction p q hp hq => intros; exact and_congr (hp _ _) (hq _ _)
  | disjunction p q hp hq => intros; exact or_congr (hp _ _) (hq _ _)
  | existsObject p hp =>
      intro objects predicates
      change (∃ c, coding.codeTruth member operations (pushObject objects c) predicates p) ↔ _
      have expanded := exists_congr (fun c => hp (pushObject objects c) predicates)
      simp only [coding.decode_pushObject] at expanded
      exact expanded.trans (coding.exists_object_iff
        (fun x => p.truth (coding.interpretation member application k s)
          (pushObject (fun i => coding.decode (objects i)) x) predicates)).symm
  | forallObject p hp =>
      intro objects predicates
      change (∀ c, coding.codeTruth member operations (pushObject objects c) predicates p) ↔ _
      have expanded := forall_congr' (fun c => hp (pushObject objects c) predicates)
      simp only [coding.decode_pushObject] at expanded
      exact expanded.trans (coding.forall_object_iff
        (fun x => p.truth (coding.interpretation member application k s)
          (pushObject (fun i => coding.decode (objects i)) x) predicates)).symm
  | existsPredicate arity p hp =>
      intros; exact exists_congr (fun X => hp _ _)
  | forallPredicate arity p hp =>
      intros; exact forall_congr' (fun X => hp _ _)

/-- The exact source-comprehension obligation. For each complete target
formula and each parameter assignment, an available source set represents
its truth on tuple codes. This is an obligation, not an assumed Z2 theorem. -/
def PullbackRepresentation : Prop :=
  ∀ (arity : Nat) (formula : Applicative.Formula)
    (parameters : ObjectAssignment D)
    (predicates : PredicateAssignment (coding.Relation member)),
    ∃ X : S, ∀ xs : Fin (arity + 1) → C,
      member X (coding.tuple arity xs) ↔
        formula.truth (coding.interpretation member application k s)
          (assignTuple (arity + 1) (coding.decodeTuple xs) parameters) predicates

/-- Every pullback of an object-tuple property automatically passes the
saturation guard. In particular, comprehension witnesses need no additional
closure operation on the source set domain. -/
theorem represented_pullback_saturated (arity : Nat) (X : S)
    (p : (Fin (arity + 1) → D) → Prop)
    (represented : ∀ xs, member X (coding.tuple arity xs) ↔ p (coding.decodeTuple xs)) :
    coding.Saturated member arity X := by
  intro xs ys same
  exact (represented xs).trans (same ▸ (represented ys).symm)

/-- Conditional transfer of full classical comprehension. The relation
sorts contain only available source sets, never externally supplied subsets. -/
theorem fullComprehension_of_pullbackRepresentation
    (empty : S) (empty_law : ∀ c, ¬ member empty c)
    (represented : coding.PullbackRepresentation member application k s) :
    HasFullComprehension (coding.interpretation member application k s) := by
  refine ⟨?_, ?_⟩
  · intro arity
    refine ⟨⟨empty, ?_⟩⟩
    intro xs ys same
    exact iff_of_false (empty_law _) (empty_law _)
  · intro arity formula parameters predicates
    obtain ⟨X, hX⟩ := represented arity formula parameters predicates
    have saturated : coding.Saturated member arity X :=
      coding.represented_pullback_saturated member arity X
        (fun xs => formula.truth (coding.interpretation member application k s)
          (assignTuple (arity + 1) xs parameters) predicates) hX
    refine ⟨⟨X, saturated⟩, ?_⟩
    intro xs
    change member X (coding.tuple arity (coding.representatives xs)) ↔ _
    simpa only [decodeTuple_representatives] using hX (coding.representatives xs)

/-- The resulting full algebra follows from the established V2 equivalence;
all arithmetic representation hypotheses remain visible in the statement. -/
theorem fcAlgebra_of_pullbackRepresentation
    (empty : S) (empty_law : ∀ c, ¬ member empty c)
    (represented : coding.PullbackRepresentation member application k s) :
    V2.FCAlgebra (coding.interpretation member application k s) :=
  V2.fullComprehension_implies_fcAlgebra _
    (coding.fullComprehension_of_pullbackRepresentation member application k s
      empty empty_law represented)

end Presentation

/-- Specialization to the quotient of valid codes by a proved equivalence.
The tuple encoder operates on codes; no quotient representative is encoded
as an object-language choice function. -/
def quotientPresentation (equivalence : Setoid C)
    (tuple : (arity : Nat) → (Fin (arity + 1) → C) → C) :
    Presentation (Quotient equivalence) C where
  decode := Quotient.mk equivalence
  onto := Quotient.exists_rep
  tuple := tuple

theorem quotient_saturated_iff (equivalence : Setoid C)
    (tuple : (arity : Nat) → (Fin (arity + 1) → C) → C)
    (member : Membership C S) (arity : Nat) (X : S) :
    (quotientPresentation equivalence tuple).Saturated member arity X ↔
      ∀ xs ys : Fin (arity + 1) → C,
        (∀ i, equivalence.r (xs i) (ys i)) →
          (member X (tuple arity xs) ↔ member X (tuple arity ys)) := by
  constructor
  · intro saturated xs ys equivalent
    apply saturated xs ys
    funext i
    exact Quotient.sound (equivalent i)
  · intro saturated xs ys same
    apply saturated xs ys
    intro i
    exact Quotient.exact (congrFun same i)

end FregeanECA.Research.Z2Reverse.RelationCoding
