import FregeanECA.Part2.Models
import FregeanECA.Part2.NaturalECA

/-!
An explicit full Part II model admitting Hume's Principle.

The carrier is Nat, carrying the previously constructed extensional
combinatory algebra. Every relation on that carrier is available. The NEW
cross-sort map `number` assigns n+1 to a finite predicate with n instances
and 0 to an infinite predicate. It is not a native computational function,
and this result is model expansion / joint satisfiability, not derivability
of Hume's Principle from the unexpanded Part II axiom set.
-/

namespace FregeanECA.Part2.Hume

abbrev Predicate := Nat → Prop
abbrev BinaryRelation := Nat → Nat → Prop

/-- An ordinary one-to-one correspondence whose graph is a binary relation.
All such graphs are available in the full-relation model used below. -/
def BijectionGraph (P Q : Predicate) (B : BinaryRelation) : Prop :=
  (∀ x y, B x y → P x ∧ Q y) ∧
  (∀ x, P x → ∃! y, B x y) ∧
  (∀ y, Q y → ∃! x, B x y)

def Equinumerous (P Q : Predicate) : Prop :=
  ∃ B : BinaryRelation, BijectionGraph P Q B

theorem equinumerous_iff_equiv (P Q : Predicate) :
    Equinumerous P Q ↔ Nonempty ({x // P x} ≃ {y // Q y}) := by
  classical
  constructor
  · rintro ⟨B, support, total, onto⟩
    let f : {x // P x} → {y // Q y} := fun x =>
      ⟨Classical.choose (total x.val x.property).exists,
        (support x.val _ (Classical.choose_spec (total x.val x.property).exists)).2⟩
    have graph : ∀ x, B x.val (f x).val :=
      fun x => Classical.choose_spec (total x.val x.property).exists
    refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩⟩
    · intro x x' same
      apply Subtype.ext
      have both : B x'.val (f x).val := by rw [same]; exact graph x'
      obtain ⟨w, _, unique⟩ := onto (f x).val (f x).property
      exact (unique x.val (graph x)).trans (unique x'.val both).symm
    · intro y
      obtain ⟨x, related, _⟩ := onto y.val y.property
      let px : {x // P x} := ⟨x, (support x y.val related).1⟩
      refine ⟨px, Subtype.ext ?_⟩
      obtain ⟨w, _, unique⟩ := total x px.property
      exact (unique (f px).val (graph px)).trans (unique y.val related).symm
  · rintro ⟨e⟩
    let B : BinaryRelation := fun x y => ∃ hx : P x, (e ⟨x, hx⟩).val = y
    refine ⟨B, ?_, ?_, ?_⟩
    · rintro x y ⟨hx, same⟩
      exact ⟨hx, same ▸ (e ⟨x, hx⟩).property⟩
    · intro x hx
      refine ⟨(e ⟨x, hx⟩).val, ⟨hx, rfl⟩, ?_⟩
      rintro y ⟨hx', same⟩
      exact same.symm
    · intro y hy
      refine ⟨(e.symm ⟨y, hy⟩).val, ?_, ?_⟩
      · exact ⟨(e.symm ⟨y, hy⟩).property, congrArg Subtype.val (e.apply_symm_apply _)⟩
      · rintro x ⟨hx, same⟩
        have same' : e ⟨x, hx⟩ = ⟨y, hy⟩ := Subtype.ext same
        exact congrArg Subtype.val ((e.symm_apply_apply ⟨x, hx⟩).symm.trans
          (congrArg e.symm same'))

/-- The coding of finite cardinalities leaves zero for the infinite case. -/
noncomputable def number (P : Predicate) : Nat := by
  classical
  exact if finite : Finite {x // P x} then
    @Fintype.card {x // P x} (@Fintype.ofFinite _ finite) + 1 else 0

theorem number_eq_iff_equiv (P Q : Predicate) :
    number P = number Q ↔ Nonempty ({x // P x} ≃ {y // Q y}) := by
  classical
  by_cases hp : Finite {x // P x}
  · let := hp
    by_cases hq : Finite {y // Q y}
    · let := hq
      let := Fintype.ofFinite {x // P x}
      let := Fintype.ofFinite {y // Q y}
      simp only [number, dif_pos hp, dif_pos hq, Nat.add_right_cancel_iff,
        Fintype.card_eq]
    · simp only [number, dif_pos hp, dif_neg hq, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, false_iff]
      rintro ⟨e⟩
      exact hq (Finite.of_equiv {x // P x} e)
  · by_cases hq : Finite {y // Q y}
    · let := hq
      simp only [number, dif_neg hp, dif_pos hq, eq_comm (a := 0),
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_iff]
      rintro ⟨e⟩
      exact hp (Finite.of_equiv {y // Q y} e.symm)
    · let : Infinite {x // P x} := not_finite_iff_infinite.mp hp
      let : Infinite {y // Q y} := not_finite_iff_infinite.mp hq
      simp only [number, dif_neg hp, dif_neg hq, true_iff]
      infer_instance

/-- Hume's Principle, for every unary relation of this explicit full model. -/
theorem humes_principle (P Q : Predicate) :
    number P = number Q ↔ Equinumerous P Q :=
  (number_eq_iff_equiv P Q).trans (equinumerous_iff_equiv P Q).symm

noncomputable def specification := fullRelations NaturalECA.algebra
noncomputable def functional := copyExpansion specification

/-- The exact positive-arity relation domains of the constructed model. -/
abbrev Relation (index : Nat) := (Fin (index + 1) → Nat) → Prop

def extension (P : Relation 0) : Predicate := fun x => P (fun _ => x)

noncomputable def relationNumber (P : Relation 0) : Nat := number (extension P)

/-- Equinumerosity with the witness explicitly in the model's binary relation
sort, rather than in its restricted sort of represented computations. -/
def ModelEquinumerous (P Q : Relation 0) : Prop :=
  ∃ B : Relation 1, BijectionGraph (extension P) (extension Q)
    (fun x y => B (fun i => if i = 0 then x else y))

theorem model_equinumerous_iff (P Q : Relation 0) :
    ModelEquinumerous P Q ↔ Equinumerous (extension P) (extension Q) := by
  constructor
  · rintro ⟨B, law⟩
    exact ⟨fun x y => B (fun i => if i = 0 then x else y), law⟩
  · rintro ⟨B, law⟩
    exact ⟨fun arguments => B (arguments 0) (arguments 1), law⟩

theorem model_humes_principle (P Q : Relation 0) :
    relationNumber P = relationNumber Q ↔ ModelEquinumerous P Q :=
  (humes_principle (extension P) (extension Q)).trans
    (model_equinumerous_iff P Q).symm

/-- Every binary graph used by equinumerosity belongs to the actual relation
sort. The index 1 denotes arity 2 in the project's positive-arity convention. -/
theorem every_bijection_graph_is_available (B : BinaryRelation) :
    ∃ R : (Fin 2 → Nat) → Prop,
      ∀ x y, specification.satisfies 1 R (fun i => if i = 0 then x else y) ↔ B x y :=
  ⟨fun arguments => B (arguments 0) (arguments 1), fun _ _ => Iff.rfl⟩

/-- An unconditional common full-comprehension model, expanded by a
cardinality abstraction satisfying HP on its entire object domain. -/
theorem part_two_has_hume_expansion :
    FullTSConditions specification ∧ FullTFConditions functional ∧
      ∀ P Q : Relation 0, relationNumber P = relationNumber Q ↔ ModelEquinumerous P Q :=
  ⟨fullRelations_satisfies_full_TS NaturalECA.algebra
      NaturalECA.extensional NaturalECA.nontrivial,
    copyExpansion_satisfies_full_TF NaturalECA.algebra
      NaturalECA.extensional NaturalECA.nontrivial,
    model_humes_principle⟩

end FregeanECA.Part2.Hume
