/-!
# Finite reduction paths and the diamond argument

These elementary relation lemmas are independent of lambda syntax. They turn
a one-step diamond into confluence of finite paths, allowing a branch to take
zero steps when two contractions already have the same result.
-/

namespace Frege.Relations

universe u v

inductive Path {α : Type u} (relation : α → α → Prop) : α → α → Prop where
  | refl (point : α) : Path relation point point
  | next : relation first second → Path relation second last → Path relation first last

def Optional {α : Type u} (relation : α → α → Prop) (left right : α) : Prop :=
  relation left right ∨ left = right

def Diamond {α : Type u} (relation : α → α → Prop) : Prop :=
  ∀ {source left right}, relation source left → relation source right →
    ∃ common, relation left common ∧ relation right common

def Confluent {α : Type u} (relation : α → α → Prop) : Prop :=
  ∀ {source left right}, Path relation source left → Path relation source right →
    ∃ common, Path relation left common ∧ Path relation right common

namespace Path

theorem trans {α : Type u} {relation : α → α → Prop}
    {left middle right : α}
    (first : Path relation left middle) (second : Path relation middle right) :
    Path relation left right := by
  induction first with
  | refl _ => exact second
  | next step _ rest => exact .next step (rest second)

theorem single {α : Type u} {relation : α → α → Prop} {left right : α} (step : relation left right) :
    Path relation left right := .next step (.refl _)

theorem map {α : Type u} {β : Type v} {relation : α → α → Prop}
    {left right : α}
    {target : β → β → Prop} (function : α → β)
    (preserves : ∀ {left right}, relation left right → target (function left) (function right))
    (path : Path relation left right) : Path target (function left) (function right) := by
  induction path with
  | refl _ => exact .refl _
  | next step _ rest => exact .next (preserves step) rest

theorem strip {α : Type u} {relation : α → α → Prop} (diamond : Diamond relation)
    {source left right : α}
    (step : relation source left) (path : Path relation source right) :
    ∃ common, Path relation left common ∧ relation right common := by
  induction path generalizing left with
  | refl _ => exact ⟨left, .refl _, step⟩
  | next first _ rest =>
      obtain ⟨corner, fromLeft, fromNext⟩ := diamond step first
      obtain ⟨common, fromCorner, fromRight⟩ := rest fromNext
      exact ⟨common, .next fromLeft fromCorner, fromRight⟩

end Path

/-- A diamond for single steps gives confluence for all finite paths. -/
theorem a_diamond_relation_is_confluent {α : Type u} {relation : α → α → Prop}
    (diamond : Diamond relation) : Confluent relation := by
  intro source left right first second
  induction first generalizing right with
  | refl _ => exact ⟨right, second, .refl _⟩
  | next step _ rest =>
      obtain ⟨corner, fromNext, fromRight⟩ := Path.strip diamond step second
      obtain ⟨common, fromLeft, fromCorner⟩ := rest fromNext
      exact ⟨common, fromLeft, .next fromRight fromCorner⟩

theorem Optional.toPath {α : Type u} {relation : α → α → Prop}
    {left right : α}
    (step : Optional relation left right) : Path relation left right := by
  rcases step with one | same
  · exact .single one
  · subst right; exact .refl _

/-- The optional step relation inherits a square that permits zero-step joins. -/
theorem optional_steps_have_a_diamond {α : Type u} {relation : α → α → Prop}
    (square : ∀ {source left right}, relation source left → relation source right →
      ∃ common, Optional relation left common ∧ Optional relation right common) :
    Diamond (Optional relation) := by
  intro source left right first second
  rcases first with first | same
  · rcases second with second | same
    · exact square first second
    · subst right; exact ⟨left, .inr rfl, .inl first⟩
  · subst left; exact ⟨right, second, .inr rfl⟩

/-- Allowing zero steps in the joining square still suffices for confluence. -/
theorem optional_diamonds_give_confluence {α : Type u} {relation : α → α → Prop}
    (square : ∀ {source left right}, relation source left → relation source right →
      ∃ common, Optional relation left common ∧ Optional relation right common) :
    Confluent relation := by
  have insert : ∀ {a b}, Path relation a b → Path (Optional relation) a b := by
    intro a b path
    exact path.map id (fun step => Or.inl step)
  have remove : ∀ {a b}, Path (Optional relation) a b → Path relation a b := by
    intro a b path
    induction path with
    | refl _ => exact .refl _
    | next step _ rest => exact (Optional.toPath step).trans rest
  intro source left right first second
  obtain ⟨common, fromLeft, fromRight⟩ :=
    a_diamond_relation_is_confluent (optional_steps_have_a_diamond square) (insert first) (insert second)
  exact ⟨common, remove fromLeft, remove fromRight⟩

end Frege.Relations
