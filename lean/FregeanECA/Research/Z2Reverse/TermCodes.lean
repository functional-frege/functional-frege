import Frege.BetaEtaConversion
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Find

/-!
# Explicit syntax codes and least beta-eta class codes

These are external Lean prerequisites for an arithmetisation. `termCode` and
`decode` are concrete computable syntax operations. `classCode` is the least
natural number coding a convertible term, rather than a chosen bijection with
the quotient. Computing `classCode` is not asserted: it uses classical
decidability of the conversion predicate.

This file does not define an arithmetic formula for conversion, prove a Z2
derivation, or provide a proof interpretation inside nonstandard Z2 models.
-/

namespace FregeanECA.Research.Z2Reverse.TermCodes

open Frege OpenLambda

/-- The four constructor tags are 0, 1, 2, and 3. -/
def termCode : Term n → Nat
  | .var i => Nat.pair 0 i.val
  | .coeff a => Nat.pair 1 a
  | .app f x => Nat.pair 2 (Nat.pair (termCode f) (termCode x))
  | .lam body => Nat.pair 3 (termCode body)

theorem termCode_injective {n : Nat} : Function.Injective (termCode (n := n)) := by
  intro left right same
  induction left with
  | var i =>
      cases right <;> simp only [termCode, Nat.pair_eq_pair] at same <;> try omega
      exact congrArg Program.var (Fin.ext same.2)
  | coeff a =>
      cases right <;> simp only [termCode, Nat.pair_eq_pair] at same <;> try omega
      exact congrArg Program.coeff same.2
  | app f x ihf ihx =>
      cases right <;> simp only [termCode, Nat.pair_eq_pair] at same <;> try omega
      exact congr (congrArg Program.app (ihf same.2.1)) (ihx same.2.2)
  | lam body ih =>
      cases right <;> simp only [termCode, Nat.pair_eq_pair] at same <;> try omega
      exact congrArg Program.lam (ih same.2)

/-- A bounded parser. Malformed tags and out-of-scope local indices fail. -/
def decodeFuel : Nat → (n : Nat) → Nat → Option (Term n)
  | 0, _, _ => none
  | fuel + 1, n, code =>
      let tag := (Nat.unpair code).1
      let payload := (Nat.unpair code).2
      if tag = 0 then
        if h : payload < n then some (.var ⟨payload, h⟩) else none
      else if tag = 1 then some (.coeff payload)
      else if tag = 2 then
        match decodeFuel fuel n (Nat.unpair payload).1,
            decodeFuel fuel n (Nat.unpair payload).2 with
        | some f, some x => some (.app f x)
        | _, _ => none
      else if tag = 3 then
        (decodeFuel fuel (n + 1) payload).map Program.lam
      else none

theorem decodeFuel_termCode (term : Term n) (fuel : Nat) (enough : termCode term < fuel) :
    decodeFuel fuel n (termCode term) = some term := by
  induction term generalizing fuel with
  | var i =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [decodeFuel, termCode, i.isLt]
  | coeff a =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [decodeFuel, termCode]
  | app f x ihf ihx =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hp := Nat.add_le_pair 2 (Nat.pair (termCode f) (termCode x))
          have hf := Nat.left_le_pair (termCode f) (termCode x)
          have hx := Nat.right_le_pair (termCode f) (termCode x)
          have ef : termCode f < fuel := by simp only [termCode] at enough; omega
          have ex : termCode x < fuel := by simp only [termCode] at enough; omega
          simp [decodeFuel, termCode, ihf fuel ef, ihx fuel ex]
  | lam body ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hp := Nat.add_le_pair 3 (termCode body)
          have eb : termCode body < fuel := by simp only [termCode] at enough; omega
          simp [decodeFuel, termCode, ih fuel eb]

/-- The code itself gives a sufficient structural recursion bound. -/
def decode (n code : Nat) : Option (Term n) := decodeFuel (code + 1) n code

@[simp] theorem decode_termCode (term : Term n) : decode n (termCode term) = some term :=
  decodeFuel_termCode term _ (Nat.lt_succ_self _)

/-- Membership in the set of syntax codes in a beta-eta class. -/
def InClass (term : Term n) (code : Nat) : Prop :=
  ∃ other : Term n, termCode other = code ∧ Equality term other

theorem inClass_nonempty (term : Term n) : ∃ code, InClass term code :=
  ⟨termCode term, term, rfl, .refl term⟩

/-- A canonical class number specified by minimisation, with no arbitrary bijection. -/
noncomputable def classCode (term : Term n) : Nat := by
  classical
  exact Nat.find (inClass_nonempty term)

theorem classCode_spec (term : Term n) : InClass term (classCode term) := by
  classical
  exact Nat.find_spec (inClass_nonempty term)

theorem classCode_min (term : Term n) {code : Nat} (member : InClass term code) :
    classCode term ≤ code := by
  classical
  exact Nat.find_min' (inClass_nonempty term) member

theorem classCode_le_termCode (term : Term n) : classCode term ≤ termCode term :=
  classCode_min term ⟨term, rfl, .refl term⟩

theorem classCode_eq_of_equivalent {left right : Term n} (same : Equality left right) :
    classCode left = classCode right := by
  apply Nat.le_antisymm
  · obtain ⟨other, code, equivalent⟩ := classCode_spec right
    exact classCode_min left ⟨other, code, same.trans equivalent⟩
  · obtain ⟨other, code, equivalent⟩ := classCode_spec left
    exact classCode_min right ⟨other, code, same.symm.trans equivalent⟩

theorem classCode_eq_iff {left right : Term n} :
    classCode left = classCode right ↔ Equality left right := by
  constructor
  · intro same
    obtain ⟨l, hl, el⟩ := classCode_spec left
    obtain ⟨r, hr, er⟩ := classCode_spec right
    have terms : l = r := termCode_injective (hl.trans (same.trans hr.symm))
    subst r
    exact el.trans er.symm
  · exact classCode_eq_of_equivalent

theorem classCode_eq_iff_betaEta {left right : Term n} :
    classCode left = classCode right ↔ BetaEtaConvertible left right :=
  classCode_eq_iff.trans (algebra_equations_are_exactly_beta_eta_conversion left right)

theorem classCode_app_congr {f g x y : Term n}
    (functions : classCode f = classCode g) (arguments : classCode x = classCode y) :
    classCode (.app f x) = classCode (.app g y) :=
  classCode_eq_of_equivalent (.app (classCode_eq_iff.mp functions)
    (classCode_eq_iff.mp arguments))

theorem decode_classCode_isSome (term : Term n) : (decode n (classCode term)).isSome := by
  obtain ⟨other, code, _⟩ := classCode_spec term
  rw [← code, decode_termCode]
  rfl

/-- The unique syntactic term with the least code, obtained by the concrete parser. -/
noncomputable def representative (term : Term n) : Term n :=
  (decode n (classCode term)).get (decode_classCode_isSome term)

theorem representative_spec (term : Term n) :
    termCode (representative term) = classCode term ∧ Equality term (representative term) := by
  obtain ⟨other, code, equivalent⟩ := classCode_spec term
  have parsed : decode n (classCode term) = some other := by rw [← code, decode_termCode]
  have same : representative term = other := by simp [representative, parsed]
  exact same.symm ▸ ⟨code, equivalent⟩

theorem representative_eq_iff {left right : Term n} :
    representative left = representative right ↔ Equality left right := by
  rw [← classCode_eq_iff]
  constructor
  · intro same
    exact (representative_spec left).1.symm.trans
      ((congrArg termCode same).trans (representative_spec right).1)
  · intro same
    apply termCode_injective
    exact (representative_spec left).1.trans (same.trans (representative_spec right).1.symm)

/-- The graph of canonical application uses no representative choice. -/
def ApplicationGraph (f x result : Nat) : Prop :=
  ∃ left right : Term 0,
    classCode left = f ∧ classCode right = x ∧ classCode (.app left right) = result

def CanonicalCode (code : Nat) : Prop := ∃ term : Term 0, classCode term = code

/-- The least-code condition written without the minimisation operator. -/
theorem canonicalCode_iff_least (code : Nat) : CanonicalCode code ↔
    ∃ term : Term 0, termCode term = code ∧
      ∀ other, Equality term other → code ≤ termCode other := by
  constructor
  · rintro ⟨term, rfl⟩
    refine ⟨representative term, (representative_spec term).1, ?_⟩
    intro other equivalent
    exact classCode_min term ⟨other, rfl, (representative_spec term).2.trans equivalent⟩
  · rintro ⟨term, code, least⟩
    refine ⟨term, Nat.le_antisymm ?_ ?_⟩
    · exact code ▸ classCode_le_termCode term
    · obtain ⟨other, otherCode, equivalent⟩ := classCode_spec term
      exact otherCode ▸ least other equivalent

theorem application_total {f x : Nat} (hf : CanonicalCode f) (hx : CanonicalCode x) :
    ∃ result, CanonicalCode result ∧ ApplicationGraph f x result := by
  obtain ⟨left, rfl⟩ := hf
  obtain ⟨right, rfl⟩ := hx
  exact ⟨classCode (.app left right), ⟨.app left right, rfl⟩, left, right, rfl, rfl, rfl⟩

theorem application_unique {f x first second : Nat}
    (hfirst : ApplicationGraph f x first) (hsecond : ApplicationGraph f x second) :
    first = second := by
  obtain ⟨left, right, hf, hx, hr⟩ := hfirst
  obtain ⟨left', right', hf', hx', hr'⟩ := hsecond
  exact hr.symm.trans ((classCode_app_congr (hf.trans hf'.symm)
    (hx.trans hx'.symm)).trans hr')

/-- The arithmetic carrier is a specified subset of codes, not all of Nat. -/
abbrev CodeObject := {code : Nat // CanonicalCode code}

noncomputable def ofTerm (term : Term 0) : CodeObject :=
  ⟨classCode term, term, rfl⟩

theorem canonical_decode_isSome (code : CodeObject) : (decode 0 code.val).isSome := by
  obtain ⟨term, equal⟩ := code.property
  rw [← equal]
  exact decode_classCode_isSome term

/-- Decode a canonical code; no choice of a term from a quotient is used. -/
noncomputable def codeTerm (code : CodeObject) : Term 0 :=
  (decode 0 code.val).get (canonical_decode_isSome code)

@[simp] theorem codeTerm_ofTerm (term : Term 0) : codeTerm (ofTerm term) = representative term :=
  rfl

theorem codeTerm_code (code : CodeObject) : termCode (codeTerm code) = code.val := by
  obtain ⟨number, term, equal⟩ := code
  subst number
  exact (representative_spec term).1

@[simp] theorem ofTerm_codeTerm (code : CodeObject) : ofTerm (codeTerm code) = code := by
  obtain ⟨number, term, equal⟩ := code
  subst number
  apply Subtype.ext
  exact classCode_eq_of_equivalent (representative_spec term).2.symm

@[simp] theorem ofTerm_eq_iff {left right : Term 0} :
    ofTerm left = ofTerm right ↔ Equality left right :=
  Subtype.ext_iff.trans classCode_eq_iff

/-- Quotient elimination into canonical numbers is invariant under conversion. -/
noncomputable def quotientCode (element : Element) : CodeObject :=
  Quotient.liftOn element ofTerm (fun _ _ same => ofTerm_eq_iff.mpr same)

@[simp] theorem quotientCode_termClass (term : Term 0) :
    quotientCode (termClass term) = ofTerm term := rfl

/-- This equivalence is fixed by syntax coding and least representatives. -/
noncomputable def quotientEquivalence : Element ≃ CodeObject where
  toFun := quotientCode
  invFun := fun code => termClass (codeTerm code)
  left_inv := by
    intro element
    refine Quotient.inductionOn element ?_
    intro term
    exact Quotient.sound (representative_spec term).2.symm
  right_inv := ofTerm_codeTerm

/-- Canonical application computes a syntactic application and then minimises. -/
noncomputable def application (f x : CodeObject) : CodeObject :=
  ofTerm (.app (codeTerm f) (codeTerm x))

theorem application_graph (f x : CodeObject) :
    ApplicationGraph f.val x.val (application f x).val := by
  refine ⟨codeTerm f, codeTerm x, ?_, ?_, rfl⟩
  · exact congrArg Subtype.val (ofTerm_codeTerm f)
  · exact congrArg Subtype.val (ofTerm_codeTerm x)

@[simp] theorem application_ofTerm (f x : Term 0) :
    application (ofTerm f) (ofTerm x) = ofTerm (.app f x) := by
  apply ofTerm_eq_iff.mpr
  exact .app (representative_spec f).2.symm (representative_spec x).2.symm

@[simp] theorem quotientValue_ofTerm (term : Term 0) :
    quotientEquivalence.symm (ofTerm term) = termClass term :=
  Quotient.sound (representative_spec term).2.symm

theorem application_matches_quotient (f x : CodeObject) :
    quotientEquivalence.symm (application f x) =
      OpenLambda.apply (quotientEquivalence.symm f) (quotientEquivalence.symm x) := by
  exact quotientValue_ofTerm _

end FregeanECA.Research.Z2Reverse.TermCodes
