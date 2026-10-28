import FregeanECA.Research.Z2Reverse.InternalConversionFormula
import FregeanECA.Research.Z2Reverse.ComprehensionTransfer

/-! Model-independent syntax for the reverse translation. The five atomic
builders are fixed formulas, and every larger formula is built recursively. -/
namespace FregeanECA.Research.Z2Reverse.UniformFormulaTranslation
open Part2 ArithmeticModel NativeFormulaTools Positive RelationCoding ArithmeticCodeAtoms
open FormulaTranslation

structure Atoms where
  equalFormula : NTerm → NTerm → NFormula
  kFormula : NTerm → NFormula
  sFormula : NTerm → NFormula
  appFormula : NTerm → NTerm → NTerm → NFormula
  pairFormula : NTerm → NTerm → NTerm → NFormula

namespace Atoms
variable (atoms : Atoms)

def tupleGraph (atoms : Atoms) : (arity : Nat) → (Fin (arity + 1) → NTerm) → NTerm → NFormula
  | 0, args, output => .equal output (args 0)
  | n + 1, args, output => .existsNumber (.conjunction
      (atoms.tupleGraph n (fun i => liftTerm 1 (args i.succ)) (.var 0))
      (atoms.pairFormula (liftTerm 1 (args 0)) (.var 0) (liftTerm 1 output)))


def termGraph (atoms : Atoms) (varTerms : Nat → NTerm) (output : NTerm) : Positive.Term → NFormula
  | .var i => .equal output (varTerms i)
  | .constantK => atoms.kFormula output
  | .constantS => atoms.sFormula output
  | .app f x => .existsNumber (.existsNumber (.conjunction
      (atoms.termGraph (fun i => liftTerm 2 (varTerms i)) (.var 1) f)
      (.conjunction (atoms.termGraph (fun i => liftTerm 2 (varTerms i)) (.var 0) x)
        (atoms.appFormula (.var 1) (.var 0) (liftTerm 2 output)))))


def tupleMember (arity : Nat) (setIndex : Nat) (args : Fin (arity + 1) → NTerm) : NFormula :=
  .existsNumber (.conjunction
    (atoms.tupleGraph arity (fun i => liftTerm 1 (args i)) (.var 0)) (.member (.var 0) setIndex))


def saturatedFormula (arity setIndex : Nat) : NFormula :=
  forallNumbers (arity + 1) (forallNumbers (arity + 1) (.implies
    (andFin (arity + 1) (fun i => atoms.equalFormula (.var (arity + 1 + i.val)) (.var i.val)))
    (SecondOrderArithmetic.iffF
      (atoms.tupleMember arity setIndex (fun i => .var (arity + 1 + i.val)))
      (atoms.tupleMember arity setIndex (fun i => .var i.val)))))


def equationFormula (varTerms : Nat → NTerm) (left right : Positive.Term) : NFormula :=
  .existsNumber (.existsNumber (.conjunction
    (atoms.termGraph (fun i => liftTerm 2 (varTerms i)) (.var 1) left)
    (.conjunction (atoms.termGraph (fun i => liftTerm 2 (varTerms i)) (.var 0) right)
      (atoms.equalFormula (.var 1) (.var 0)))))


def relationFormula (varTerms : Nat → NTerm) (arity setIndex : Nat)
    (args : Fin (arity + 1) → Positive.Term) : NFormula :=
  existsNumbers (arity + 1) (.conjunction
    (andFin (arity + 1) (fun i => atoms.termGraph
      (fun j => liftTerm (arity + 1) (varTerms j)) (.var i.val) (args i)))
    (atoms.tupleMember arity setIndex (fun i => .var i.val)))


def translate (atoms : Atoms)
    (varTerms : Nat → NTerm) (relationMap : Nat → Nat → Nat) : Applicative.Formula → NFormula
  | .equal a b => equationFormula atoms varTerms a b
  | .relation arity i args => relationFormula atoms varTerms arity (relationMap arity i) args
  | .relationEqual arity i j => .setEqual (relationMap arity i) (relationMap arity j)
  | .falsum => .falsum
  | .implies p q => .implies (translate atoms varTerms relationMap p) (translate atoms varTerms relationMap q)
  | .conjunction p q => .conjunction (translate atoms varTerms relationMap p) (translate atoms varTerms relationMap q)
  | .disjunction p q => .disjunction (translate atoms varTerms relationMap p) (translate atoms varTerms relationMap q)
  | .existsObject p => .existsNumber
      (translate atoms (pushObject (fun i => liftTerm 1 (varTerms i)) (.var 0)) relationMap p)
  | .forallObject p => .forallNumber
      (translate atoms (pushObject (fun i => liftTerm 1 (varTerms i)) (.var 0)) relationMap p)
  | .existsPredicate arity p => .existsSet (.conjunction (saturatedFormula atoms arity 0)
      (translate atoms varTerms (bindRelationMap relationMap arity) p))
  | .forallPredicate arity p => .forallSet (.implies (saturatedFormula atoms arity 0)
      (translate atoms varTerms (bindRelationMap relationMap arity) p))


end Atoms

universe u v w
variable {N : Type u} {S : Type v} {D : Type w}
  {A : ArithmeticStructure N S} {coding : Presentation D N}
  {application : D → D → D} {k s : D}
  {operations : coding.CodeOperations application k s}

def ofDefinitions (atoms : ArithmeticCodeAtoms.Definitions A coding operations) : Atoms :=
  ⟨atoms.equalFormula, atoms.kFormula, atoms.sFormula, atoms.appFormula, atoms.pairFormula⟩

variable (atoms : ArithmeticCodeAtoms.Definitions A coding operations)

@[simp] theorem tupleGraph_eq (arity : Nat) (args : Fin (arity + 1) → NTerm) (out : NTerm) :
    (ofDefinitions atoms).tupleGraph arity args out = atoms.tupleGraph arity args out := by
  induction arity generalizing out with
  | zero => rfl
  | succ arity ih =>
      simp only [Atoms.tupleGraph, ArithmeticCodeAtoms.Definitions.tupleGraph, ih]
      rfl

@[simp] theorem termGraph_eq (varTerms : Nat → NTerm) (out : NTerm) (t : Positive.Term) :
    (ofDefinitions atoms).termGraph varTerms out t = atoms.termGraph varTerms out t := by
  induction t generalizing varTerms out with
  | var => rfl
  | constantK => rfl
  | constantS => rfl
  | app f x ihf ihx =>
      simp only [Atoms.termGraph, ArithmeticCodeAtoms.Definitions.termGraph, ihf, ihx]
      rfl

@[simp] theorem tupleMember_eq (arity index : Nat) (args : Fin (arity + 1) → NTerm) :
    (ofDefinitions atoms).tupleMember arity index args = atoms.tupleMember arity index args := by
  simp only [Atoms.tupleMember, ArithmeticCodeAtoms.Definitions.tupleMember, tupleGraph_eq]

@[simp] theorem saturatedFormula_eq (arity index : Nat) :
    (ofDefinitions atoms).saturatedFormula arity index =
      FormulaTranslation.Definitions.saturatedFormula atoms arity index := by
  simp only [Atoms.saturatedFormula, FormulaTranslation.Definitions.saturatedFormula, tupleMember_eq]
  rfl

@[simp] theorem equationFormula_eq (varTerms : Nat → NTerm) (left right : Positive.Term) :
    (ofDefinitions atoms).equationFormula varTerms left right =
      FormulaTranslation.Definitions.equalFormula atoms varTerms left right := by
  simp only [Atoms.equationFormula, FormulaTranslation.Definitions.equalFormula, termGraph_eq]
  rfl

@[simp] theorem relationFormula_eq (varTerms : Nat → NTerm) (arity index : Nat)
    (args : Fin (arity + 1) → Positive.Term) :
    (ofDefinitions atoms).relationFormula varTerms arity index args =
      FormulaTranslation.Definitions.relationFormula atoms varTerms arity index args := by
  simp only [Atoms.relationFormula, FormulaTranslation.Definitions.relationFormula, termGraph_eq, tupleMember_eq]

@[simp] theorem translate_eq (p : Applicative.Formula) (varTerms : Nat → NTerm)
    (relationMap : Nat → Nat → Nat) :
    (ofDefinitions atoms).translate varTerms relationMap p =
      FormulaTranslation.Definitions.translate atoms varTerms relationMap p := by
  induction p generalizing varTerms relationMap <;>
    simp_all only [Atoms.translate, FormulaTranslation.Definitions.translate, equationFormula_eq,
      relationFormula_eq, saturatedFormula_eq]

/-- The same five builders are used in every source model. -/
noncomputable def fixedAtoms : Atoms where
  equalFormula := InternalAtomicDefinitions.equalFormula InternalConversionFormula.conversionFormula.val
  kFormula := InternalAtomicDefinitions.kFormula
  sFormula := InternalAtomicDefinitions.sFormula
  appFormula := InternalAtomicDefinitions.applicationFormula
  pairFormula := NativeAtomTranslation.pairFormula

@[simp] theorem ofDefinitions_fixed (A : ArithmeticStructure N S) (model : ModelsZ2 A)
    (sets : Nat → S) :
    ofDefinitions (InternalConversionFormula.definitions A model sets) = fixedAtoms := rfl

noncomputable def rawTranslate := fixedAtoms.translate

end FregeanECA.Research.Z2Reverse.UniformFormulaTranslation
