import FregeanECA.Part2.OracleFiniteSyntax

/-! Exact code/selector equations used by the finite-table satisfaction proof. -/
namespace FregeanECA.Part2.Oracle
open FFL FFL.FirstOrder

theorem isSubformula_iff (formula : Semisentence language n) (code : Nat) :
    isSubformula (formulaCode formula) code = 1 ↔
      ∃ node ∈ formulaParts formula, Encodable.encode node = code := by
  simp [isSubformula, formulaCode]

theorem isSubterm_iff (formula : Semisentence language n) (code : Nat) :
    isSubterm (formulaCode formula) code = 1 ↔
      ∃ node ∈ formulaTermParts formula, Encodable.encode node = code := by
  simp [isSubterm, formulaCode]

@[simp] theorem packSentence_encode (sentence : Sentence language) :
    packSentence (Encodable.encode sentence) = formulaCode sentence := by
  simp [packSentence]

@[simp] theorem isSentence_encode (sentence : Sentence language) :
    isSentence (Encodable.encode sentence) = 1 := by
  simp [isSentence]

theorem isSentence_iff (code : Nat) :
    isSentence code = 1 ↔ ∃ sentence : Sentence language,
      Encodable.decode code = some sentence := by
  simp [isSentence, Option.isSome_iff_exists]

theorem packSentence_of_decode (code : Nat) (sentence : Sentence language)
    (decoded : Encodable.decode code = some sentence) :
    packSentence code = formulaCode sentence := by
  simp [packSentence, decoded]

@[simp] theorem formulaTag_verum  :
    formulaTag (formulaCode (.verum : Semisentence language n)) = 0 := by
  simp [formulaTag, formulaCode]

@[simp] theorem formulaTag_falsum  :
    formulaTag (formulaCode (.falsum : Semisentence language n)) = 1 := by
  simp [formulaTag, formulaCode]

@[simp] theorem formulaTag_rel (symbol : language.Rel arity) (arguments : Fin arity → ClosedSemiterm language n) :
    formulaTag (formulaCode (.rel symbol arguments)) = 2 := by
  simp [formulaTag, formulaCode]

@[simp] theorem formulaTag_nrel (symbol : language.Rel arity) (arguments : Fin arity → ClosedSemiterm language n) :
    formulaTag (formulaCode (.nrel symbol arguments)) = 3 := by
  simp [formulaTag, formulaCode]

@[simp] theorem formulaTag_and (left right : Semisentence language n) :
    formulaTag (formulaCode (.and left right)) = 4 := by
  simp [formulaTag, formulaCode]

@[simp] theorem formulaTag_or (left right : Semisentence language n) :
    formulaTag (formulaCode (.or left right)) = 5 := by
  simp [formulaTag, formulaCode]

@[simp] theorem formulaTag_all (body : Semisentence language (n+1)) :
    formulaTag (formulaCode (.all body)) = 6 := by
  simp [formulaTag, formulaCode]

@[simp] theorem formulaTag_exs (body : Semisentence language (n+1)) :
    formulaTag (formulaCode (.exs body)) = 7 := by
  simp [formulaTag, formulaCode]

@[simp] theorem formulaArity_rel (symbol : language.Rel arity)
    (arguments : Fin arity → ClosedSemiterm language n) :
    formulaArity (formulaCode (.rel symbol arguments)) = arity := by
  simp [formulaArity, formulaCode]

@[simp] theorem formulaSymbol_rel (symbol : language.Rel arity)
    (arguments : Fin arity → ClosedSemiterm language n) :
    formulaSymbol (formulaCode (.rel symbol arguments)) = symbol := by
  simp [formulaSymbol, formulaCode]

@[simp] theorem formulaArity_nrel (symbol : language.Rel arity)
    (arguments : Fin arity → ClosedSemiterm language n) :
    formulaArity (formulaCode (.nrel symbol arguments)) = arity := by
  simp [formulaArity, formulaCode]

@[simp] theorem formulaSymbol_nrel (symbol : language.Rel arity)
    (arguments : Fin arity → ClosedSemiterm language n) :
    formulaSymbol (formulaCode (.nrel symbol arguments)) = symbol := by
  simp [formulaSymbol, formulaCode]

@[simp] theorem formulaArgument_rel (symbol : language.Rel arity)
    (arguments : Fin arity → ClosedSemiterm language n) (i : Fin arity) :
    formulaArgument (formulaCode (.rel symbol arguments)) i.val = termCode (arguments i) := by
  simp [formulaArgument, formulaCode, i.isLt]

@[simp] theorem formulaArgument_nrel (symbol : language.Rel arity)
    (arguments : Fin arity → ClosedSemiterm language n) (i : Fin arity) :
    formulaArgument (formulaCode (.nrel symbol arguments)) i.val = termCode (arguments i) := by
  simp [formulaArgument, formulaCode, i.isLt]

@[simp] theorem formulaLeft_and (left right : Semisentence language n) :
    formulaLeft (formulaCode (.and left right)) = formulaCode left := by
  simp [formulaLeft, formulaCode]

@[simp] theorem formulaRight_and (left right : Semisentence language n) :
    formulaRight (formulaCode (.and left right)) = formulaCode right := by
  simp [formulaRight, formulaCode]

@[simp] theorem formulaLeft_or (left right : Semisentence language n) :
    formulaLeft (formulaCode (.or left right)) = formulaCode left := by
  simp [formulaLeft, formulaCode]

@[simp] theorem formulaRight_or (left right : Semisentence language n) :
    formulaRight (formulaCode (.or left right)) = formulaCode right := by
  simp [formulaRight, formulaCode]

@[simp] theorem formulaLeft_all (body : Semisentence language (n+1)) :
    formulaLeft (formulaCode (.all body)) = formulaCode body := by
  simp [formulaLeft, formulaCode]

@[simp] theorem formulaLeft_exs (body : Semisentence language (n+1)) :
    formulaLeft (formulaCode (.exs body)) = formulaCode body := by
  simp [formulaLeft, formulaCode]

@[simp] theorem termTag_bvar (i : Fin n) :
    termTag (termCode (.bvar i)) = 0 := by simp [termTag, termCode]

@[simp] theorem termVariable_bvar (i : Fin n) :
    termVariable (termCode (.bvar i)) = i.val := by simp [termVariable, termCode]

@[simp] theorem termTag_func (symbol : language.Func arity)
    (arguments : Fin arity → ClosedSemiterm language n) :
    termTag (termCode (.func symbol arguments)) = 1 := by
  simp [termTag, termCode]

@[simp] theorem termArity_func (symbol : language.Func arity)
    (arguments : Fin arity → ClosedSemiterm language n) :
    termArity (termCode (.func symbol arguments)) = arity := by
  simp [termArity, termCode]

@[simp] theorem termSymbol_func (symbol : language.Func arity)
    (arguments : Fin arity → ClosedSemiterm language n) :
    termSymbol (termCode (.func symbol arguments)) = symbol := by
  simp [termSymbol, termCode]

@[simp] theorem termArgument_func (symbol : language.Func arity)
    (arguments : Fin arity → ClosedSemiterm language n) (i : Fin arity) :
    termArgument (termCode (.func symbol arguments)) i.val = termCode (arguments i) := by
  simp [termArgument, termCode, i.isLt]

end FregeanECA.Part2.Oracle
