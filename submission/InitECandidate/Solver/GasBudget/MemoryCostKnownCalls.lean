import InitECandidate.Solver.GasBudget.U256MemoryValues
import InitECandidate.Solver.GasBudget.MemoryGasCostValue
import InitECandidate.Solver.Input.KnownUnaryPrefix

namespace InitECandidate.Solver.GasBudget.MemoryCostCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Input.RlpWrite

inductive Kind where | sat | zero | ceil | words | cost
def Argument : Kind → Type | .sat | .zero => U256Value.Words | .ceil | .words | .cost => BitVec 64
def Kind.name : Kind → MlS
  | .sat => ofString "sat_word" | .zero => ofString "u256_is_zero" | .ceil => ofString "ceil32"
  | .words => ofString "words_of" | .cost => ofString "memory_gas_cost"
def Kind.formal : Kind → MlS
  | .sat | .ceil => ofString "v" | .zero => ofString "a" | .words => ofString "n" | .cost => ofString "size"
def Kind.argumentShape : Kind → ShapeHOL | .sat | .zero => U256Value.tupleShape | .ceil | .words | .cost => .one
def Kind.body : Kind → ProgHOL 64
  | .sat => SatWord.body | .zero => U256Zero.body | .ceil => Ceil32.body | .words => WordsOf.body | .cost => MemoryGasCost.body
def Kind.price : Kind → Nat | .sat | .zero => 0 | .ceil => 1 | .words => 2 | .cost => 5
def Kind.input : (kind : Kind) → Argument kind → ValueHOL 64
  | .sat, quadBits | .zero, quadBits => U256Value.tuple quadBits
  | .ceil, word | .words, word | .cost, word => .val (.word word)
def Kind.result : (kind : Kind) → Argument kind → ValueHOL 64
  | .sat, quadBits => .val (.word (SatWord.resultWord quadBits))
  | .zero, quadBits => .val (.word (U256Zero.resultWord quadBits))
  | .ceil, word => .val (.word (Ceil32.resultWord word))
  | .words, word => .val (.word (WordsOf.resultWord word))
  | .cost, word => .val (.word (MemoryGasCost.resultWord word))

theorem original_code (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup kind.name = some ([(kind.formal, kind.argumentShape)], kind.body, .one) := by
  cases kind with
  | sat => exact SatWord.original_code code installed
  | zero => exact U256Zero.original_code code installed
  | ceil => exact WordsOf.ceil_code code installed
  | words => exact WordsOf.original_code code installed
  | cost =>
    simpa only [Kind.name, Kind.formal, Kind.argumentShape, Kind.body, MemoryGasCost.body, MemoryCostEffects.Kind.name,
      MemoryCostEffects.Kind.body, MemoryCostEffects.Kind.signature, MemoryCostEffects.Kind.original,
      Guest.guestFn_memory_gas_cost, shapeToHOL, List.map_cons, List.map_nil, paramToHOL]
      using MemoryCostEffects.entry code installed .memory_gas_cost

theorem pure_body (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code kind.body := by
  cases kind with
  | sat => exact ArithmeticEffects.pure_sat_word code (OriginalCodeEnvironment.arithmetic code installed)
  | zero => exact ArithmeticEffects.pure_u256_is_zero code (OriginalCodeEnvironment.arithmetic code installed)
  | ceil => exact MemoryCostEffects.pure_ceil32 code installed
  | words => exact MemoryCostEffects.pure_words_of code installed
  | cost => exact MemoryCostEffects.pure_memory_gas_cost code installed

theorem price_body (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code kind.body kind.price := by
  cases kind with
  | sat => exact ArithmeticEffects.price_sat_word code (OriginalCodeEnvironment.arithmetic code installed)
  | zero => exact ArithmeticEffects.price_u256_is_zero code (OriginalCodeEnvironment.arithmetic code installed)
  | ceil => exact MemoryCostEffects.price_ceil32 code installed
  | words => exact MemoryCostEffects.price_words_of code installed
  | cost => exact MemoryCostEffects.price_memory_gas_cost code installed

theorem determines (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) (argument : Argument kind)
    (entry target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) (codeEq : entry.code = code)
    (binding : entry.locals.lookup kind.formal = some (kind.input argument))
    (normal : evaluateHOLFiniteState entry kind.body = (some (.returned returned), target)) : returned = kind.result argument := by
  have current : Input.OriginalCode.Installed entry.code := by rw [codeEq]; exact installed
  cases kind with
  | sat =>
    have same := congrArg Prod.fst (normal.symm.trans (SatWord.execute entry argument binding))
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq, Kind.result] using same
  | zero =>
    have same := congrArg Prod.fst (normal.symm.trans (U256Zero.execute entry argument binding))
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq, Kind.result] using same
  | ceil => exact (Ceil32.normal entry target argument current binding returned normal).1
  | words => exact (WordsOf.normal entry target argument current binding returned normal).1
  | cost => exact MemoryGasCost.normal_value entry target argument current binding returned normal

/-- The actual call supplies its helper run, value, clock allowance and a
canonical continuation retaining all nonlocal state. No future model or
successful argument lookup is assumed beyond the stated current read. -/
theorem normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (expression : ExpHOL 64) (continuation : ProgHOL 64) (argument : Argument kind) (returned : ValueHOL 64)
    (installed : Input.OriginalCode.Installed source.code) (read : WitnessRadix.QueryBranch.eval source expression = some (kind.input argument))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one kind.name [expression] continuation) = (some (.returned returned), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ kind.price + 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (kind.result argument) {source with clock := source.clock - paid} ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧ post = WitnessRadix.QueryBranch.restore source name inner := by
  exact Input.KnownUnaryPrefix.normal source post name .one kind.name kind.formal kind.argumentShape .one kind.body kind.price expression continuation
    (kind.input argument) (kind.result argument) returned (original_code kind source.code installed) (pure_body kind source.code installed)
    (price_body kind source.code installed) read (determines kind source.code installed argument) run

theorem installed_after {source ready : PanSemStateFiniteExact 64 Guest.HostMemory}
    (fields : Input.LocalEffects.erase ready = Input.LocalEffects.erase source)
    (installed : Input.OriginalCode.Installed source.code) : Input.OriginalCode.Installed ready.code := by
  have code := congrArg PanSemStateFiniteExact.code fields
  change ready.code = source.code at code
  rw [code]
  exact installed

end InitECandidate.Solver.GasBudget.MemoryCostCalls

#print axioms InitECandidate.Solver.GasBudget.MemoryCostCalls.determines
#print axioms InitECandidate.Solver.GasBudget.MemoryCostCalls.normal
