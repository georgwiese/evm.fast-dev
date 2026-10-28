import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.ZeroAnyCost
import InitECandidate.Solver.Input.CopyAnyCost

namespace InitECandidate.Solver.Input.CurrentHash.MemoryCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current declaration entries, with all-outcome arithmetic-loop proofs
reused only after their actual Software bodies and ABI are checked. -/
theorem zero_entry (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one) := by
  simpa only [Code.name, Code.formals, Code.body, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_memzero, Zero.formals, Zero.body, shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
    using Code.installed code installed .memzero

theorem copy_entry (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one) :=
  CopyGeneral.original_code code installed

/-- All actual zero-call outcomes. No pointer alignment/mapping, successful
store, allocator room, future return or positive incoming clock is assumed. -/
theorem zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS))
    (arguments : List (ExpHOL 64)) (pointer : BitVec 64) (length : Nat) (small : length + 32 < 2^64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some (Zero.values pointer length)) :
    source.clock - (evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "memzero") arguments)).2.clock ≤
      ZeroAny.price length + 1 := by
  obtain ⟨callee, called, pointerCell, lengthCell⟩ := Zero.environment source.code.lookup pointer length (zero_entry source.code installed)
  exact ClockCost.call_current source destination (ofString "memzero") arguments (Zero.values pointer length)
    Zero.body callee .one (ZeroAny.price length) args called
    (ZeroAny.body_cost (callEntryStateHOLFinite source callee) length small lengthCell)

/-- The corresponding real copy call retains the same all-outcome scope. -/
theorem copy (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS))
    (arguments : List (ExpHOL 64)) (output input : BitVec 64) (length : Nat) (small : length + 32 < 2^64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some (CopyGeneral.values output input length)) :
    source.clock - (evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "memcpy") arguments)).2.clock ≤
      CopyAny.price length + 1 := by
  obtain ⟨callee, called, outputCell, inputCell, lengthCell⟩ := CopyGeneral.environment source.code.lookup output input length (copy_entry source.code installed)
  exact ClockCost.call_current source destination (ofString "memcpy") arguments (CopyGeneral.values output input length)
    Copy32.body callee .one (CopyAny.price length) args called
    (CopyAny.body_cost (callEntryStateHOLFinite source callee) length small lengthCell)

end InitECandidate.Solver.Input.CurrentHash.MemoryCost

#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryCost.zero_entry
#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryCost.copy_entry
#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryCost.zero
#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryCost.copy
