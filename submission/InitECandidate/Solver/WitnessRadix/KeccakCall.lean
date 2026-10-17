import InitECandidate.Solver.WitnessRadix.KeccakMapped
import InitECandidate.Solver.WitnessRadix.CodeEnvironment
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.WitnessRadix.Keccak
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 10000

def formals : List (MlS × ShapeHOL) := [(ofString "stp", .one)]
def values (pointer : BitVec 64) : List (ValueHOL 64) := [.val (.word pointer)]
def rawLocals (pointer : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "stp" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (pointer : BitVec 64)
    (code : codeFn (ofString "keccak_f1600") = some (formals, f1600Body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "keccak_f1600") (values pointer) = some (f1600Body, callee, .one) ∧
      callee.lookup (ofString "stp") = some (.val (.word pointer)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values pointer).length ∧
      ((formals.zip (values pointer)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "keccak_f1600") (values pointer) =
      some (f1600Body, rawLocals pointer, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, lookup, locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, lookup, ?_⟩
  rw [locals]; simp [rawLocals]

/-- Actual call of the fixed permutation function from mapped state words,
real code/oracle/argument facts, with exact byte/FFI update and one call clock. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (pointer : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values pointer))
    (code : source.code.lookup (ofString "keccak_f1600") = some (formals, f1600Body, .one))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle) (aligned : pointer.toNat % 8 = 0)
    (fits : pointer.toNat + 200 < 2 ^ 64)
    (mapped : ∀ word : Fin 25, source.memaddrs (byteAddress pointer (8 * word.val))) (enough : 1 ≤ source.clock) :
    ∃ bytes : List (BitVec 8), bytes.length = 200 ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "keccak_f1600") arguments) =
        (none, { post source pointer bytes with clock := source.clock - 1 }) := by
  classical
  obtain ⟨callee, lookup, stpLocal⟩ := environment source.code.lookup pointer code
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨bytes, length, bodyRun⟩ := f1600_mapped entry pointer stpLocal oracleEq aligned fits mapped
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "keccak_f1600")
    arguments (values pointer) f1600Body callee .one (.val (.word 0#64)) (emptyLocalsHOLFinite (post entry pointer bytes))
    args lookup (by omega) bodyRun (by simp [shapeEqHOL, shapeOfHOLExact])
  exact ⟨bytes, length, callRun⟩

end InitECandidate.Solver.WitnessRadix.Keccak

#print axioms InitECandidate.Solver.WitnessRadix.Keccak.environment
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.call_execute
