import InitECandidate.Solver.MutableTable.HashByteRuntime.Execution
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Call

namespace InitECandidate.Solver.MutableTable.HashByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix
open MemeqByteRuntime (price)

def values (length : Nat) (pointer : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word pointer), .val (.word (BitVec.ofNat 64 (length)))]
def rawLocals (length : Nat) (pointer : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "key_len" then some (.val (.word (BitVec.ofNat 64 (length)))) else
  if name = ofString "p" then some (.val (.word pointer)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (length : Nat) (pointer : BitVec 64) (known : table (ofString "htab_hash") = some (Hash.formals, Hash.body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "htab_hash") (values length pointer) = some (Hash.body, callee, .one) ∧
      callee.lookup (ofString "p") = some (.val (.word pointer)) ∧
      callee.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (length)))) := by
  have valid : (Hash.formals.map Prod.fst).Nodup ∧ Hash.formals.length = (values length pointer).length ∧
      ((Hash.formals.zip (values length pointer)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [Hash.formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "htab_hash") (values length pointer) = some (Hash.body, rawLocals length pointer, .one) := by
    simp only [lookupCodeHOLExact, known, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table
    (ofString "htab_hash") (values length pointer) Hash.body (rawLocals length pointer) .one raw
  refine ⟨callee, called, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "p" ≠ ofString "key_len" from by decide]
  · rw [locals]
    simp [rawLocals]

/-- Original generic hash caller, derived from mapped input bytes at either
alignment. The caller allowance is8 clocks for28-byte keys and12 for60-byte
keys. Memory/control/FFI are unchanged; no distribution hypothesis is used. -/
theorem call_of_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values length pointer))
    (known : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (small : length ≤ 64) (not20 : length ≠ 20) (not32 : length ≠ 32) (not52 : length ≠ 52)
    (mapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset)))
    (enough : price length + 1 ≤ source.clock) :
    ∃ digest, evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_hash") arguments continuation) =
      (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - (price length + 1)} name digest) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, pLocal, lenLocal⟩ := environment source.code.lookup length pointer known
  let entry := callEntryStateHOLFinite source callee
  let bytes := MemeqByteRuntime.observed source pointer
  have reads : ∀ index < length, @panMemLoadByteHOL 64 _ entry.memory entry.memaddrs
      (fun address => Classical.propDecidable (entry.memaddrs address)) entry.be (pointer + BitVec.ofNat 64 index) = some (bytes index) := by
    intro index inside
    exact MemeqByteRuntime.observed_read source pointer index (mapped index inside)
  obtain ⟨digest, target, run, frame⟩ := execute entry pointer length bytes pLocal lenLocal reads small not20 not32 not52
    (by change price length ≤ source.clock - 1; omega)
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1 - price length} := frame
  have actual := Input.CallNormal.pure_return_execute source target name (ofString "htab_hash") arguments _ Hash.body continuation callee digest
    (price length) args called (by omega) run callerFrame
  have subtract : source.clock - 1 - price length = source.clock - (price length + 1) := by omega
  exact ⟨digest, by simpa only [subtract] using actual⟩

end InitECandidate.Solver.MutableTable.HashByteRuntime

#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.environment
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.call_of_mapped
