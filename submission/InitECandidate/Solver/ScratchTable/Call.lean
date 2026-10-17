import InitECandidate.Solver.ScratchTable.Execution
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.ScratchTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def formals : List (MlS × ShapeHOL) := [(ofString "key_len", .one), (ofString "cap", .one)]
def values : List (ValueHOL 64) := [.val (.word 20#64), .val (.word 4#64)]
def rawLocals (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "cap" then some (.val (.word 4#64)) else if name = ofString "key_len" then some (.val (.word 20#64)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (known : table (ofString "htab_new_scratch") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "htab_new_scratch") values = some (body, callee, .one) ∧
      callee.lookup (ofString "key_len") = some (.val (.word 20#64)) ∧
      callee.lookup (ofString "cap") = some (.val (.word 4#64)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = values.length ∧
      ((formals.zip values).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "htab_new_scratch") values = some (body, rawLocals, .one) := by
    simp only [lookupCodeHOLExact, known, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table
    (ofString "htab_new_scratch") values body rawLocals .one raw
  refine ⟨callee, called, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "key_len" ≠ ofString "cap" from by decide]
  · rw [locals]
    simp [rawLocals]

/-- The actual (20,4) scratch delete-table call consumes12source clocks,
reserves272aligned bytes and preserves all memory at/above the old cursor. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (scratch memory : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (known : source.code.lookup (ofString "htab_new_scratch") = some (formals, body, .one))
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (scratchAligned : scratch.toNat % 8 = 0) (memoryAligned : memory.toNat % 8 = 0)
    (room : memory.toNat + 272 ≤ scratch.toNat)
    (mapped : ∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (cursor scratch 72 + BitVec.ofNat 64 offset))
    (usedMapped : source.memaddrs (cursor scratch 208))
    (enough : 12 ≤ source.clock) :
    ∃ finalMemory : WitnessRadix.WordWrites.Memory,
      (∀ query : BitVec 64, Arenas.Outside memory scratch query → finalMemory query = source.memory query) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new_scratch") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with
          globals := source.globals.update (ofString "scratch_ptr", .val (.word (cursor scratch 272)))
          memory := finalMemory
          clock := source.clock - 12} name (cursor scratch 72)) continuation
         (output.1, restore source name output.2)) := by
  classical
  obtain ⟨callee, called, keyLocal, capLocal⟩ := environment source.code.lookup known
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target, bodyRun, memoryEq, frame, preserved⟩ := execute entry scratch memory code zeroCode
    scratchGlobal memoryGlobal keyLocal capLocal scratchAligned memoryAligned room mapped usedMapped
    (by change 11 ≤ source.clock - 1; omega)
  have actual := Input.CallNormal.return_execute source target name .one (ofString "htab_new_scratch") arguments values
    body continuation callee .one (.val (.word (cursor scratch 72))) args called (by omega) bodyRun
    (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have clocks : source.clock - 1 - 11 = source.clock - 12 := by omega
  have restored : {target with locals := source.locals} = {source with
      globals := source.globals.update (ofString "scratch_ptr", .val (.word (cursor scratch 272)))
      memory := target.memory
      clock := source.clock - 12} := by
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, clocks] using callerFrame
  have nextEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    setVarHOLFinite (ofString name) (.val (.word (cursor scratch 72))) state) restored
  change Input.CallNormal.continuationEntry source target name (.val (.word (cursor scratch 72))) = _ at nextEq
  rw [nextEq] at actual
  exact ⟨target.memory, preserved, actual⟩

end InitECandidate.Solver.ScratchTable

#print axioms InitECandidate.Solver.ScratchTable.environment
#print axioms InitECandidate.Solver.ScratchTable.call_execute
