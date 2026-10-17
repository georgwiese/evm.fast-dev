import InitECandidate.Solver.ScratchList.Execution
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.ScratchList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def formals : List (MlS × ShapeHOL) := [(ofString "esz", .one), (ofString "cap", .one)]
def values (size capacity : BitVec 64) : List (ValueHOL 64) := [.val (.word size), .val (.word capacity)]
def rawLocals (size capacity : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "cap" then some (.val (.word capacity)) else if name = ofString "esz" then some (.val (.word size)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (size capacity : BitVec 64) (known : table (ofString "lst_new_scratch") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "lst_new_scratch") (values size capacity) = some (body, callee, .one) ∧
      callee.lookup (ofString "esz") = some (.val (.word size)) ∧ callee.lookup (ofString "cap") = some (.val (.word capacity)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values size capacity).length ∧
      ((formals.zip (values size capacity)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "lst_new_scratch") (values size capacity) =
      some (body, rawLocals size capacity, .one) := by
    simp only [lookupCodeHOLExact, known, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table
    (ofString "lst_new_scratch") (values size capacity) body (rawLocals size capacity) .one raw
  refine ⟨callee, called, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "esz" ≠ ofString "cap" from by decide]
  · rw [locals]
    simp [rawLocals]

/-- Actual scratch-list caller. The two real allocator calls plus this call
consume exactly three source clocks, preserving memory above the old cursor. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (scratch memory size capacity : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values size capacity))
    (known : source.code.lookup (ofString "lst_new_scratch") = some (formals, body, .one))
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (aligned : memory.toNat % 8 = 0) (headerRoom : memory.toNat + 24 ≤ scratch.toNat)
    (bufferRoom : memory.toNat + (size * capacity).toNat ≤ (header scratch).toNat)
    (mapped : ∀ offset ∈ ([0, 8, 16] : List Nat), source.memaddrs (header scratch + BitVec.ofNat 64 offset))
    (enough : 3 ≤ source.clock) :
    ∃ finalMemory : WitnessRadix.WordWrites.Memory,
      (∀ query : BitVec 64, Arenas.Outside memory scratch query → finalMemory query = source.memory query) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "lst_new_scratch") arguments continuation) =
        (let output := evaluateHOLFiniteState
          (WitnessRadix.QueryBranch.bind {Arenas.post source .down (header scratch) (size * capacity) with
            memory := finalMemory
            clock := source.clock - 3} name (header scratch)) continuation
         (output.1, restore source name output.2)) := by
  classical
  obtain ⟨callee, called, sizeLocal, capLocal⟩ := environment source.code.lookup size capacity known
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target, bodyRun, memoryEq, frame, preserved⟩ := execute entry scratch memory size capacity
    code scratchGlobal memoryGlobal sizeLocal capLocal aligned headerRoom bufferRoom mapped
    (by change 2 ≤ source.clock - 1; omega)
  have actual := Input.CallNormal.return_execute source target name .one (ofString "lst_new_scratch") arguments
    (values size capacity) body continuation callee .one (.val (.word (header scratch)))
    args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have clocks : source.clock - 1 - 2 = source.clock - 3 := by omega
  have restored : {target with locals := source.locals} = {Arenas.post source .down (header scratch) (size * capacity) with
      memory := target.memory
      clock := source.clock - 3} := by
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, Arenas.post, clocks] using callerFrame
  have nextEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    setVarHOLFinite (ofString name) (.val (.word (header scratch))) state) restored
  change Input.CallNormal.continuationEntry source target name (.val (.word (header scratch))) = _ at nextEq
  rw [nextEq] at actual
  exact ⟨target.memory, preserved, actual⟩

end InitECandidate.Solver.ScratchList

#print axioms InitECandidate.Solver.ScratchList.environment
#print axioms InitECandidate.Solver.ScratchList.call_execute
