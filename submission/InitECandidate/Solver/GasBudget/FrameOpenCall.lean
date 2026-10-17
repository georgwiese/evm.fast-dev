import InitECandidate.Solver.GasBudget.FrameOpenExecution

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def formals : List (MlS × ShapeHOL) := [(ofString "msg", .one), (ofString "kind", .one)]
def values (message kind : BitVec 64) : List (ValueHOL 64) := [.val (.word message), .val (.word kind)]
def rawLocals (message kind : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "kind" then some (.val (.word kind)) else if name = ofString "msg" then some (.val (.word message)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (message kind : BitVec 64) (known : table (ofString "frame_open") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "frame_open") (values message kind) = some (body, callee, .one) ∧
      callee.lookup (ofString "msg") = some (.val (.word message)) ∧ callee.lookup (ofString "kind") = some (.val (.word kind)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values message kind).length ∧
      ((formals.zip (values message kind)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "frame_open") (values message kind) = some (body, rawLocals message kind, .one) := by
    simp only [lookupCodeHOLExact, known, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table
    (ofString "frame_open") (values message kind) body (rawLocals message kind) .one raw
  refine ⟨callee, called, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "msg" ≠ ofString "kind" from by decide]
  · rw [locals]
    simp [rawLocals]

/-- Actual scoped frame_open call, with original child/continuation activation
and preservation of all memory outside the incoming live arena. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (rest : ProgHOL 64)
    (scratch lower message empty parent continuation kind : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values message kind))
    (known : source.code.lookup (ofString "frame_open") = some (formals, body, .one))
    (newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (enough : words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 ≤ source.clock) :
    ∃ (finalMemory : Memory) (spent : Nat),
      spent ≤ words.length.toNat ∧ regularBudget finalMemory (FrameNew.framePointer scratch) = words.gas.toNat ∧
      (∀ query, Arenas.Outside lower scratch query → finalMemory query = source.memory query) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "frame_open") arguments rest) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with
          globals := (((source.globals.update (ofString "frame_mem_ptr", .val (.word (FrameNew.memoryPointer lower)))).update
            (ofString "scratch_ptr", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))).update
            (ofString "ev", .val (.word (FrameNew.framePointer scratch)))).update
            (ofString "cur_cont", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))
          memory := finalMemory
          clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent)}
          name (FrameNew.framePointer scratch)) rest
         (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, messageLocal, kindLocal⟩ := environment source.code.lookup message kind known
  let calleeSource := callEntryStateHOLFinite source callee
  have calleeEntry : FrameNew.Entry calleeSource scratch lower message empty words addresses keys addressCount keyCount :=
    entry.relocals_clock callee (source.clock - 1)
  obtain ⟨target, spent, spentBound, bodyRun, frame, budget, outside⟩ := execute calleeSource scratch lower message empty parent continuation kind words
    addresses keys addressCount keyCount calleeEntry newCode messageLocal kindLocal evGlobal continuationGlobal room
    (by change words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 ≤ source.clock - 1; omega)
  have actual := Input.CallNormal.return_execute source target name .one (ofString "frame_open") arguments
    (values message kind) body rest callee .one (.val (.word (FrameNew.framePointer scratch)))
    args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have clocks : source.clock - 1 - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 + spent) =
      source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent) := by omega
  have restored : {target with locals := source.locals} = {source with
      globals := (((source.globals.update (ofString "frame_mem_ptr", .val (.word (FrameNew.memoryPointer lower)))).update
        (ofString "scratch_ptr", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))).update
        (ofString "ev", .val (.word (FrameNew.framePointer scratch)))).update
        (ofString "cur_cont", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))
      memory := target.memory
      clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent)} := by
    simpa only [emptyLocalsHOLFinite, calleeSource, callEntryStateHOLFinite, clocks] using callerFrame
  have nextEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    setVarHOLFinite (ofString name) (.val (.word (FrameNew.framePointer scratch))) state) restored
  change Input.CallNormal.continuationEntry source target name (.val (.word (FrameNew.framePointer scratch))) = _ at nextEq
  rw [nextEq] at actual
  exact ⟨target.memory, spent, spentBound, budget, outside, actual⟩

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.environment
#print axioms InitECandidate.Solver.GasBudget.FrameOpen.call_execute
