import InitECandidate.Solver.GasBudget.FrameNewEntry

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def formals : List (MlS × ShapeHOL) := [(ofString "msg", .one)]

/-- Real frame_new caller ABI and lexical restoration, with the complete
constructor derived. The returned frame's initialized regular ledger equals
MSG_GAS, and all input read cells survive. Caller source allowance is
n+memzero_price(bitmap_bytes(n))+38, not a target runtime bound. -/
theorem call_execute_full (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (scratch lower message empty : BitVec 64) (words : MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word message)])
    (known : source.code.lookup (ofString "frame_new") = some (formals, body, .one))
    (enough : words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 38 ≤ source.clock) :
    ∃ (finalMemory : Memory) (spent : Nat),
      spent ≤ words.length.toNat ∧
      regularBudget finalMemory (framePointer scratch) = words.gas.toNat ∧
      GasSeed finalMemory (framePointer scratch) words.gas ∧
      (∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩,
        finalMemory cell.1 = source.memory cell.1) ∧
      (∀ query, Arenas.Outside lower scratch query → finalMemory query = source.memory query) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "frame_new") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with
          globals := (source.globals.update (ofString "frame_mem_ptr", .val (.word (memoryPointer lower)))).update
            (ofString "scratch_ptr", .val (.word (finalScratch scratch words.length)))
          memory := finalMemory
          clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 38 + spent)}
          name (framePointer scratch)) continuation
         (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, messageLocal⟩ := Input.CallNormal.unary_environment source.code.lookup
    (ofString "frame_new") "msg" body message known
  let calleeSource := callEntryStateHOLFinite source callee
  have calleeEntry : Entry calleeSource scratch lower message empty words addresses keys addressCount keyCount :=
    entry.relocals_clock callee (source.clock - 1)
  obtain ⟨target, spent, spentBound, bodyRun, frame, budget, seed, preserved, outsideFrame⟩ := execute_full calleeSource scratch lower message empty words
    addresses keys addressCount keyCount calleeEntry.code calleeEntry.memoryCode calleeEntry.jumpCode calleeEntry.logCode
    calleeEntry.tableCode calleeEntry.countCode calleeEntry.scratchGlobal calleeEntry.lowerGlobal messageLocal calleeEntry.emptyGlobal
    calleeEntry.scratchAligned calleeEntry.lowerAligned calleeEntry.lengthFits calleeEntry.room calleeEntry.arena
    calleeEntry.messageMapped calleeEntry.messageCells calleeEntry.messageProtected calleeEntry.inputMapped calleeEntry.inputCells
    calleeEntry.inputProtected calleeEntry.codeMapped
    (by change words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 37 ≤ source.clock - 1; omega)
  have actual := Input.CallNormal.return_execute source target name .one (ofString "frame_new") arguments
    [.val (.word message)] body continuation callee .one (.val (.word (framePointer scratch)))
    args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have clocks : source.clock - 1 - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 37 + spent) =
      source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 38 + spent) := by omega
  have restored : {target with locals := source.locals} = {source with
      globals := (source.globals.update (ofString "frame_mem_ptr", .val (.word (memoryPointer lower)))).update
        (ofString "scratch_ptr", .val (.word (finalScratch scratch words.length)))
      memory := target.memory
      clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 38 + spent)} := by
    simpa only [emptyLocalsHOLFinite, calleeSource, callEntryStateHOLFinite, clocks] using callerFrame
  have nextEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    setVarHOLFinite (ofString name) (.val (.word (framePointer scratch))) state) restored
  change Input.CallNormal.continuationEntry source target name (.val (.word (framePointer scratch))) = _ at nextEq
  rw [nextEq] at actual
  exact ⟨target.memory, spent, spentBound, budget, seed, preserved, outsideFrame, actual⟩

theorem caller_budget_131072 (length : Nat) (bounded : length ≤ 131072) :
    length + WitnessRadix.Zero.price (JumpDest.bitmapBytes length) + 38 ≤ 131623 := by
  simp only [WitnessRadix.Zero.price, JumpDest.bitmapBytes]
  omega

theorem caller_budget_65536 (length : Nat) (bounded : length ≤ 65536) :
    length + WitnessRadix.Zero.price (JumpDest.bitmapBytes length) + 38 ≤ 65831 := by
  simp only [WitnessRadix.Zero.price, JumpDest.bitmapBytes]
  omega

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (scratch lower message empty : BitVec 64) (words : MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word message)])
    (known : source.code.lookup (ofString "frame_new") = some (formals, body, .one))
    (enough : words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 38 ≤ source.clock) :
    ∃ (finalMemory : Memory) (spent : Nat),
      spent ≤ words.length.toNat ∧
      regularBudget finalMemory (framePointer scratch) = words.gas.toNat ∧
      (∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩,
        finalMemory cell.1 = source.memory cell.1) ∧
      (∀ query, Arenas.Outside lower scratch query → finalMemory query = source.memory query) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "frame_new") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with
          globals := (source.globals.update (ofString "frame_mem_ptr", .val (.word (memoryPointer lower)))).update
            (ofString "scratch_ptr", .val (.word (finalScratch scratch words.length)))
          memory := finalMemory
          clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 38 + spent)}
          name (framePointer scratch)) continuation
         (output.1, restore source name output.2)) := by
  obtain ⟨memory, spent, bound, budget, seed, preserved, outside, run⟩ := call_execute_full source name arguments continuation
    scratch lower message empty words addresses keys addressCount keyCount entry args known enough
  exact ⟨memory, spent, bound, budget, preserved, outside, run⟩

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.call_execute
#print axioms InitECandidate.Solver.GasBudget.FrameNew.caller_budget_131072
#print axioms InitECandidate.Solver.GasBudget.FrameNew.caller_budget_65536

#print axioms InitECandidate.Solver.GasBudget.FrameNew.call_execute_full
