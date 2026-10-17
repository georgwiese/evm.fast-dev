import InitECandidate.Solver.JumpDest.Execution
import InitECandidate.Solver.JumpDest.Environment
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual scoped compute_jumpdests call, with its own body/allocator/clear/
scan executions derived. The earlier-memory frame refers to the incoming
scratch cursor; no preservation oracle or assumed callee result is used. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (scratch memory code length : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      arguments = some (values code length))
    (known : source.code.lookup (ofString "compute_jumpdests") = some (formals, body, .one))
    (scratchCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (aligned : memory.toNat % 8 = 0) (fits : length.toNat + 63 < 2 ^ 64)
    (room : memory.toNat + bitmapBytes length.toNat ≤ scratch.toNat)
    (codeMapped : ∀ offset < length.toNat,
      source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress code offset)))
    (bitmapMapped : ∀ offset, offset + 8 ≤ bitmapBytes length.toNat → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress (Arenas.rounded .down scratch (bytesWord length)) offset))
    (enough : length.toNat + WitnessRadix.Zero.price (bitmapBytes length.toNat) + 3 ≤ source.clock) :
    ∃ (finalMemory : WitnessRadix.WordWrites.Memory) (spent : Nat),
      spent ≤ length.toNat ∧
      (∀ query : BitVec 64, scratch.toNat ≤ query.toNat → finalMemory query = source.memory query) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "compute_jumpdests") arguments continuation) =
        (let output := evaluateHOLFiniteState
          (WitnessRadix.QueryBranch.bind
            {Arenas.post source .down scratch (bytesWord length) with
              memory := finalMemory
              clock := source.clock - (WitnessRadix.Zero.price (bitmapBytes length.toNat) + 3 + spent)}
            name (Arenas.rounded .down scratch (bytesWord length))) continuation
         (output.1, restore source name output.2)) := by
  classical
  obtain ⟨callee, called, codeLocal, nLocal⟩ := environment source.code.lookup code length known
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target, spent, spentBound, bodyRun, frame, preserved⟩ := execute entry scratch memory code length
    scratchCode zeroCode scratchGlobal memoryGlobal codeLocal nLocal aligned fits room codeMapped bitmapMapped
    (by change length.toNat + WitnessRadix.Zero.price (bitmapBytes length.toNat) + 2 ≤ source.clock - 1; omega)
  have actual := Input.CallNormal.return_execute source target name .one (ofString "compute_jumpdests") arguments
    (values code length) body continuation callee .one (.val (.word (Arenas.rounded .down scratch (bytesWord length))))
    args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have clocks : source.clock - 1 - (WitnessRadix.Zero.price (bitmapBytes length.toNat) + 2 + spent) =
      source.clock - (WitnessRadix.Zero.price (bitmapBytes length.toNat) + 3 + spent) := by omega
  have restored : {target with locals := source.locals} =
      {Arenas.post source .down scratch (bytesWord length) with
        memory := target.memory
        clock := source.clock - (WitnessRadix.Zero.price (bitmapBytes length.toNat) + 3 + spent)} := by
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, Arenas.post, clocks] using callerFrame
  have nextEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    setVarHOLFinite (ofString name) (.val (.word (Arenas.rounded .down scratch (bytesWord length)))) state) restored
  change Input.CallNormal.continuationEntry source target name (.val (.word (Arenas.rounded .down scratch (bytesWord length)))) = _ at nextEq
  rw [nextEq] at actual
  exact ⟨target.memory, spent, spentBound, preserved, actual⟩

/-- Conditional literal relaxations. The caller must derive its actual code
length; these numbers price source clocks, not target instructions. -/
theorem caller_budget_131072 (length : Nat) (bounded : length ≤ 131072) :
    length + WitnessRadix.Zero.price (bitmapBytes length) + 3 ≤ 131588 := by
  simp only [WitnessRadix.Zero.price, bitmapBytes]
  omega

theorem caller_budget_65536 (length : Nat) (bounded : length ≤ 65536) :
    length + WitnessRadix.Zero.price (bitmapBytes length) + 3 ≤ 65796 := by
  simp only [WitnessRadix.Zero.price, bitmapBytes]
  omega

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.call_execute
#print axioms InitECandidate.Solver.JumpDest.caller_budget_131072
#print axioms InitECandidate.Solver.JumpDest.caller_budget_65536
