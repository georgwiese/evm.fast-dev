import InitECandidate.Solver.Input.CurrentHash.HashPrefix
import InitECandidate.Solver.Input.CurrentStartup.MainDecodedPayload
import InitECandidate.Solver.Input.CurrentStartup.AllocationFrontier

namespace InitECandidate.Solver.Input.CurrentHash.RootEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Main's actual first action after the returned decoder. -/
def actions : List CallPrefix.Action := (CallPrefix.cutAt 1 HashPrefix.decoderTail).1
def afterRoot : ProgHOL 64 := (CallPrefix.cutAt 1 HashPrefix.decoderTail).2
def arguments : List (ExpHOL 64) := [.var .local (ofString "si"), .var .local (ofString "root")]

theorem source_shape : HashPrefix.decoderTail = CallPrefix.program actions afterRoot :=
  (CallPrefix.reconstructAt 1 HashPrefix.decoderTail).symm

theorem actions_shape : actions = [.scoped (ofString "root") .one (ofString "alloc") [.const 32#64]] := by
  unfold actions
  rw [HashPrefix.source_shape, HashPrefix.actions_shape]
  rfl

theorem after_shape : afterRoot = .seq
    (.call (some (none, none)) (ofString "htr_new_payload_request") arguments) HashPrefix.afterHash := by
  unfold afterRoot
  rw [HashPrefix.source_shape, HashPrefix.actions_shape]
  rfl

/-- Physical payload data at the genuine hash caller. The decoder snapshot
stays indexed by its original post-state; only proved memory/heap facts move
through the following allocation, whose globals really do change. -/
structure Ready (input : Guest.InputBlob) (decoded current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (origin : CurrentStartup.DecoderOrigin) (record gasWord requestRecord root array : BitVec 64)
    (payloadLength start size : Nat) : Prop where
  run : CurrentStartup.MainSeparatedInput.RootRun input origin
  snapshot : CurrentStartup.WitnessHeadersReturn.Snapshot (decoderOrigin := origin) input decoded origin.pointer origin.word
    record gasWord requestRecord payloadLength
  payload : Payload.ReturnedImage input current origin.pointer record array payloadLength start size
  arena : CurrentStartup.ArenaState current
  little : current.be = false
  si : current.locals.lookup (ofString "si") = some (.val (.word origin.word))
  rootLocal : current.locals.lookup (ofString "root") = some (.val (.word root))
  enteringHeap : decoded.globals.lookup (ofString "heap_ptr") = some (.val (.word root))
  rootAfter : max (record.toNat + 136) (requestRecord.toNat + 80) ≤ root.toNat
  arrayBefore : array.toNat + 16 * VarList.decodedCount input start size ≤ root.toNat
  aligned : root.toNat % 8 = 0
  room : root.toNat + 32 ≤ 2952790016
  heap : NormalHeapEffects.AtLeast (root.toNat + 32) current
  memory : current.memory = decoded.memory
  clock : current.clock = decoded.clock - 1
  args : evalListHOLFinite current (h := fun query => Classical.propDecidable (current.memaddrs query)) arguments =
    some [.val (.word origin.word), .val (.word root)]

/-- A real continuing main decoder and the actual following root allocation
derive the hash-entry image and separation. No extra allocation room, returned
hash result or assumed future clock is added. -/
theorem allocated {input : Guest.InputBlob} {source decoded current : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : CurrentStartup.HostState input source) (heap : NormalHeapEffects.AtLeast 2701135464 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (decoder : CallPrefix.Execution source CurrentStartup.DecoderPrefix.actions decoded)
    (allocation : CallPrefix.Execution decoded actions current)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ origin : CurrentStartup.DecoderOrigin, ∃ record gasWord requestRecord root array : BitVec 64,
    ∃ payloadLength start size : Nat,
      Ready input decoded current origin record gasWord requestRecord root array payloadLength start size := by
  obtain ⟨origin, record, gasWord, requestRecord, array, payloadLength, start, size, run, si, snapshot, payload, before⟩ :=
    CurrentStartup.MainDecodedState.payload_image initial heap offsets decoder gas
  have decodedArena := CurrentStartup.DecoderPrefix.reached_state initial.arena decoder
  have reached : CallPrefix.Reaches decoded (.scoped (ofString "root") .one (CurrentStartup.Code.name .alloc) [.const 32#64]) current := by
    rw [actions_shape] at allocation
    cases allocation with
    | step first rest => cases rest; exact first
  obtain ⟨root, heapCell, rootAfter, aligned, room, stateEq, currentHeap⟩ :=
    CurrentStartup.allocation_frontier_after (ofString "root") 32#64
      (max (record.toNat + 136) (requestRecord.toNat + 80)) decodedArena.code snapshot.heap reached
  have memory : current.memory = decoded.memory := by rw [stateEq]; rfl
  have siCurrent : current.locals.lookup (ofString "si") = some (.val (.word origin.word)) := by
    rw [stateEq]
    simpa [setVarHOLFinite, WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
      show ofString "root" ≠ ofString "si" from by decide] using si
  have rootCurrent : current.locals.lookup (ofString "root") = some (.val (.word root)) := by
    rw [stateEq]
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have arrayBefore : array.toNat + 16 * VarList.decodedCount input start size ≤ root.toNat := by omega
  have extent : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start size) current := by
    obtain ⟨cursor, cell, low, high, cursorAligned⟩ := currentHeap
    exact ⟨cursor, cell, by omega, high, cursorAligned⟩
  have currentPayload := payload.of_interval root.toNat arrayBefore (by intro query lower upper; rw [memory]) extent
  have currentArena : CurrentStartup.ArenaState current := by
    rw [stateEq]
    refine ⟨?_, ?_, decodedArena.domain, decodedArena.code⟩
    · simpa [setVarHOLFinite, WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
        CurrentStartup.key, show ofString "heap_ptr" ≠ ofString "scratch_ptr" from by decide,
        show ofString "scratch_ptr" ≠ ofString "heap_ptr" from by decide] using decodedArena.scratch
    · simpa [setVarHOLFinite, WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
        CurrentStartup.key, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" from by decide,
        show ofString "frame_mem_ptr" ≠ ofString "heap_ptr" from by decide] using decodedArena.frame
  have little : current.be = false := by
    rw [stateEq]
    exact decoder.runtime.2.1.trans initial.little
  refine ⟨origin, record, gasWord, requestRecord, root, array, payloadLength, start, size,
    ⟨run, snapshot, currentPayload, currentArena, little, siCurrent, rootCurrent, heapCell, rootAfter, arrayBefore,
      aligned, room, currentHeap, memory, ?_, ?_⟩⟩
  · rw [stateEq]
    rfl
  · simp [arguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, siCurrent, rootCurrent]

end InitECandidate.Solver.Input.CurrentHash.RootEntry

#print axioms InitECandidate.Solver.Input.CurrentHash.RootEntry.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.RootEntry.actions_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.RootEntry.after_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.RootEntry.allocated
