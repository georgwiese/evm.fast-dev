import InitECandidate.Solver.GasBudget.MessageCallOpen
import InitECandidate.Solver.GasBudget.FrameEntryAfterClear

namespace InitECandidate.Solver.GasBudget.MessageCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

/-- The actual original non-creation message-call body through child
activation: output allocation/clear, real dispatch, depth guard, parent
scopes and full frame_open. Every call-clock payment follows from execution;
all input reads survive the intervening output allocation. -/
theorem body_open_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (start cursor : Nat) (scratch lower empty parent continuation recipient : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower (BitVec.ofNat 64 start) empty words addresses keys addressCount keyCount)
    (environment : WarmKeys.Environment source)
    (cursorLower : 2701131776 ≤ cursor) (cursorBound : cursor ≤ 33806089496) (cursorAligned : cursor % 8 = 0)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (messageRegion : MemoryRegion.Valid ⟨start, 176⟩) (messageBefore : start + 176 ≤ cursor)
    (addressesBefore : addresses.toNat + 32 ≤ cursor) (keysBefore : keys.toNat + 32 ≤ cursor)
    (binding : source.locals.lookup (ofString "msg") = some (.val (.word (BitVec.ofNat 64 start))))
    (recipientCell : source.memory (BitVec.ofNat 64 start + 24#64) = .word recipient) (nonzero : recipient ≠ 0#64)
    (known : source.code.lookup (ofString "process_message") = some ([(ofString "msg", .one)], ProcessMessage.body, .one))
    (openCode : source.code.lookup (ofString "frame_open") = some (FrameOpen.formals, FrameOpen.body, .one))
    (newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ (paid : Nat) (ready : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) (finish : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ paid ≤ words.length.toNat + Zero.price (JumpDest.bitmapBytes words.length.toNat) + 51 ∧
      ready.clock = source.clock - paid ∧ regularBudget ready.memory (FrameNew.framePointer scratch) = words.gas.toNat ∧
      ready.globals.lookup (ofString "ev") = some (.val (.word (FrameNew.framePointer scratch))) ∧
      ready.globals.lookup (ofString "cur_cont") = some (.val (.word (FrameOpen.recordPointer (FrameNew.finalScratch scratch words.length)))) ∧
      ready.code = source.code ∧ ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 96)))) ∧
      cursor + 96 ≤ 33806089496 ∧ ready.memaddrs = source.memaddrs ∧ ready.be = source.be ∧
      evaluateHOLFiniteState ready ProcessMessage.afterOpen = (some (.returned returned), finish) ∧
      ∀ query, Arenas.Outside lower scratch query → query.toNat < cursor → ready.memory query = source.memory query := by
  obtain ⟨outputRegion, prefixFits, inner, restRun, restored⟩ := prefix_normal source post cursor environment cursorLower cursorBound cursorAligned heap value normal
  let cleared := clearedState source cursor
  have messageWordBefore (offset : Nat) (inside : offset < 176) :
      (BitVec.ofNat 64 start + BitVec.ofNat 64 offset).toNat < cursor := by
    rw [MessageField.field_number start offset messageRegion (by omega)]
    omega
  have headerBefore (address : BitVec 64) (before : address.toNat + 32 ≤ cursor) : (address + 24#64).toNat < cursor := by
    have number := byteAddress_toNat address 24 (by omega)
    change (address + 24#64).toNat = address.toNat + 24 at number
    omega
  have inputBefore : ∀ cell ∈ FrameNew.suffixCells (BitVec.ofNat 64 start) ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩, cell.1.toNat < cursor := by
    intro cell member
    simp only [FrameNew.suffixCells, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact messageWordBefore 112 (by decide)
    · exact messageWordBefore 120 (by decide)
    · exact messageWordBefore 152 (by decide)
    · exact messageWordBefore 160 (by decide)
    · exact headerBefore addresses addressesBefore
    · exact headerBefore keys keysBefore
  have clearEntry := entry.after_result_clear source scratch lower (BitVec.ofNat 64 start) empty words addresses keys addressCount keyCount cursor outputRegion
    (by intro offset member; simp only [FrameNew.messageOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> exact messageWordBefore _ (by decide)) inputBefore
  have clearMessage : cleared.locals.lookup (ofString "msg") = some (.val (.word (BitVec.ofNat 64 start))) :=
    (bind_lookup_other _ "out" "msg" _ (by decide)).trans binding
  have recipientMapped : cleared.memaddrs (BitVec.ofNat 64 start + 24#64) := by
    change source.memaddrs _
    rw [environment.domain]
    exact MemoryRegion.word_mapped ⟨start, 176⟩ messageRegion 24 (by change 24 + 8 ≤ 176; decide) (by decide)
  have clearRecipient : cleared.memory (BitVec.ofNat 64 start + 24#64) = .word recipient :=
    (cleared_earlier source cursor outputRegion _ (messageWordBefore 24 (by decide))).trans recipientCell
  obtain ⟨called, dispatchFinish, invokeRun, dispatchRun, dispatchRestored⟩ := dispatch_normal cleared inner (BitVec.ofNat 64 start) recipient clearMessage recipientMapped clearRecipient nonzero value restRun
  let declared := bind cleared "frame" 0#64
  have declaredMessage : declared.locals.lookup (ofString "msg") = some (.val (.word (BitVec.ofNat 64 start))) := (bind_lookup_other _ "frame" "msg" _ (by decide)).trans clearMessage
  have declaredEntry : FrameNew.Entry declared scratch lower (BitVec.ofNat 64 start) empty words addresses keys addressCount keyCount := clearEntry.relocals_clock declared.locals cleared.clock
  have globals (name : String) (different : ofString "heap_ptr" ≠ ofString name) : declared.globals.lookup (ofString name) = source.globals.lookup (ofString name) := by
    simp [declared, cleared, clearedState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, Ne.symm different]
  obtain ⟨paid, ready, returned, finish, fits, price, clock, budget, active, activeContinuation, codes, domain, endian, heapSame, afterOpenRun, outside⟩ :=
    invoke_open_normal declared called scratch lower (BitVec.ofNat 64 start) empty parent continuation words addresses keys addressCount keyCount declaredEntry known openCode newCode declaredMessage
      ((globals "ev" (by decide)).trans evGlobal) ((globals "cur_cont" (by decide)).trans continuationGlobal) room invokeRun
  have nextHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 96)))) := by
    rw [heapSame]
    simp [declared, cleared, clearedState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  refine ⟨5 + paid, ready, returned, finish, ?_, by omega, ?_, budget, active, activeContinuation, codes, nextHeap, outputRegion.upper, domain, endian, afterOpenRun, ?_⟩
  · change paid ≤ source.clock - 5 at fits
    omega
  · change ready.clock = source.clock - 5 - paid at clock
    omega
  · intro query apart before
    exact (outside query apart).trans (cleared_earlier source cursor outputRegion query before)

end InitECandidate.Solver.GasBudget.MessageCall

#print axioms InitECandidate.Solver.GasBudget.MessageCall.body_open_normal
