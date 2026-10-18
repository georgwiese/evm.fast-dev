import InitECandidate.Solver.GasBudget.MessageCallBodyOpen

namespace InitECandidate.Solver.GasBudget.MessageCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

/-- Follow the actual root process_message_call site to the active child,
including its own call clock. The message's physical gas cell supplies the
cap on the child's initialized regular ledger; no gas-ledger oracle is used. -/
theorem call_open_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (start cursor : Nat) (scratch lower empty parent continuation recipient gas : BitVec 64) (intrinsicRegular : Nat) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower (BitVec.ofNat 64 start) empty words addresses keys addressCount keyCount)
    (environment : WarmKeys.Environment source)
    (cursorLower : 2701131776 ≤ cursor) (cursorBound : cursor ≤ 33806089496) (cursorAligned : cursor % 8 = 0)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (messageRegion : MemoryRegion.Valid ⟨start, 176⟩) (messageBefore : start + 176 ≤ cursor)
    (addressesBefore : addresses.toNat + 32 ≤ cursor) (keysBefore : keys.toNat + 32 ≤ cursor)
    (binding : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))))
    (recipientCell : source.memory (BitVec.ofNat 64 start + 24#64) = .word recipient) (nonzero : recipient ≠ 0#64)
    (gasCell : source.memory (BitVec.ofNat 64 start + 40#64) = .word gas) (cap : gas.toNat + intrinsicRegular ≤ 16777216)
    (callCode : source.code.lookup (ofString "process_message_call") = some (formals, body, .one))
    (known : source.code.lookup (ofString "process_message") = some ([(ofString "msg", .one)], ProcessMessage.body, .one))
    (openCode : source.code.lookup (ofString "frame_open") = some (FrameOpen.formals, FrameOpen.body, .one))
    (newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (normal : evaluateHOLFiniteState source Recipient.messageSite = (some (.returned value), post)) :
    ∃ (paid : Nat) (ready : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) (finish : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ paid ≤ words.length.toNat + Zero.price (JumpDest.bitmapBytes words.length.toNat) + 52 ∧
      ready.clock = source.clock - paid ∧ regularBudget ready.memory (FrameNew.framePointer scratch) = gas.toNat ∧
      regularBudget ready.memory (FrameNew.framePointer scratch) + intrinsicRegular ≤ 16777216 ∧
      ready.globals.lookup (ofString "ev") = some (.val (.word (FrameNew.framePointer scratch))) ∧
      ready.globals.lookup (ofString "cur_cont") = some (.val (.word (FrameOpen.recordPointer (FrameNew.finalScratch scratch words.length)))) ∧
      ready.code = source.code ∧ ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 96)))) ∧
      cursor + 96 ≤ 33806089496 ∧ ready.memaddrs = source.memaddrs ∧ ready.be = source.be ∧
      evaluateHOLFiniteState ready ProcessMessage.afterOpen = (some (.returned returned), finish) ∧
      ∀ query, Arenas.Outside lower scratch query → query.toNat < cursor → ready.memory query = source.memory query := by
  rw [actual_call] at normal
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "m"] = some [.val (.word (BitVec.ofNat 64 start))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, binding]
  obtain ⟨callee, called, messageLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "process_message_call") "msg" body (BitVec.ofNat 64 start) callCode
  have positive := Input.CallNormal.normal_clock source post (ofString "out") .one (ofString "process_message_call") _ afterCall value normal
  obtain ⟨target, returned, bodyRun⟩ := Input.CallNormal.callee_return source post (ofString "out") .one (ofString "process_message_call") _ [.val (.word (BitVec.ofNat 64 start))]
    body afterCall callee .one args called positive value normal
  let calleeSource := callEntryStateHOLFinite source callee
  have calleeEntry : FrameNew.Entry calleeSource scratch lower (BitVec.ofNat 64 start) empty words addresses keys addressCount keyCount := entry.relocals_clock callee (source.clock - 1)
  obtain ⟨paid, ready, bodyValue, finish, fits, price, clock, budget, active, activeContinuation, codes, nextHeap, nextBound, domain, endian, restRun, outside⟩ :=
    body_open_normal calleeSource target returned start cursor scratch lower empty parent continuation recipient words addresses keys addressCount keyCount calleeEntry
      (environment.of_fields rfl rfl rfl) cursorLower cursorBound cursorAligned heap messageRegion messageBefore addressesBefore keysBefore messageLocal recipientCell nonzero
      known openCode newCode evGlobal continuationGlobal room bodyRun
  have gasEq : words.gas = gas := by
    have stored := entry.messageCells 40 (by simp [FrameNew.messageOffsets])
    change source.memory (BitVec.ofNat 64 start + 40#64) = .word words.gas at stored
    exact HolWordLab.word.inj (stored.symm.trans gasCell)
  rw [gasEq] at budget
  refine ⟨paid + 1, ready, bodyValue, finish, ?_, by omega, ?_, budget, by omega, active, activeContinuation, codes, nextHeap, nextBound, domain, endian, restRun, outside⟩
  · change paid ≤ source.clock - 1 at fits
    omega
  · change ready.clock = source.clock - 1 - paid at clock
    omega

end InitECandidate.Solver.GasBudget.MessageCall

#print axioms InitECandidate.Solver.GasBudget.MessageCall.call_open_normal
