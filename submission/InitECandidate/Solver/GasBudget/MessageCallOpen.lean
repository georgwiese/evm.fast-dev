import InitECandidate.Solver.GasBudget.MessageCallDispatch

namespace InitECandidate.Solver.GasBudget.MessageCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Follow the real assigned process_message call to its actual active
child. The initial physical regular ledger is MSG_GAS, and all prefix call
clocks are derived from the real normal execution. -/
theorem invoke_open_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower message empty parent continuation : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (known : source.code.lookup (ofString "process_message") = some ([(ofString "msg", .one)], ProcessMessage.body, .one))
    (openCode : source.code.lookup (ofString "frame_open") = some (FrameOpen.formals, FrameOpen.body, .one))
    (newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (binding : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (normal : evaluateHOLFiniteState source invokeMessage = (none, target)) :
    ∃ (paid : Nat) (ready : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) (finish : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ paid ≤ words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 46 ∧
      ready.clock = source.clock - paid ∧ regularBudget ready.memory (FrameNew.framePointer scratch) = words.gas.toNat ∧
      ready.globals.lookup (ofString "ev") = some (.val (.word (FrameNew.framePointer scratch))) ∧
      ready.globals.lookup (ofString "cur_cont") = some (.val (.word (FrameOpen.recordPointer (FrameNew.finalScratch scratch words.length)))) ∧
      ready.code = source.code ∧
      ready.memaddrs = source.memaddrs ∧ ready.be = source.be ∧
      ready.globals.lookup (ofString "heap_ptr") = source.globals.lookup (ofString "heap_ptr") ∧
      evaluateHOLFiniteState ready ProcessMessage.afterOpen = (some (.returned returned), finish) ∧
      ∀ query, Arenas.Outside lower scratch query → ready.memory query = source.memory query := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "msg"] = some [.val (.word message)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, binding]
  obtain ⟨callee, called, messageLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "process_message") "msg" ProcessMessage.body message known
  obtain ⟨positive, target, returned, bodyRun⟩ := Input.CallNormal.assigned_callee_return source target (some (.local, ofString "frame")) (ofString "process_message") _
    [.val (.word message)] ProcessMessage.body callee .one args called normal
  let calleeSource := callEntryStateHOLFinite source callee
  have calleeEntry : FrameNew.Entry calleeSource scratch lower message empty words addresses keys addressCount keyCount := entry.relocals_clock callee (source.clock - 1)
  obtain ⟨memory, spent, finish, bound, fits, budget, outside, restRun, restored⟩ := ProcessMessage.open_normal calleeSource target returned
    scratch lower message empty parent continuation words addresses keys addressCount keyCount calleeEntry openCode newCode messageLocal evGlobal continuationGlobal room bodyRun
  let ready := FrameOpen.openedState (ProcessMessage.enteredState calleeSource parent continuation) "child" scratch lower words.length memory spent
  let paid := WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 46 + spent
  have funded : paid ≤ source.clock := by
    change WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent ≤ source.clock - 1 at fits
    dsimp [paid]
    omega
  have clock : ready.clock = source.clock - paid := by
    change source.clock - 1 - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent) = source.clock - paid
    dsimp [paid]
    omega
  refine ⟨paid, ready, returned, finish, funded, by dsimp [paid]; omega, clock, budget, ?_, ?_, rfl, rfl, rfl, ?_, restRun, outside⟩
  · simp [ready, FrameOpen.openedState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "cur_cont" ≠ ofString "ev" from by decide]
  · simp [ready, FrameOpen.openedState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simp [ready, FrameOpen.openedState, ProcessMessage.enteredState, calleeSource, callEntryStateHOLFinite,
      WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "cur_cont" ≠ ofString "heap_ptr" from by decide,
      show ofString "ev" ≠ ofString "heap_ptr" from by decide,
      show ofString "scratch_ptr" ≠ ofString "heap_ptr" from by decide,
      show ofString "frame_mem_ptr" ≠ ofString "heap_ptr" from by decide]

end InitECandidate.Solver.GasBudget.MessageCall

#print axioms InitECandidate.Solver.GasBudget.MessageCall.invoke_open_normal
