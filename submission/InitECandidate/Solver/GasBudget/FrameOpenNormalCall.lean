import InitECandidate.Solver.GasBudget.FrameOpenNormal

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def openedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (scratch lower length : BitVec 64) (memory : Memory) (spent : Nat) :=
  bind {source with
    globals := (((source.globals.update (ofString "frame_mem_ptr", .val (.word (FrameNew.memoryPointer lower)))).update
      (ofString "scratch_ptr", .val (.word (recordPointer (FrameNew.finalScratch scratch length))))).update
      (ofString "ev", .val (.word (FrameNew.framePointer scratch)))).update
      (ofString "cur_cont", .val (.word (recordPointer (FrameNew.finalScratch scratch length))))
    memory := memory
    clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes length.toNat) + 45 + spent)}
    name (FrameNew.framePointer scratch)

/-- Real normal frame_open call, deriving its available clock, actual child
pointer, canonical activation state and physical initial gas ledger before
entering the original caller continuation. Arena reachability remains explicit. -/
theorem call_normal_full (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (rest : ProgHOL 64) (value : ValueHOL 64)
    (scratch lower message empty parent continuation kind : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values message kind))
    (known : source.code.lookup (ofString "frame_open") = some (formals, body, .one))
    (newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "frame_open") arguments rest) = (some (.returned value), post)) :
    ∃ (memory : Memory) (spent : Nat) (inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      spent ≤ words.length.toNat ∧ WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent ≤ source.clock ∧
      regularBudget memory (FrameNew.framePointer scratch) = words.gas.toNat ∧
      GasSeed memory (FrameNew.framePointer scratch) words.gas ∧
      (∀ query, Arenas.Outside lower scratch query → memory query = source.memory query) ∧
      evaluateHOLFiniteState (openedState source name scratch lower words.length memory spent) rest = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨callee, called, messageLocal, kindLocal⟩ := environment source.code.lookup message kind known
  have positive := Input.CallNormal.normal_clock source post (ofString name) .one (ofString "frame_open") arguments rest value normal
  obtain ⟨target, returned, bodyRun⟩ := Input.CallNormal.callee_return source post (ofString name) .one (ofString "frame_open") arguments (values message kind)
    body rest callee .one args called positive value normal
  let calleeSource := callEntryStateHOLFinite source callee
  have calleeEntry : FrameNew.Entry calleeSource scratch lower message empty words addresses keys addressCount keyCount := entry.relocals_clock callee (source.clock - 1)
  obtain ⟨spent, bound, fits, resultEq, frame, budget, seed, outside⟩ := body_normal_full calleeSource target scratch lower message empty parent continuation kind words
    addresses keys addressCount keyCount calleeEntry newCode messageLocal kindLocal evGlobal continuationGlobal room returned bodyRun
  rw [resultEq] at bodyRun
  have actual := Input.CallNormal.return_execute source target name .one (ofString "frame_open") arguments (values message kind) body rest callee .one
    (.val (.word (FrameNew.framePointer scratch))) args called positive bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have clocks : source.clock - 1 - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 + spent) =
      source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent) := by omega
  have resumed : Input.CallNormal.continuationEntry source target name (.val (.word (FrameNew.framePointer scratch))) =
      openedState source name scratch lower words.length target.memory spent := by
    unfold Input.CallNormal.continuationEntry openedState
    apply congrArg (setVarHOLFinite (ofString name) (.val (.word (FrameNew.framePointer scratch))))
    simpa only [emptyLocalsHOLFinite, calleeSource, callEntryStateHOLFinite, clocks] using callerFrame
  rw [resumed] at actual
  have actualResult := congrArg Prod.fst (actual.symm.trans normal)
  have actualPost := congrArg Prod.snd (actual.symm.trans normal)
  let inner := (evaluateHOLFiniteState (openedState source name scratch lower words.length target.memory spent) rest).2
  refine ⟨target.memory, spent, inner, bound, ?_, budget, seed, outside, Prod.ext actualResult rfl, actualPost.symm⟩
  change WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 + spent ≤ source.clock - 1 at fits
  omega

theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (rest : ProgHOL 64) (value : ValueHOL 64)
    (scratch lower message empty parent continuation kind : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values message kind))
    (known : source.code.lookup (ofString "frame_open") = some (formals, body, .one))
    (newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "frame_open") arguments rest) = (some (.returned value), post)) :
    ∃ (memory : Memory) (spent : Nat) (inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      spent ≤ words.length.toNat ∧ WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent ≤ source.clock ∧
      regularBudget memory (FrameNew.framePointer scratch) = words.gas.toNat ∧
      (∀ query, Arenas.Outside lower scratch query → memory query = source.memory query) ∧
      evaluateHOLFiniteState (openedState source name scratch lower words.length memory spent) rest = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨memory, spent, inner, bound, fits, budget, seed, outside, run, scopes⟩ := call_normal_full source post name arguments rest value
    scratch lower message empty parent continuation kind words addresses keys addressCount keyCount entry args known newCode evGlobal continuationGlobal room normal
  exact ⟨memory, spent, inner, bound, fits, budget, outside, run, scopes⟩

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.call_normal

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.call_normal_full
