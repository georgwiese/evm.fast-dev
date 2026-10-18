import InitECandidate.Solver.GasBudget.ProcessMessageProgram

namespace InitECandidate.Solver.GasBudget.ProcessMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def enteredState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent continuation : BitVec 64) :=
  bind (bind source "parent" parent) "parent_cont" continuation

/-- Reach the real frame_open call after the unchanged depth guard and both
parent declarations. Only actual normal execution justifies passing the guard. -/
theorem open_reached (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) (parent continuation : BitVec 64)
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ finish, evaluateHOLFiniteState (enteredState source parent continuation) openSite = (some (.returned value), finish) ∧
      post = restore source "parent" (restore (bind source "parent" parent) "parent_cont" finish) := by
  rw [body_shape] at normal
  have past := guard_read_only.normal_continue source post _ value normal
  rw [WitnessRadix.StateSteps.next_sequence source source .skip _ (by rw [evaluateHOLFiniteState_skip]) (Nat.le_refl _)] at past
  unfold parentScopes at past
  obtain ⟨declared, inner, read, _, innerRun, restored⟩ := Input.CallNormal.declaration_normal_entry source post "parent" .one (.var .global (ofString "ev")) _ value past
  have parentRead : eval source (.var .global (ofString "ev")) = some (.val (.word parent)) := by
    simpa only [eval, evalHOLExact, toExact] using evGlobal
  have parentEq : declared = .val (.word parent) := Option.some.inj (read.symm.trans parentRead)
  subst declared
  obtain ⟨declared, finish, read, _, finishRun, innerRestored⟩ := Input.CallNormal.declaration_normal_entry (bind source "parent" parent) inner "parent_cont" .one
    (.var .global (ofString "cur_cont")) openSite value innerRun
  have continuationRead : eval (bind source "parent" parent) (.var .global (ofString "cur_cont")) = some (.val (.word continuation)) := by
    simpa only [eval, evalHOLExact, toExact, WitnessRadix.QueryBranch.bind, setVarHOLFinite] using continuationGlobal
  have continuationEq : declared = .val (.word continuation) := Option.some.inj (read.symm.trans continuationRead)
  subst declared
  rw [innerRestored] at restored
  exact ⟨finish, finishRun, restored⟩

/-- Actual process_message opens its child with regular ledger equal to
the physical message gas. No helper result or source-clock funding is assumed. -/
theorem open_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (scratch lower message empty parent continuation : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (known : source.code.lookup (ofString "frame_open") = some (FrameOpen.formals, FrameOpen.body, .one))
    (newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ (memory : Memory) (spent : Nat) (finish : PanSemStateFiniteExact 64 Guest.HostMemory),
      spent ≤ words.length.toNat ∧ WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 45 + spent ≤ source.clock ∧
      regularBudget memory (FrameNew.framePointer scratch) = words.gas.toNat ∧
      (∀ query, Arenas.Outside lower scratch query → memory query = source.memory query) ∧
      evaluateHOLFiniteState (FrameOpen.openedState (enteredState source parent continuation) "child" scratch lower words.length memory spent) afterOpen = (some (.returned value), finish) ∧
      post = restore source "parent" (restore (bind source "parent" parent) "parent_cont"
        (restore (enteredState source parent continuation) "child" finish)) := by
  obtain ⟨openPost, openRun, restored⟩ := open_reached source post value parent continuation evGlobal continuationGlobal normal
  let entered := enteredState source parent continuation
  have enteredMessage : entered.locals.lookup (ofString "msg") = some (.val (.word message)) :=
    (bind_lookup_other _ "parent_cont" "msg" _ (by decide)).trans ((bind_lookup_other _ "parent" "msg" _ (by decide)).trans messageLocal)
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) [localVar "msg", .const 0#64] = some (FrameOpen.values message 0#64) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, enteredMessage, FrameOpen.values]
  have enteredEntry : FrameNew.Entry entered scratch lower message empty words addresses keys addressCount keyCount := entry.relocals_clock entered.locals source.clock
  obtain ⟨memory, spent, finish, bound, fits, budget, outside, restRun, openRestored⟩ := FrameOpen.call_normal entered openPost "child" _ afterOpen value
    scratch lower message empty parent continuation 0#64 words addresses keys addressCount keyCount enteredEntry args known newCode evGlobal continuationGlobal room openRun
  rw [openRestored] at restored
  exact ⟨memory, spent, finish, bound, fits, budget, outside, restRun, restored⟩

end InitECandidate.Solver.GasBudget.ProcessMessage

#print axioms InitECandidate.Solver.GasBudget.ProcessMessage.open_reached
#print axioms InitECandidate.Solver.GasBudget.ProcessMessage.open_normal
