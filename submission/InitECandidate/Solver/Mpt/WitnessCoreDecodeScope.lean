import InitECandidate.Solver.Input.CoreDecodeResumeNormal
import InitECandidate.Solver.Input.ScopeLookup

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem decode_scoped_terminal_fields (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) :
    let current:=restore source "d" (delivered ready node)
    current.locals.lookup (ofString "result")=some (.val (.word node)) ∧
      current.locals.lookup (ofString "mode")=some (.val (.word 0#64)) ∧
      current.memory=ready.memory ∧ current.globals=ready.globals ∧ current.clock=ready.clock := by
  have fields:=delivered_fields ready node
  exact ⟨(Input.ScalarScope.restore_other source _ "d" "result" (by decide)).trans fields.1,
    (Input.ScalarScope.restore_other source _ "d" "mode" (by decide)).trans fields.2.1,rfl,rfl,rfl⟩

/-- After the original d scope closes, a genuine fresh record push has
exact top/mode/PREV fields and its real next resolver slot. Fresh branch
index0 is essential to the slot identity; no continuing arbitrary index is
silently reset in the physical loop invariant. -/
theorem decode_scoped_push_fields (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (record previous : BitVec 64)
    (payload : WitnessRecord.Payload) (fresh : payload.Fresh) :
    let current:=restore source "d" (pushed ready record previous payload)
    current.locals.lookup (ofString "top")=some (.val (.word record)) ∧
      current.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 payload.slotIndex))) ∧
      current.locals.lookup (ofString "mode")=some (.val (.word 2#64)) ∧
      current.memory record=.word previous ∧ current.globals=ready.globals ∧ current.clock=ready.clock := by
  have fields:=pushed_fields ready record previous payload
  have slot : (pushed ready record previous payload).locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 payload.slotIndex))):=by
    rw [←fresh_pushed_slot payload fresh]
    exact fields.2.1
  exact ⟨(Input.ScalarScope.restore_other source _ "d" "top" (by decide)).trans fields.1,
    (Input.ScalarScope.restore_other source _ "d" "slot" (by decide)).trans slot,
    (Input.ScalarScope.restore_other source _ "d" "mode" (by decide)).trans fields.2.2.1,fields.2.2.2.1,rfl,rfl⟩

theorem decode_scoped_terminal_other (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (name : String) (notD : ofString "d"≠ofString name) (notResult : ofString "result"≠ofString name) (notMode : ofString "mode"≠ofString name) :
    (restore source "d" (delivered ready node)).locals.lookup (ofString name)=ready.locals.lookup (ofString name) :=
  (Input.ScalarScope.restore_other source _ "d" name notD).trans
    ((bind_lookup_other _ "mode" name 0#64 notMode).trans (bind_lookup_other ready "result" name node notResult))

theorem decode_scoped_push_other (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (record previous : BitVec 64) (payload : WitnessRecord.Payload)
    (name : String) (notD : ofString "d"≠ofString name) (notTop : ofString "top"≠ofString name)
    (notSlot : ofString "slot"≠ofString name) (notMode : ofString "mode"≠ofString name) :
    (restore source "d" (pushed ready record previous payload)).locals.lookup (ofString name)=ready.locals.lookup (ofString name) :=
  (Input.ScalarScope.restore_other source _ "d" name notD).trans (pushed_other ready record previous payload name notTop notSlot notMode)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.decode_scoped_terminal_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.decode_scoped_push_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.decode_scoped_terminal_other
#print axioms InitECandidate.Solver.Mpt.WitnessCore.decode_scoped_push_other
