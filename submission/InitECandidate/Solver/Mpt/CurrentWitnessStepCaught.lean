import InitECandidate.Solver.Mpt.WitnessStepProgram
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Rlp.CurrentDecodeMemory
import InitECandidate.Solver.Input.CaughtAssignedStops
import InitECandidate.Solver.Input.ClockCostCaughtAssigned
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Mpt.CurrentWitnessStep
open WitnessStep Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem caught_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length) := by
  simp [arguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]

theorem rlp_cost (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source (rlpBody kind)).2.clock≤60*length.toNat+12 := by
  cases kind with
  | resolve=>exact Nat.le_trans (Rlp.CurrentItem.body_cost source pointer length pointerCell lengthCell arena fits arena.code) (by omega)
  | decode=>exact Rlp.CurrentDecode.body_cost source pointer length pointerCell lengthCell arena fits arena.code

theorem rlp_normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (rlpBody kind)=(some (.returned value),post)) :
    parsed kind pointer length value ∧ Rlp.CurrentItem.Frame source post ∧ source.clock-post.clock≤60*length.toNat+12 := by
  have cost:=rlp_cost kind source pointer length pointerCell lengthCell arena fits
  rw [normal] at cost
  cases kind with
  | resolve=>
    obtain ⟨valid,frame,itemCost⟩:=Rlp.CurrentItem.body_normal source post pointer length pointerCell lengthCell arena fits arena.code value normal
    exact ⟨valid,frame,cost⟩
  | decode=>exact Rlp.CurrentDecode.body_normal source post pointer length pointerCell lengthCell arena fits arena.code value normal

/-- Current actual caught parsing covers errors and short clocks, using the
actual mapped scratch frame and retained runtime metadata. -/
theorem caught_cost (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source (caught kind)).2.clock≤60*length.toNat+14 := by
  have args:=caught_arguments source pointer length pointerCell lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString (rlpName kind)) (rlpBody kind) Rlp.Item.resultShape pointer length
    (rlp_code kind source.code arena.code)
  exact ClockCost.caught_destination_current source (some (.local,ofString "it")) (ofString (rlpName kind)) arguments _ (rlpBody kind) callee Rlp.Item.resultShape
    (ofString "RlpErr") (ofString "e") handler (60*length.toNat+12) 1 args called
    (rlp_cost kind _ pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits) (Fail.call_price source.code arena.code [.const 3#64])

/-- A real normally continuing caught call must have parsed its actual
input. The MPT handler cannot manufacture successful fallthrough. -/
theorem caught_none (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (normal : evaluateHOLFiniteState source (caught kind)=(none,post)) :
    ∃ target value,parsed kind pointer length value ∧ Rlp.CurrentItem.Frame source post ∧
      (∀ cursor limit,Rlp.Validation.Arena source cursor limit→Rlp.Validation.Above source post cursor.toNat) ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤60*length.toNat+13 ∧
      post=CallNormal.continuationEntry source target "it" value := by
  have args:=caught_arguments source pointer length pointerCell lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString (rlpName kind)) (rlpBody kind) Rlp.Item.resultShape pointer length
    (rlp_code kind source.code arena.code)
  have stops : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→(evaluateHOLFiniteState current handler).1≠none := by
    intro current codeEq passed
    have installed : OriginalCode.Installed current.code := by rw [codeEq]; exact arena.code
    exact Fail.call_not_normal current _ installed [.const 3#64] (Prod.ext passed rfl)
  obtain ⟨funded,target,value,bodyRun,checked,endpoint⟩:=CallNormal.assigned_caught_stops source post (ofString "it") (ofString (rlpName kind)) arguments _ (rlpBody kind) callee Rlp.Item.resultShape
    (ofString "RlpErr") (ofString "e") handler args called stops normal
  obtain ⟨valid,frame,cost⟩:=rlp_normal kind (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits value bodyRun
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) (rlpBody kind)
  rw [bodyRun] at forward
  change target.clock≤source.clock-1 at forward
  change source.clock-1-target.clock≤60*length.toNat+12 at cost
  have above : ∀ cursor limit,Rlp.Validation.Arena source cursor limit→Rlp.Validation.Above source post cursor.toNat:=by
    intro cursor limit physical query beyond
    have entered:=physical.of_fields source (callEntryStateHOLFinite source callee) cursor limit rfl rfl
    rw [endpoint]
    cases kind with
    | resolve=>
      have protectedWords:=(Rlp.CurrentItem.body_normal_above (callEntryStateHOLFinite source callee) target pointer length cursor limit
        pointerLocal lengthLocal (arena.of_frame rfl) entered fits arena.code value bodyRun).2.2.1
      exact protectedWords query beyond
    | decode=>
      have protectedWords:=(Rlp.CurrentDecode.body_normal_above (callEntryStateHOLFinite source callee) target pointer length cursor limit
        pointerLocal lengthLocal (arena.of_frame rfl) entered fits arena.code value bodyRun).2.2.1
      exact protectedWords query beyond
  exact ⟨target,value,valid,frame.of_erase rfl (by rw [endpoint]; rfl),above,by omega,by omega,endpoint⟩

end InitECandidate.Solver.Mpt.CurrentWitnessStep

#print axioms InitECandidate.Solver.Mpt.CurrentWitnessStep.rlp_cost
#print axioms InitECandidate.Solver.Mpt.CurrentWitnessStep.rlp_normal
#print axioms InitECandidate.Solver.Mpt.CurrentWitnessStep.caught_cost
#print axioms InitECandidate.Solver.Mpt.CurrentWitnessStep.caught_none
