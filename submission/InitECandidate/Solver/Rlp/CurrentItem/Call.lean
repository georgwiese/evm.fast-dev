import InitECandidate.Solver.Input.ScopedCallTrace
import InitECandidate.Solver.Rlp.CurrentItem.Memory
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.CurrentItem
open Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

/-- A continuation is priced only after the actual item decoder has returned
a positive item contained in the supplied input and retaining runtime and memory outside scratch. -/
theorem scoped_valid_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ answer : ValueHOL 64,
      Item.Valid pointer length.toNat answer → Frame source current →
      current.clock-(evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {current with locals:=source.locals}) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_item") expressions continuation)).2.clock≤60*length.toNat+tailPrice+11 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Item.body Item.resultShape pointer length (Item.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code
  have actual:=ClockCost.scoped_reached_current source name Item.resultShape (ofString "rlp_item") expressions (Header.values pointer length) Item.body continuation callee Item.resultShape (60*length.toNat+10) tailPrice args called paid ?_
  · omega
  · intro target answer normal checked
    obtain ⟨complete,frame,price⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer normal
    exact tail target answer complete (frame.of_erase rfl rfl)

/-- Real normal callers retain the exact successful decode value and caller
state at the real child-return clock, plus the actual later continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_item") expressions continuation)=(some (.returned value),post)) :
    ∃ answer : ValueHOL 64,∃ calleePost inner,Item.Valid pointer length.toNat answer ∧ calleePost.clock≤source.clock ∧ source.clock-calleePost.clock≤60*length.toNat+11 ∧
      Frame source calleePost ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {calleePost with locals:=source.locals}) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Item.body Item.resultShape pointer length (Item.original_code source.code arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_normal source post name Item.resultShape (ofString "rlp_item") expressions (Header.values pointer length) Item.body continuation callee Item.resultShape args called value normal
  obtain ⟨complete,frame,price⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer bodyRun
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) Item.body
  rw [bodyRun] at forward
  change source.clock-1-target.clock≤60*length.toNat+10 at price
  change target.clock≤source.clock-1 at forward
  exact ⟨answer,target,inner,complete,(by omega),(by omega),frame.of_erase rfl rfl,remaining,endpoint⟩

/-- All actual nested caller outcomes retain their real callee state,
protect earlier inputs and live records, and expose only the genuine suffix. -/
theorem scoped_trace_above (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit : BitVec 64)
    (arena : LiveArena source) (physical : Validation.Arena source cursor limit)
    (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Header.values pointer length))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_item") expressions continuation)=(outcome,post)) :
    source.clock-post.clock≤60*length.toNat+11 ∨ ∃ target answer inner,
      Item.Valid pointer length.toNat answer ∧ Frame source target ∧ Validation.Above source target cursor.toNat ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤60*length.toNat+11 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name answer) continuation=(outcome,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") Item.body Item.resultShape
    pointer length (Item.original_code source.code arena.code)
  let entry:=callEntryStateHOLFinite source callee
  have entryPhysical:=physical.of_fields source entry cursor limit rfl rfl
  have price:=body_cost entry pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code
  rcases CallNormal.scoped_trace source post name Item.resultShape (ofString "rlp_item") expressions _ Item.body continuation callee Item.resultShape
    (60*length.toNat+10) args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,answer,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨valid,frame,above,spent⟩:=body_normal_above entry target pointer length cursor limit pointerLocal lengthLocal
      (arena.of_frame rfl) entryPhysical fits arena.code answer bodyRun
    exact Or.inr ⟨target,answer,inner,valid,frame.of_erase rfl rfl,above,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.scoped_valid_cost
#print axioms InitECandidate.Solver.Rlp.CurrentItem.scoped_normal

#print axioms InitECandidate.Solver.Rlp.CurrentItem.scoped_trace_above
