import InitECandidate.Solver.Rlp.CurrentItem.Memory
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.CurrentItem
open Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

/-- A continuation is priced only after the actual item decoder has returned
a positive item contained in the supplied input and preserving all nonlocal fields. -/
theorem scoped_valid_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (tail : ∀ answer : ValueHOL 64,∀ clock : Nat,Item.Valid pointer length.toNat answer →
      clock-(evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {source with clock:=clock}) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_item") expressions continuation)).2.clock≤46*length.toNat+tailPrice+11 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Item.body Item.resultShape pointer length (Item.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code
  have actual:=ClockCost.scoped_reached_current source name Item.resultShape (ofString "rlp_item") expressions (Header.values pointer length) Item.body continuation callee Item.resultShape (46*length.toNat+10) tailPrice args called paid ?_
  · omega
  · intro target answer normal checked
    obtain ⟨complete,frame,price⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer normal
    have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) frame
    change {target with locals:=source.locals}={source with clock:=target.clock} at callerFrame
    unfold CallNormal.continuationEntry
    rw [callerFrame]
    exact tail answer target.clock complete

/-- Real normal callers retain the exact successful decode value and caller
state at the real child-return clock, plus the actual later continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_item") expressions continuation)=(some (.returned value),post)) :
    ∃ answer : ValueHOL 64,∃ clock : Nat,∃ inner,Item.Valid pointer length.toNat answer ∧ clock≤source.clock ∧ source.clock-clock≤46*length.toNat+11 ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {source with clock:=clock}) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Item.body Item.resultShape pointer length (Item.original_code source.code arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_normal source post name Item.resultShape (ofString "rlp_item") expressions (Header.values pointer length) Item.body continuation callee Item.resultShape args called value normal
  obtain ⟨complete,frame,price⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer bodyRun
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) Item.body
  rw [bodyRun] at forward
  change source.clock-1-target.clock≤46*length.toNat+10 at price
  change target.clock≤source.clock-1 at forward
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) frame
  change {target with locals:=source.locals}={source with clock:=target.clock} at callerFrame
  unfold CallNormal.continuationEntry at remaining
  rw [callerFrame] at remaining
  exact ⟨answer,target.clock,inner,complete,(by omega),(by omega),remaining,endpoint⟩

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.scoped_valid_cost
#print axioms InitECandidate.Solver.Rlp.CurrentItem.scoped_normal
