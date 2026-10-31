import InitECandidate.Solver.Rlp.CurrentDecodeMemory
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

/-- A continuation is priced only after the actual full decoder has returned
an item occupying the complete input and retaining runtime and memory outside scratch. -/
theorem scoped_valid_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ answer : ValueHOL 64,
      Complete pointer length answer → CurrentItem.Frame source current →
      current.clock-(evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {current with locals:=source.locals}) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_decode_fully") expressions continuation)).2.clock≤60*length.toNat+tailPrice+13 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") Decode.body Item.resultShape pointer length (Decode.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code
  have actual:=ClockCost.scoped_reached_current source name Item.resultShape (ofString "rlp_decode_fully") expressions (Header.values pointer length) Decode.body continuation callee Item.resultShape (60*length.toNat+12) tailPrice args called paid ?_
  · omega
  · intro target answer normal checked
    obtain ⟨complete,frame,price⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer normal
    exact tail target answer complete (frame.of_erase rfl rfl)

/-- Real normal callers retain the exact successful decode value and caller
state at the real child-return clock, plus the actual later continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_decode_fully") expressions continuation)=(some (.returned value),post)) :
    ∃ answer : ValueHOL 64,∃ calleePost inner,Complete pointer length answer ∧ calleePost.clock≤source.clock ∧ source.clock-calleePost.clock≤60*length.toNat+13 ∧
      CurrentItem.Frame source calleePost ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {calleePost with locals:=source.locals}) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") Decode.body Item.resultShape pointer length (Decode.original_code source.code arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_normal source post name Item.resultShape (ofString "rlp_decode_fully") expressions (Header.values pointer length) Decode.body continuation callee Item.resultShape args called value normal
  obtain ⟨complete,frame,price⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer bodyRun
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) Decode.body
  rw [bodyRun] at forward
  change source.clock-1-target.clock≤60*length.toNat+12 at price
  change target.clock≤source.clock-1 at forward
  exact ⟨answer,target,inner,complete,(by omega),(by omega),frame.of_erase rfl rfl,remaining,endpoint⟩

end InitECandidate.Solver.Rlp.CurrentDecode

#print axioms InitECandidate.Solver.Rlp.CurrentDecode.scoped_valid_cost
#print axioms InitECandidate.Solver.Rlp.CurrentDecode.scoped_normal
