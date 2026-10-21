import InitECandidate.Solver.Rlp.SlicesTrace
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The genuine successful scoped return supplies the full current parser contract. -/
theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_list_to_slices") expressions continuation)=(some (.returned value),post)) :
    ∃ target items count inner,Returned source target pointer length heap cursor limit count items ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (result heap count)) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  have fits : pointer.toNat+length.toNat<2^64 := by have := heap.isLt; omega
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code installed)
  have entryArena := Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price := body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩ :=
    Input.CallNormal.scoped_normal source post name resultShape (ofString "rlp_list_to_slices") expressions _ body continuation callee resultShape args called value run
  have clock:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock price
  change target.clock≤source.clock-1 at clock
  change source.clock-1-target.clock≤71*length.toNat+34 at price
  have forward : target.clock≤source.clock := by omega
  have cost : source.clock-target.clock≤71*length.toNat+35 := by omega
  obtain ⟨items,count,itemModel,countEq,countBound,valueEq,records,room,nextArena,nextHeap,frame,_⟩ :=
    body_normal (callEntryStateHOLFinite source callee) target pointer length heap cursor limit cutoff pointerLocal lengthLocal entryArena heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove installed answer bodyRun
  rw [valueEq] at continued
  have fields := Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned answer)) bodyRun
  have globalsFrame (key : MlS) (notHeap : key≠ofString "heap_ptr") : target.globals.lookup key=source.globals.lookup key := by
    by_cases scratch : key=ofString "scratch_ptr"
    · rw [scratch,nextArena.cursorGlobal,arena.cursorGlobal]
    · have pure := globals key source.code installed notHeap scratch (callEntryStateHOLFinite source callee) rfl
      rw [bodyRun] at pure
      exact congrArg Prod.snd pure
  exact ⟨target,items,count,inner,⟨itemModel,countEq,countBound,records,room,nextArena,nextHeap,frame,
    fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,globalsFrame,forward,cost⟩,continued,endpoint⟩

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.scoped_returned
