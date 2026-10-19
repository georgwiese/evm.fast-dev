import InitECandidate.Solver.Rlp.ListCountItemsNormal
import InitECandidate.Solver.Rlp.DecodeGlobals
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real returning scoped count call supplies its exact item sequence
at the reached memory, unchanged heap cursor and actual continuation. -/
theorem scoped_normal_items (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (cutoff : Nat) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_count") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ calleePost items count inner,
      ListItems calleePost pointer length.toNat items ∧ count.toNat=items.length ∧
      Validation.Arena calleePost cursor limit ∧ Validation.Above source calleePost cursor.toNat ∧
      calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      source.clock-calleePost.clock≤60*length.toNat+32 ∧
      evaluateHOLFiniteState (bind {calleePost with locals:=source.locals} name count) continuation=(some (.returned returned),inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") body .one pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,value,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_normal source post name .one (ofString "rlp_list_count") arguments _ body continuation callee .one args called returned normal
  have entryArena := Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  obtain ⟨items,count,itemModel,valueEq,countNumber,nextArena,above⟩ :=
    body_items (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit cutoff pointerLocal lengthLocal entryArena fits
      aligned scratchBelow inputAbove installed value bodyRun
  have currentItems : ListItems source pointer length.toNat items :=
    ListItems.transport (callEntryStateHOLFinite source callee) source pointer length.toNat items itemModel length.isLt (by intro offset inside; rfl)
  have fields := Input.evaluation_fields (callEntryStateHOLFinite source callee) calleePost body (some (.returned value)) bodyRun
  have byteFrame := Validation.Above.bytes_agree source calleePost cutoff pointer length
    (Validation.Above.mono source calleePost cursor.toNat cutoff above scratchBelow) aligned inputAbove fits fields.1 fields.2.1
  have reachedItems := ListItems.transport source calleePost pointer length.toNat items currentItems length.isLt byteFrame
  have heapFrame := globals (ofString "heap_ptr") source.code installed (by decide) (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at heapFrame
  have heapEq := congrArg Prod.snd heapFrame
  have price := body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  rw [bodyRun] at price
  change source.clock-1-calleePost.clock≤60*length.toNat+31 at price
  rw [valueEq] at continuationRun
  exact ⟨positive,calleePost,items,count,inner,reachedItems,countNumber,nextArena,above,heapEq,by omega,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.scoped_normal_items
