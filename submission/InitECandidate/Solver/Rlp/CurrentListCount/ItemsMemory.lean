import InitECandidate.Solver.Rlp.CurrentListCount.ItemsLoop
import InitECandidate.Solver.Rlp.CurrentListCount.Memory

namespace InitECandidate.Solver.Rlp.CurrentListCount
open ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete normal original counting derives the actual ordered encodings
covering its input, exact returned item count, arena and scratch footprint. -/
theorem body_items (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Input.CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (before : pointer.toNat+length.toNat≤2952790016)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ items : List ListItem,∃ count : BitVec 64,ListItems source pointer length.toNat items ∧
      value=.val (.word count) ∧ count.toNat=items.length ∧
      Input.MemoryMetadata.erase target=Input.MemoryMetadata.erase source ∧
      Validation.Outside source target 2952790016 2965299200 := by
  rw [body_shape] at normal
  obtain ⟨countInner,countRun,countRestore⟩ := Input.declaration_return_word source target "count" (.const 0#64) 0#64 _ value rfl normal
  let counted := bind source "count" 0#64
  obtain ⟨offInner,offRun,offRestore⟩ := Input.declaration_return_word counted countInner "off" (.const 0#64) 0#64 _ value rfl countRun
  have noReturns : ∀ returned,(evaluateHOLFiniteState (seeded source) loop).1≠some (.returned returned) := by
    rw [loop_shape]
    exact ((Input.LocalPrefix.loop condition loop_body_safe).summary_full (seeded source)).2.1
  obtain ⟨middle,loopRun,returnRun⟩ := Input.sequence_returned (seeded source) offInner loop (.return (localVar "count")) value noReturns offRun
  have view := seeded_view source pointer length pointerCell lengthCell arena fits
  obtain ⟨items,count,itemModel,reached,countNumber,metadata,outside⟩ := loop_items (seeded source) middle pointer length 0#64 0#64 view before installed loopRun
  have currentItems : ListItems source pointer length.toNat items := by
    have actual : ListItems (seeded source) pointer length.toNat items := by simpa using itemModel
    exact ListItems.transport (seeded source) source pointer length.toNat items actual length.isLt (by intro offset inside; rfl)
  obtain ⟨read,returned⟩ := Input.return_normal middle offInner (localVar "count") value returnRun
  have countRead : eval middle (localVar "count")=some (.val (.word count)) := by
    simp [eval,evalHOLExact,localVar,toExact,reached.countCell]
  refine ⟨items,count,currentItems,Option.some.inj (read.symm.trans countRead),by simpa using countNumber,
    ?_,?_⟩
  · rw [countRestore,offRestore,returned]
    exact metadata
  · refine ⟨?_,?_⟩
    · rw [countRestore,offRestore,returned]
      exact outside.runtime
    · intro query outsideQuery
      rw [countRestore,offRestore,returned]
      exact outside query outsideQuery

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.body_items
