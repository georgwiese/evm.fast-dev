import InitECandidate.Solver.Rlp.SlicesCallNormal
import InitECandidate.Solver.Rlp.SlicesGlobals
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual original first/second pass output, with the current persistent
allocation and separate scratch footprint derived from its genuine return. -/
structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit count : BitVec 64) (items : List ListItem) : Prop where
  itemsAtReturn : ListItems target pointer length.toNat items
  countEq : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  records : Records target.memory heap pointer items
  room : heap.toNat+16*count.toNat≤33806089496
  arena : Validation.Arena target cursor limit
  heapGlobal : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64))))
  memory : ∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+16*count.toNat≤query.toNat →
    target.memory query=source.memory query
  code : target.code=source.code
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  exceptions : target.eshapes=source.eshapes
  globals : ∀ key,key≠ofString "heap_ptr" → target.globals.lookup key=source.globals.lookup key
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤71*length.toNat+35

/-- All outcomes of a scoped original slice conversion: stopped calls are
priced, while a real return supplies its concrete records and continuation. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_list_to_slices") expressions continuation)=(outcome,post)) :
    source.clock-post.clock≤71*length.toNat+35 ∨
      ∃ target items count inner,Returned source target pointer length heap cursor limit count items ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (result heap count)) continuation=(outcome,inner) ∧ post=restore source name inner := by
  have fits : pointer.toNat+length.toNat<2^64 := by have := heap.isLt; omega
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code installed)
  have entryArena := Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price := body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  rcases Input.CallNormal.scoped_trace source post name resultShape (ofString "rlp_list_to_slices") expressions _ body continuation callee resultShape (71*length.toNat+34)
      args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,answer,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
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
    exact Or.inr ⟨target,items,count,inner,⟨itemModel,countEq,countBound,records,room,nextArena,nextHeap,frame,
      fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,globalsFrame,forward,cost⟩,continued,endpoint⟩

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.scoped_trace
