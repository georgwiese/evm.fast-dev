import InitECandidate.Solver.Mpt.CurrentIndexedModel
import InitECandidate.Solver.Input.IgnoredCallTarget

namespace InitECandidate.Solver.Mpt.CurrentIndexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch Input

/-- The actual row and current encoded key supply the setter's true ABI
and complete physical entry. Its nonempty condition belongs to that row. -/
theorem set_entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit encoded : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices) (small : encoded≤9)
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (inside : model.index.toNat<count) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite source.code.lookup (ofString "mpt_set")
        (SetTrie.values m keyPointer (BitVec.ofNat 64 encoded) (slices model.index.toNat).1 (slices model.index.toNat).2)=some (SetTrie.body,callee,.one) ∧
      ∃ entry : IndexedSet.Entry (callEntryStateHOLFinite source callee) m keyPointer encoded
        (slices model.index.toNat).1 (slices model.index.toNat).2 cutoff limit,entry.heap=model.heap := by
  obtain ⟨callee,called,mLocal,keyLocal,lengthLocal,pointerLocal,sizeLocal⟩:=SetTrie.environment source.code.lookup m keyPointer (BitVec.ofNat 64 encoded)
    (slices model.index.toNat).1 (slices model.index.toNat).2 (SetTrie.original_code source.code model.installed)
  let entry : IndexedSet.Entry (callEntryStateHOLFinite source callee) m keyPointer encoded (slices model.index.toNat).1 (slices model.index.toNat).2 cutoff limit:={
    root:=model.root,heap:=model.heap,mCell:=mLocal,keyCell:=keyLocal,lengthCell:=lengthLocal,pointerCell:=pointerLocal,sizeCell:=sizeLocal
    small:=by omega
    pointerActive:=(model.rows.extra model.index.toNat inside).1,sizeActive:=(model.rows.extra model.index.toNat inside).2
    domain:=model.domain,little:=model.little,installed:=model.installed,heapCell:=model.heapCell,heapArena:=model.heapArena,heapAligned:=model.heapAligned
    inputArena:=⟨by decide,by change 2701134808+encoded≤33806089496; omega⟩
    inputBefore:=by change 2701134808+encoded≤model.heap.toNat; have a:=model.headerAbove; have b:=model.headerBefore; have c:=model.floor; omega
    headerArena:=model.headerArena,headerAligned:=model.headerAligned,headerBefore:=model.headerBefore,cutoffAligned:=model.cutoffAligned,floor:=model.floor
    rootStored:=model.rootStored,flagStored:=model.flagStored,payload:=model.rows.payload model.index.toNat inside
    graph:=model.graph,member:=model.member,values:=model.values,regions:=model.regions,disjoint:=model.disjoint,paths:=model.paths,pathRegions:=model.pathRegions,separated:=model.separated }
  exact ⟨callee,called,entry,rfl⟩

/-- Every actual ignored setter outcome costs its current body allowance
plus one caller tick. Failed allocations and short clocks are included. -/
theorem set_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit encoded : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices) (small : encoded≤9)
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (inside : model.index.toNat<count) : source.clock-(evaluateHOLFiniteState source Indexed.setCall).2.clock≤36807 := by
  obtain ⟨callee,called,entry,heapEq⟩:=set_entry model small lengthCell inside
  have args:=Indexed.set_arguments source array m model.index count m.toNat limit encoded slices NonemptyRow model.rows inside model.domain
    model.arrayCell model.mCell model.indexCell lengthCell model.keyGlobal
  exact ClockCost.call_current source (some none) (ofString "mpt_set") Indexed.setArguments _ SetTrie.body callee .one 36806 args called (IndexedSet.body_cost entry)

/-- A real normal setter call retains all rows, its actual unsecured
header and complete graph at the new heap. The caller's four loop locals
are restored by the actual ignored-call ABI. -/
theorem set_model {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit encoded : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices) (small : encoded≤9)
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (inside : model.index.toNat<count) (normal : evaluateHOLFiniteState source Indexed.setCall=(none,target)) :
    ∃ next : LoopModel target m array count cutoff limit slices,next.index=model.index ∧ model.heap.toNat≤next.heap.toNat := by
  obtain ⟨callee,called,entry,heapEq⟩:=set_entry model small lengthCell inside
  have args:=Indexed.set_arguments source array m model.index count m.toNat limit encoded slices NonemptyRow model.rows inside model.domain
    model.arrayCell model.mCell model.indexCell lengthCell model.keyGlobal
  obtain ⟨funded,child,returned,bodyRun⟩:=CallNormal.ignored_callee_return source target (ofString "mpt_set") Indexed.setArguments _ SetTrie.body callee .one args called normal
  obtain ⟨answer,⟨output⟩⟩:=IndexedSet.body_normal entry returned bodyRun
  have endpoint:=CallNormal.ignored_target source target (ofString "mpt_set") Indexed.setArguments _ SetTrie.body callee .one args called returned child bodyRun normal
  have grows : model.heap.toNat≤output.heap.toNat:=calc
    model.heap.toNat=entry.heap.toNat:=congrArg BitVec.toNat heapEq.symm
    _≤output.heap.toNat:=output.grows
  have flagNumber : (m+8#64).toNat=m.toNat+8:=byteAddress_toNat m 8 (by have upper:=model.headerArena.upper; omega)
  have flagAway : m+8#64≠m:=by intro same; have number:=congrArg BitVec.toNat same; rw [flagNumber] at number; omega
  have flagBefore : (m+8#64).toNat<cutoff:=by rw [flagNumber]; have before:=model.headerBefore; omega
  have rowMemory (query : BitVec 64) (_above : 2701134824≤query.toNat) (before : query.toNat<m.toNat) : child.memory query=source.memory query:=
    output.older query (by have a:=model.headerBefore; omega) (by intro same; subst query; omega)
  rw [endpoint]
  let next : LoopModel {child with locals:=source.locals} m array count cutoff limit slices:={
    index:=model.index,root:=output.root,heap:=output.heap,indexCell:=model.indexCell,countCell:=model.countCell,mCell:=model.mCell,arrayCell:=model.arrayCell
    bounded:=model.bounded,countBound:=model.countBound,domain:=output.domain.trans model.domain,little:=output.endian.trans model.little
    installed:=by rw [output.code]; exact model.installed
    keyGlobal:=(output.globals _ (by decide)).trans model.keyGlobal
    heapCell:=output.heapCell,heapArena:=output.heapArena,heapAligned:=output.heapAligned,floor:=Nat.le_trans model.floor grows
    headerArena:=model.headerArena,headerAligned:=model.headerAligned,headerAbove:=model.headerAbove,headerBefore:=model.headerBefore,cutoffAligned:=model.cutoffAligned
    rootStored:=output.rootStored,flagStored:=(output.older (m+8#64) flagBefore flagAway).trans model.flagStored
    rows:=model.rows.of_band source _ array count m.toNat limit slices NonemptyRow output.domain rowMemory
    graph:=output.graph,member:=output.member,values:=output.values,regions:=output.regions,disjoint:=output.disjoint,paths:=output.paths,pathRegions:=output.pathRegions,separated:=output.separated }
  exact ⟨next,rfl,grows⟩

end InitECandidate.Solver.Mpt.CurrentIndexed

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.set_entry
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.set_cost
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.set_model
