import InitECandidate.Solver.Mpt.InsertIterationDispatch
import InitECandidate.Solver.Mpt.InsertFooterNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A whole normal original251 iteration preserves the current physical
loop model and all older graph members. It either clears go or strictly
increases the consumed key length, with no acyclicity assumption. -/
theorem iteration_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length pointer size : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (model : LoopModel source key length pointer size limit nodeLower pathLower property) (active : model.go≠0#64)
    (extra : property pointer size) (empty : property 0#64 0#64)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ next : LoopModel target key length pointer size limit nodeLower pathLower property,
      model.heap.toNat≤next.heap.toNat ∧ (∀ node,model.graph.valid node → next.graph.valid node) ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ node,model.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node) ∧
      (next.go=0#64 ∨ model.level.toNat<next.level.toNat) ∧ model.graph.PathFields target.memory ∧
      (∀ address : BitVec 64,model.graph.ProtectedWord address → address.toNat<model.heap.toNat → target.memory address=source.memory address) ∧
      (next.go≠0#64 → next.graph.valid=model.graph.valid) ∧
      (∀ node,next.graph.valid node → model.graph.valid node ∨ model.heap.toNat≤node.toNat) ∧
      (∀ address : BitVec 64,model.graph.ProtectedWord address → address.toNat<model.heap.toNat →
        TrieWalk.PathWordAway key length.toNat address → next.graph.ProtectedWord address) := by
  obtain ⟨chosen,finished,choiceRun,footerRun,endpoint⟩:=iteration_entry_normal source target normal
  obtain ⟨output⟩:=dispatch_output source chosen key length pointer size limit nodeLower pathLower property model active extra empty choiceRun
  have chosenSaved (name : String) (notRoot : ofString name≠ofString "r") (notNode : ofString name≠ofString "next_node")
      (notSlot : ofString name≠ofString "next_slot") (notLevel : ofString name≠ofString "next_level") (notGo : ofString name≠ofString "go") :
      chosen.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (output.stable (ofString name) notRoot notNode notSlot notLevel notGo).trans (dispatch_saved source name notRoot notNode notSlot notLevel notGo)
  have chosenSlot : chosen.locals.lookup (ofString "slot")=some (.val (.word model.slot)):=
    (chosenSaved _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.slotCell
  have chosenResult : chosen.locals.lookup (ofString "result")=some (.val (.word model.result)):=
    (chosenSaved _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.resultCell
  have selected:=model.parentSlot.of_tags model.graph output.graph model.slot output.oldMember output.tags
  obtain ⟨localsEq,globalsEq,domainEq,endianEq,codeEq,clockEq,memory,tags,graph,same,regions,disjoint,⟨values⟩,paths,pathRegions,separated,buffers,footerFields,footerWords⟩:=
    footer_normal chosen finished model.slot output.root output.nextNode output.nextSlot output.nextLevel output.graph
      limit nodeLower output.heap.toNat pathLower output.heap.toNat property output.values output.regions output.disjoint output.paths output.pathRegions output.separated
      selected output.rootMember chosenSlot output.rootCell output.nodeCell output.slotCell output.levelCell footerRun
  have finishedSaved (name : String) (notResult : ofString name≠ofString "result") (notNode : ofString name≠ofString "node")
      (notSlot : ofString name≠ofString "slot") (notLevel : ofString name≠ofString "level") :
      finished.locals.lookup (ofString name)=chosen.locals.lookup (ofString name):=by
    rw [localsEq]
    split <;> simp [HolFiniteMapExact.update,FUPDATE,Ne.symm notResult,Ne.symm notNode,Ne.symm notSlot,Ne.symm notLevel]
  have finishedNode : finished.locals.lookup (ofString "node")=some (.val (.word output.nextNode)):=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,ofString]
  have finishedSlot : finished.locals.lookup (ofString "slot")=some (.val (.word output.nextSlot)):=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,ofString]
  have finishedLevel : finished.locals.lookup (ofString "level")=some (.val (.word output.nextLevel)):=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,ofString]
  let result:=if model.slot=0#64 then output.root else model.result
  have finishedResult : finished.locals.lookup (ofString "result")=some (.val (.word result)):=by
    by_cases zero : model.slot=0#64
    · rw [localsEq]
      simp [result,zero,HolFiniteMapExact.update,FUPDATE,ofString]
    · simpa [localsEq,result,zero,HolFiniteMapExact.update,FUPDATE,ofString] using chosenResult
  have nextResult : graph.valid result:=by
    rw [same]
    by_cases zero : model.slot=0#64
    · simpa only [result,if_pos zero] using output.rootMember
    · simpa only [result,if_neg zero] using output.oldMember model.result model.resultMember
  have nextParent:=output.nextParent.of_tags output.graph graph output.nextSlot (by intro node live; rw [same]; exact live) tags
  have finalLookup (name : String) (notRoot : ofString name≠ofString "r") (notNode : ofString name≠ofString "next_node")
      (notSlot : ofString name≠ofString "next_slot") (notLevel : ofString name≠ofString "next_level") :
      (iterationRestore source finished).locals.lookup (ofString name)=finished.locals.lookup (ofString name):=
    iteration_restore_lookup source finished name notRoot notNode notSlot notLevel
  have finishedKey :=(finishedSaved "key" (by decide) (by decide) (by decide) (by decide)).trans
    ((chosenSaved "key" (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.keyCell)
  have finishedLength :=(finishedSaved "klen" (by decide) (by decide) (by decide) (by decide)).trans
    ((chosenSaved "klen" (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.lengthCell)
  have finishedPointer :=(finishedSaved "vptr" (by decide) (by decide) (by decide) (by decide)).trans
    ((chosenSaved "vptr" (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.pointerCell)
  have finishedSize :=(finishedSaved "vlen" (by decide) (by decide) (by decide) (by decide)).trans
    ((chosenSaved "vlen" (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.sizeCell)
  let next : LoopModel (iterationRestore source finished) key length pointer size limit nodeLower pathLower property:={
    node:=output.nextNode
    slot:=output.nextSlot
    result:=result
    level:=output.nextLevel
    go:=output.go
    heap:=output.heap
    keyCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans finishedKey
    lengthCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans finishedLength
    pointerCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans finishedPointer
    sizeCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans finishedSize
    nodeCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans finishedNode
    slotCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans finishedSlot
    resultCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans finishedResult
    levelCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans finishedLevel
    goCell:=(finalLookup _ (by decide) (by decide) (by decide) (by decide)).trans ((finishedSaved _ (by decide) (by decide) (by decide) (by decide)).trans output.goCell)
    goTyped:=output.step.elim Or.inl (fun step=>Or.inr step.1)
    activeBound:=by
      intro nonzero
      rcases output.step with stopped|step
      · exact (nonzero stopped).elim
      · exact step.2.2
    bounded:=model.bounded
    domain:=domainEq.trans (output.domain.trans model.domain)
    installed:=by change Input.OriginalCode.Installed finished.code; rw [codeEq,output.code]; exact model.installed
    heapCell:=by change finished.globals.lookup (ofString "heap_ptr")=some (.val (.word output.heap)); rw [globalsEq]; exact output.heapCell
    heapArena:=output.heapArena
    heapAligned:=output.heapAligned
    floor:=model.floor.trans output.heapGrows
    payload:=by change TrieWalk.Payload finished.memaddrs pointer size limit; rw [domainEq,output.domain]; exact model.payload
    graph:=graph
    nodeMember:=by rw [same]; exact output.nodeMember
    resultMember:=nextResult
    parentSlot:=nextParent
    values:=values
    regions:=regions
    disjoint:=disjoint
    paths:=paths
    pathRegions:=pathRegions
    separated:=separated
    query:=fun nonzero=>buffers key length.toNat (output.query nonzero) }
  have inclusion (node : BitVec 64) (live : model.graph.valid node) : next.graph.valid node:=by rw [same]; exact output.oldMember node live
  have olderMemory (query : BitVec 64) (before : query.toNat<nodeLower) : finished.memory query=source.memory query:=
    (memory query before).trans (output.olderPrefix query before)
  have finalTags (node : BitVec 64) (live : model.graph.valid node) (nonzero : node≠0#64) : wordAt finished.memory node=wordAt source.memory node:=
    (tags node (output.oldMember node live) nonzero).trans (output.tags node live nonzero)
  have progress : next.go=0#64 ∨ model.level.toNat<next.level.toNat:=output.step.elim Or.inl (fun step=>Or.inr step.2.1)
  have fields : model.graph.PathFields finished.memory:=
    output.oldPathFields.trans model.graph output.graph footerFields output.oldMember
  have protectedWords (address : BitVec 64) (safe : model.graph.ProtectedWord address) (before : address.toNat<model.heap.toNat) :
      finished.memory address=source.memory address:=by
    have different : model.slot≠0#64 → address≠model.slot:=by
      intro nonzero
      rcases model.parentSlot with zero|⟨owner,offset,member,active,location,equal⟩
      · exact (nonzero zero).elim
      · rw [equal]
        exact safe.nodes owner member active offset (location.bounds source.memory owner offset).2.2.1
    exact (footerWords address different).trans (output.protectedMemory address safe before)
  have activeRegistry : next.go≠0#64 → next.graph.valid=model.graph.valid:=by
    intro active
    exact same.trans (output.activeRegistry active)
  have provenance (node : BitVec 64) (live : next.graph.valid node) : model.graph.valid node ∨ model.heap.toNat≤node.toNat:=by
    exact output.freshMembers node (by rwa [same] at live)
  have protection (address : BitVec 64) (safe : model.graph.ProtectedWord address) (before : address.toNat<model.heap.toNat)
      (away : TrieWalk.PathWordAway key length.toNat address) : next.graph.ProtectedWord address:=by
    exact (output.protectedGraph address safe before away).of_fields output.graph graph address same footerFields
  rw [endpoint]
  exact ⟨next,output.heapGrows,inclusion,olderMemory,finalTags,progress,fields,protectedWords,activeRegistry,provenance,protection⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.iteration_path_normal
