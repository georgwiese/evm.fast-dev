import InitECandidate.Solver.Mpt.InsertParentStore
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The whole original insertion footer performs its actual parent/root
update and advances the three loop locals, retaining the complete graph
and every independent current query buffer. -/
theorem footer_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (slot root nextNode nextSlot nextLevel : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower nodeUpper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower nodeUpper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (selected : graph.ParentSlot slot) (member : graph.valid root)
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word slot)))
    (rootCell : source.locals.lookup (ofString "r")=some (.val (.word root)))
    (nodeCell : source.locals.lookup (ofString "next_node")=some (.val (.word nextNode)))
    (nextSlotCell : source.locals.lookup (ofString "next_slot")=some (.val (.word nextSlot)))
    (levelCell : source.locals.lookup (ofString "next_level")=some (.val (.word nextLevel)))
    (normal : evaluateHOLFiniteState source afterChoice=(none,target)) :
    target.locals=(((if slot=0#64 then source.locals.update (ofString "result",.val (.word root)) else source.locals).update
      (ofString "node",.val (.word nextNode))).update (ofString "slot",.val (.word nextSlot))).update (ofString "level",.val (.word nextLevel)) ∧
      target.globals=source.globals ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ target.clock=source.clock ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ node,graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower nodeUpper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated ∧
        (∀ key length,graph.PathBuffer source.be pathLower pathUpper key length → next.PathBuffer target.be pathLower pathUpper key length) ∧
        graph.PathFields target.memory ∧ (∀ address : BitVec 64,(slot≠0#64 → address≠slot) → target.memory address=source.memory address) := by
  rw [after_choice_shape] at normal
  obtain ⟨middle,chosen,continued⟩:=Input.sequence_none source target _ _ normal
  obtain ⟨localsEq,globalsEq,domainEq,endianEq,codeEq,clockEq,memory,tags,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,buffers,fields,protectedWords⟩:=
    choose_result_normal source middle slot root graph limit nodeLower nodeUpper pathLower pathUpper property values regions disjoint paths pathRegions separated selected member slotCell rootCell chosen
  have current (name : MlS) (other : name≠ofString "result") : middle.locals.lookup name=source.locals.lookup name:=by
    rw [localsEq]
    split
    · simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
    · rfl
  have nextNodeRead : eval middle (localVar "next_node")=some (.val (.word nextNode)):=by
    have cell:=(current (ofString "next_node") (by decide)).trans nodeCell
    simp [eval,evalHOLExact,toExact,localVar,cell]
  obtain ⟨one,nodeRun,continued⟩:=Input.sequence_none middle target _ _ continued
  have oneEq:=Input.assign_none middle one "node" (localVar "next_node") nextNode nextNodeRead nodeRun
  subst one
  let first:=QueryBranch.bind middle "node" nextNode
  have nextSlotRead : eval first (localVar "next_slot")=some (.val (.word nextSlot)):=by
    have cell:=(bind_lookup_other middle "node" "next_slot" nextNode (by decide)).trans ((current _ (by decide)).trans nextSlotCell)
    simp [eval,evalHOLExact,toExact,localVar,show first.locals.lookup (ofString "next_slot")=some (.val (.word nextSlot)) from cell]
  obtain ⟨two,slotRun,levelRun⟩:=Input.sequence_none first target _ _ continued
  have twoEq:=Input.assign_none first two "slot" (localVar "next_slot") nextSlot nextSlotRead slotRun
  subst two
  let second:=QueryBranch.bind first "slot" nextSlot
  have nextLevelRead : eval second (localVar "next_level")=some (.val (.word nextLevel)):=by
    have cell:=(bind_lookup_other first "slot" "next_level" nextSlot (by decide)).trans
      ((bind_lookup_other middle "node" "next_level" nextNode (by decide)).trans ((current _ (by decide)).trans levelCell))
    simp [eval,evalHOLExact,toExact,localVar,show second.locals.lookup (ofString "next_level")=some (.val (.word nextLevel)) from cell]
  have endpoint:=Input.assign_none second target "level" (localVar "next_level") nextLevel nextLevelRead levelRun
  rw [endpoint]
  have finalLocals : (QueryBranch.bind second "level" nextLevel).locals=(((if slot=0#64 then source.locals.update (ofString "result",.val (.word root)) else source.locals).update
      (ofString "node",.val (.word nextNode))).update (ofString "slot",.val (.word nextSlot))).update (ofString "level",.val (.word nextLevel)):=by
    change ((middle.locals.update (ofString "node",.val (.word nextNode))).update (ofString "slot",.val (.word nextSlot))).update (ofString "level",.val (.word nextLevel))=_
    rw [localsEq]
  exact ⟨finalLocals,globalsEq,domainEq,endianEq,codeEq,clockEq,memory,tags,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,buffers,fields,protectedWords⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.footer_normal
