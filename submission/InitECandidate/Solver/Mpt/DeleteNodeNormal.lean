import InitECandidate.Solver.Mpt.DeleteNodeBodyCall
import InitECandidate.Solver.Mpt.DeleteNodeSetup
import InitECandidate.Solver.Arenas.ScratchCallNormal

namespace InitECandidate.Solver.Mpt.DeleteNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The true wrapper result restores its incoming scratch mark. Bytes
written into the released free pool need not revert. -/
structure Output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (heap cursor frame : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    extends DeleteBody.BodyOutput source target value graph heap cursor frame limit nodeLower pathLower property where
  restored : finalCursor=cursor
  globalsNonHeap : ∀ name,name≠ofString "heap_ptr"→target.globals.lookup name=source.globals.lookup name

theorem released_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (name : MlS)
    (other : name≠ofString "scratch_ptr") : (Arenas.Scratch.released source cursor).globals.lookup name=source.globals.lookup name := by
  simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE,Ne.symm other]

/-- Whole unchanged255 wrapper. Its actual mark, scalar declarations,
genuinely returning caught body call, normal release and original res
return derive the restored cursor and complete physical trie result.
The MptErr handler cannot supply a normal root. -/
theorem body_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (heap cursor frame node key length level : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (small : length.toNat≤64) (within : level.toNat≤length.toNat) (empty : property 0#64 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    Nonempty (Output source target value graph heap cursor frame limit nodeLower pathLower property) := by
  obtain ⟨_funded,markInner,markedRun,markEndpoint⟩:=mark_entry source target cursor value scratch.cursorGlobal installed normal
  let markState:=marked source cursor
  obtain ⟨inner,coreRun,scalarEndpoint⟩:=scalar_entry markState markInner value markedRun
  let ready:=scalarSetup markState
  have saved (name : String) (notError : ofString "e"≠ofString name) (notResult : ofString "res"≠ofString name) (notMark : ofString "mark"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (scalar_saved markState name notError notResult).trans (mark_saved source cursor name notMark)
  have readyNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=(saved "node" (by decide) (by decide) (by decide)).trans nodeCell
  have readyKey : ready.locals.lookup (ofString "key")=some (.val (.word key)):=(saved "key" (by decide) (by decide) (by decide)).trans keyCell
  have readyLength : ready.locals.lookup (ofString "klen")=some (.val (.word length)):=(saved "klen" (by decide) (by decide) (by decide)).trans lengthCell
  have readyLevel : ready.locals.lookup (ofString "level")=some (.val (.word level)):=(saved "level" (by decide) (by decide) (by decide)).trans levelCell
  have readyScratch:=scratch.of_fields source ready cursor frame rfl rfl
  rw [shapes.2.2.2.1] at coreRun
  obtain ⟨middle,called,afterRun⟩:=Input.sequence_returned ready inner caughtCall afterCall value (fun returned=>caught_never_returns ready returned) coreRun
  obtain ⟨returned,localsEq,⟨output⟩⟩:=caught_body_normal ready middle heap cursor frame node key length level graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member
    readyNode readyKey readyLength readyLevel small within empty heapCell heapArena heapAligned readyScratch scratchBefore floor pathFloor nodeFloor little installed called
  have readyMark : ready.locals.lookup (ofString "mark")=some (.val (.word cursor)):=
    (scalar_saved markState "mark" (by decide) (by decide)).trans (bind_lookup_same {source with clock:=source.clock-1} "mark" cursor)
  have markCell : middle.locals.lookup (ofString "mark")=some (.val (.word cursor)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "res"≠ofString "mark" from by decide] using readyMark
  have resultCell : middle.locals.lookup (ofString "res")=some returned:=by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE]
  rw [shapes.2.2.2.2.1] at afterRun
  obtain ⟨last,released,returnRun⟩:=Input.sequence_returned middle inner release footer value
    (fun returned=>Input.NoReturn.ignored_call (ofString "scratch_release") releaseArguments middle returned) afterRun
  have args : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) releaseArguments=some [.val (.word cursor)]:=by
    simp [releaseArguments,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,markCell]
  have currentInstalled : Input.OriginalCode.Installed middle.code:=by rw [output.code]; exact installed
  obtain ⟨_releaseFunded,lastEq⟩:=Arenas.Scratch.release_call_normal middle last cursor output.finalCursor releaseArguments args output.scratch.cursorGlobal currentInstalled released
  obtain ⟨read,innerEq⟩:=Input.return_normal last inner (localVar "res") value returnRun
  have lastResult : last.locals.lookup (ofString "res")=some returned:=by rw [lastEq]; exact resultCell
  have expected : eval last (localVar "res")=some returned:=by simp [eval,localVar,evalHOLExact,toExact,lastResult]
  have valueEq : value=returned:=Option.some.inj (read.symm.trans expected)
  rw [markEndpoint,scalarEndpoint,innerEq,lastEq]
  let final:=restore source "mark" (restore markState "e" (restore (QueryBranch.bind markState "e" 0#64) "res"
    (emptyLocalsHOLFinite (Arenas.Scratch.released {middle with clock:=middle.clock-1} cursor))))
  have finalScratch : Rlp.Validation.Arena final cursor frame:={
    domain:=output.domain.trans scratch.domain
    cursorGlobal:=by
      change (Arenas.Scratch.released {middle with clock:=middle.clock-1} cursor).globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))
      simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE]
    limitGlobal:=(released_other {middle with clock:=middle.clock-1} cursor (ofString "frame_mem_ptr") (by decide)).trans output.scratch.limitGlobal
    ordered:=scratch.ordered
    aligned:=scratch.aligned
    lower:=scratch.lower
    upper:=scratch.upper }
  let result : DeleteBody.BodyOutput source final value graph heap cursor frame limit nodeLower pathLower property := {
    output with
    finalCursor:=cursor
    answer:=valueEq.trans output.answer
    globals:=fun name notHeap notScratch=>(released_other {middle with clock:=middle.clock-1} cursor name notScratch).trans (output.globals name notHeap notScratch)
    heapCell:=(released_other {middle with clock:=middle.clock-1} cursor (ofString "heap_ptr") (by decide)).trans output.heapCell
    scratch:=finalScratch
    scratchDecreases:=Nat.le_refl _ }
  exact ⟨{
    toBodyOutput:=result
    restored:=rfl
    globalsNonHeap:=by
      intro name notHeap
      by_cases isScratch : name=ofString "scratch_ptr"
      · subst name
        exact result.scratch.cursorGlobal.trans scratch.cursorGlobal.symm
      · exact result.globals name notHeap isScratch }⟩

end InitECandidate.Solver.Mpt.DeleteNode

#print axioms InitECandidate.Solver.Mpt.DeleteNode.released_other
#print axioms InitECandidate.Solver.Mpt.DeleteNode.body_path_normal
