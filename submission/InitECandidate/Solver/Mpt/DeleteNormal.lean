import InitECandidate.Solver.Mpt.DeleteDescentInitial
import InitECandidate.Solver.Mpt.DeleteDescentNormal
import InitECandidate.Solver.Mpt.DeleteUnwindNormal
import InitECandidate.Solver.Mpt.DeleteBodyOutput
import InitECandidate.Solver.Mpt.TrieGraphPathErase
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole unchanged254 deletion body: follow the real setup, both actual
loops, returned res and lexical exits. The resulting physical registry,
fresh membership, heap/scratch geometry and protected memory are derived
from execution; no future helper or allocator success is assumed. -/
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
    Nonempty (BodyOutput source target value graph heap cursor frame limit nodeLower pathLower property) := by
  obtain ⟨initial,initialHeap,initialMembers,_initialFrames,_initialGo,initialCursor,initialFrame,_initialNode,_initialLevel,initialGraph⟩:=
    initial_descent_model source heap cursor frame node key length level graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member
      nodeCell keyCell lengthCell levelCell small within heapCell heapArena heapAligned scratch scratchBefore floor pathFloor nodeFloor little installed
  obtain ⟨inner,_clock,erase,continued⟩:=normal_setup source target value normal
  rw [setup_shapes.2.2.2.1] at continued
  have descentSafe : Input.LocalPrefix (ofString "key") descent:=by rw [descent_shapes.1]; exact .loop _ descent_body_safe
  obtain ⟨middle,descentRun,remainingRun⟩:=Input.sequence_returned (setup source) inner descent afterDescent value
    (fun returned=>(descentSafe.summary_full (setup source)).2.1 returned) continued
  obtain ⟨⟨descended,_stopped⟩⟩:=descent_path_normal (setup source) middle key length limit nodeLower pathLower property initial empty descentRun
  rw [setup_shapes.2.2.2.2.1] at remainingRun
  have unwindSafe : Input.LocalPrefix (ofString "key") unwind:=by rw [unwind_shapes.1]; exact .loop _ unwind_body_safe
  obtain ⟨last,unwindRun,returnRun⟩:=Input.sequence_returned middle inner unwind footer value
    (fun returned=>(unwindSafe.summary_full middle).2.1 returned) remainingRun
  obtain ⟨finished,_topZero,_empty,unwindGrows,unwindMembers,unwindFields,unwindMemory,unwindGlobals,unwindFresh,_unwindProtection⟩:=
    unwind_path_normal middle last limit nodeLower pathLower property descended.next.pending unwindRun
  rw [setup_shapes.2.2.2.2.2] at returnRun
  obtain ⟨read,innerEq⟩:=Input.return_normal last inner (localVar "res") value returnRun
  have expected : eval last (localVar "res")=some (.val (.word finished.result)):=by
    simp [eval,localVar,evalHOLExact,toExact,finished.resultCell]
  have answer : value=.val (.word finished.result):=Option.some.inj (read.symm.trans expected)
  rw [innerEq] at erase
  change Input.LocalEffects.erase target=Input.LocalEffects.erase last at erase
  have memoryEq:=Input.LocalEffects.memory_of_erase last target erase
  have globalsEq:=congrArg PanSemStateFiniteExact.globals erase
  change target.globals=last.globals at globalsEq
  have domainEq : target.memaddrs=last.memaddrs:=by
    have projected:=congrArg PanSemStateFiniteExact.memaddrs erase
    exact projected
  obtain ⟨next,same,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=
    finished.graph.after_erase last target limit nodeLower finished.heap.toNat pathLower finished.heap.toNat property finished.values finished.regions finished.disjoint finished.paths finished.pathRegions finished.separated erase
  have descentGrows : heap.toNat≤descended.next.pending.heap.toNat:=by rw [←initialHeap]; exact descended.grows
  have inclusion (current : BitVec 64) (live : graph.valid current) : next.valid current:=by
    rw [same]
    exact unwindMembers current (descended.members current (by rw [initialMembers]; exact live))
  have provenance (current : BitVec 64) (live : next.valid current) : graph.valid current ∨ heap.toNat≤current.toNat:=by
    rw [same] at live
    rcases unwindFresh current live with older|fresh
    · rcases descended.freshMembers current older with original|newer
      · exact Or.inl (by rwa [initialMembers] at original)
      · exact Or.inr (by rwa [initialHeap] at newer)
    · exact Or.inr (descentGrows.trans fresh)
  have cursorEq : finished.cursor=descended.next.pending.cursor:=by
    have currentCell:=(unwindGlobals (ofString "scratch_ptr") (by decide)).trans descended.next.pending.scratch.cursorGlobal
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using finished.scratch.cursorGlobal.symm.trans currentCell
  have frameEq : finished.frame=frame:=by
    have currentCell:=(unwindGlobals (ofString "frame_mem_ptr") (by decide)).trans descended.next.pending.scratch.limitGlobal
    have sameFrame : finished.frame=descended.next.pending.frame:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using finished.scratch.limitGlobal.symm.trans currentCell
    exact sameFrame.trans (descended.frameEq.trans initialFrame)
  have finalScratch : Rlp.Validation.Arena target finished.cursor frame:=by
    have transported:=finished.scratch.of_fields last target finished.cursor finished.frame domainEq globalsEq
    rwa [frameEq] at transported
  have oldFields : graph.PathFields target.memory:=by
    rw [memoryEq]
    have joined:=descended.fields.trans initial.pending.graph descended.next.pending.graph unwindFields descended.members
    rwa [initialGraph] at joined
  have frameBefore : frame.toNat≤nodeLower:=scratch.ordered.trans (scratchBefore.trans (floor.trans pathFloor))
  have low (address : BitVec 64) (before : address.toNat<frame.toNat) : target.memory address=source.memory address:=by
    rw [memoryEq]
    exact (unwindMemory address (before.trans_le frameBefore)).trans (descended.memoryLow address (by rw [initialFrame]; exact before))
  have band (address : BitVec 64) (above : cursor.toNat≤address.toNat) (before : address.toNat<nodeLower) : target.memory address=source.memory address:=by
    rw [memoryEq]
    exact (unwindMemory address before).trans (descended.memoryBand address (by rw [initialCursor]; exact above) before)
  have globalFrame (name : MlS) (notHeap : name≠ofString "heap_ptr") (notScratch : name≠ofString "scratch_ptr") : target.globals.lookup name=source.globals.lookup name:=by
    rw [globalsEq]
    exact (unwindGlobals name notHeap).trans (descended.globals name notHeap notScratch)
  have targetFields:=Input.evaluation_fields source target body (some (.returned value)) normal
  exact ⟨{
    root:=finished.result
    finalHeap:=finished.heap
    finalCursor:=finished.cursor
    answer:=answer
    domain:=targetFields.1
    endian:=targetFields.2.1
    code:=targetFields.2.2.2
    globals:=globalFrame
    heapCell:=by rw [globalsEq]; exact finished.heapCell
    heapArena:=finished.heapArena
    heapAligned:=finished.heapAligned
    grows:=descentGrows.trans unwindGrows
    scratch:=finalScratch
    scratchDecreases:=by rw [cursorEq,←initialCursor]; exact descended.scratchDecreases
    next:=next
    members:=inclusion
    freshMembers:=provenance
    rootMember:=by rw [same]; exact finished.resultMember
    regions:=nextRegions
    disjoint:=nextDisjoint
    values:=nextValues
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated
    fields:=oldFields
    memoryLow:=low
    memoryBand:=band }⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.body_path_normal
