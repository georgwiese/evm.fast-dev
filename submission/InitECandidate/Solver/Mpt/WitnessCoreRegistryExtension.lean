import InitECandidate.Solver.Mpt.WitnessCoreRegistryConstructors
import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A whole genuine original extension return registers its fresh node
and pops the actual active frame, preserving all older pending branches. -/
theorem ActiveRegistry.extension_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap finalHeap cursor limit nibbles length child : BitVec 64) (entry : Entry) (rest : List Entry)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.extension nibbles length)
    (owned : ResultOwned source entry.mark heap.toNat child) (above : cursor.toNat≤frontier) (frontierBefore : frontier≤heap.toNat)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (actualHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
    (normal : evaluateHOLFiniteState source returnExtension=(none,post)) :
    Nonempty (ActiveRegistry post frontier db ⟨finalHeap,cursor,rest,.returning,true⟩) := by
  obtain ⟨next,nextCell,nextArena,nextAligned,grows,scratch,tail,returnedOwned,actualTop,actualResult,globals,locals,memory,domain,endian,code,rank,
      extensionView,frame,before⟩:=return_extension_stack_normal source post db heap cursor limit nibbles length child entry rest view payload owned
    topCell resultCell heapCell heapArena heapAligned arena installed normal
  have same : next=finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nextCell.symm.trans actualHeap)))
  subst next
  have childMember:=registry.returned rfl child resultCell
  obtain ⟨nodes,member,includes,members⟩:=registry.nodes.extension_result source post frontier db heap finalHeap cursor limit nibbles length child
    above frontierBefore frame extensionView actualHeap before childMember
  have children:=registry.children.normal_frame source post registry.nodes.graph.valid nodes.graph.valid db heap cursor limit (entry::rest)
    view includes (by have ceiling:=(view.records entry List.mem_cons_self).ceiling; have lower:=view.above entry List.mem_cons_self; omega) frame
  have tailChildren:=children.tail post nodes.graph.valid entry rest
  have tags:=registry.nodes.tags_normal source post frontier heap db cursor limit above frame
  have excluded:=registry.excludes_extension source post frontier db _ view nodes.graph heap members tags (fun _=>Nat.le_refl _)
  refine ⟨⟨nodes,tailChildren,?_,?_⟩⟩
  · intro current member node index occupied currentPayload
    exact excluded current (List.mem_cons_of_mem entry member) node index occupied currentPayload
  · intro phase node cell
    have same : node=heap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans actualResult)))
    subst node
    exact member

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.extension_normal
