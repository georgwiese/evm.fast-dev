import InitECandidate.Solver.Mpt.NibblesConcatAllocation
import InitECandidate.Solver.Mpt.NibblesConcatCopies
import InitECandidate.Solver.Mpt.NibblesConcatMemory
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The whole original concatenation derives successful allocation and
both exact copies from its actual normal return. All older words survive;
the complete joined path, including bytes beyond64, is in its fresh buffer. -/
theorem body_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap a al b bl : BitVec 64)
    (left : TrieWalk.NibbleSpan source.memory source.memaddrs source.be a al.toNat)
    (right : TrieWalk.NibbleSpan source.memory source.memaddrs source.be b bl.toNat)
    (sourceA : AllocatedBytes.Arena a al.toNat) (sourceB : AllocatedBytes.Arena b bl.toNat)
    (leftBefore : a.toNat+al.toNat≤heap.toNat) (rightBefore : b.toNat+bl.toNat≤heap.toNat)
    (aCell : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (alCell : source.locals.lookup (ofString "al")=some (.val (.word al)))
    (bCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (blCell : source.locals.lookup (ofString "bl")=some (.val (.word bl)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word heap) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (al+bl)))),
        memory:=copyMemory source.memory heap a al b bl} ∧
      AllocatedBytes.Arena (PersistentAlloc.rounded heap (al+bl)) 0 ∧ (PersistentAlloc.rounded heap (al+bl)).toNat%8=0 ∧
      heap.toNat+al.toNat+bl.toNat≤(PersistentAlloc.rounded heap (al+bl)).toNat ∧
      TrieWalk.NibbleSpan target.memory target.memaddrs target.be heap (al.toNat+bl.toNat) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) := by
  obtain ⟨amount,destination,nextArena,nextAligned,grows,inner,continued,endpoint⟩:=
    allocation_entry source target heap a al b bl sourceA sourceB alCell blCell heapCell frontier installed value normal
  let ready:=allocated source heap al bl
  have aReady : ready.locals.lookup (ofString "a")=some (.val (.word a)):=
    (allocated_lookup_other source heap al bl "a" (by decide)).trans aCell
  have alReady : ready.locals.lookup (ofString "al")=some (.val (.word al)):=
    (allocated_lookup_other source heap al bl "al" (by decide)).trans alCell
  have bReady : ready.locals.lookup (ofString "b")=some (.val (.word b)):=
    (allocated_lookup_other source heap al bl "b" (by decide)).trans bCell
  have blReady : ready.locals.lookup (ofString "bl")=some (.val (.word bl)):=
    (allocated_lookup_other source heap al bl "bl" (by decide)).trans blCell
  have outReady : ready.locals.lookup (ofString "out")=some (.val (.word heap)):=bind_lookup_same _ "out" heap
  obtain ⟨answer,innerEq⟩:=copies_normal ready inner heap a al b bl sourceA sourceB destination aReady alReady bReady blReady outReady domain installed value continued
  have memoryEq : target.memory=copyMemory source.memory heap a al b bl:=by
    rw [endpoint,innerEq]
    simp only [restore,emptyLocalsHOLFinite,copied,CopyGeneral.callState,ready,allocated,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,copyMemory,little]
  have frame : Input.LocalEffects.erase target=Input.LocalEffects.erase {source with
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (al+bl)))),
      memory:=copyMemory source.memory heap a al b bl}:=by
    rw [endpoint,innerEq]
    simp only [Input.LocalEffects.erase,restore,emptyLocalsHOLFinite,copied,CopyGeneral.callState,ready,allocated,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,copyMemory,little]
  have fields:=Input.evaluation_fields source target body (some (.returned value)) normal
  have leftLittle : TrieWalk.NibbleSpan source.memory source.memaddrs false a al.toNat:=by simpa only [little] using left
  have rightLittle : TrieWalk.NibbleSpan source.memory source.memaddrs false b bl.toNat:=by simpa only [little] using right
  obtain ⟨span,older⟩:=memory_path source.memory source.memaddrs heap a al b bl leftLittle rightLittle sourceA sourceB destination aligned leftBefore rightBefore
    (fun offset inside=>AllocatedBytes.byte_mapped source heap (al.toNat+bl.toNat) offset domain destination inside)
  exact ⟨answer,frame,nextArena,nextAligned,grows,(by rw [memoryEq,fields.1,fields.2.1,little]; exact span),
    fun query before=>(congrFun memoryEq query).trans (older query before)⟩

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.body_path_normal
