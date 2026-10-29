import InitECandidate.Solver.Mpt.CurrentWitnessRootCacheFrame
import InitECandidate.Solver.Input.NoReturnScoped
import InitECandidate.Solver.Input.NoReturnDecision
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real cache guard cannot return from its enclosing root decoder. -/
theorem current_cache_guard_never : NoReturn.Never cacheGuard := by
  have allocated : NoReturn.Never cacheAllocated:=NoReturn.scoped_call _ _ _ _ _
    (NoReturn.sequence _ _ (NoReturn.ignored_call _ _) (NoReturn.store _ _))
  unfold cacheGuard
  apply NoReturn.conditional
  · exact allocated
  · exact NoReturn.skip

/-- Actual normal root-cache suffix returns its original node and keeps
all memory before the original materialization frontier unchanged. -/
theorem current_suffix_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap frontier root node : BitVec 64)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (beforeHeap : frontier.toNat≤heap.toNat)
    (bounds : node=0#64 ∨ frontier.toNat≤node.toNat ∧ node.toNat≤2952790016)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterMaterialize=(some (.returned value),post)) :
    value=.val (.word node) ∧ PersistentNormalFrame source post frontier := by
  rw [suffix_shape] at normal
  obtain ⟨middle,guardRun,footerRun⟩:=Input.sequence_returned source post cacheGuard (.return (localVar "nd")) value
    (current_cache_guard_never source) normal
  have choice : evaluateHOLFiniteState source cacheGuard=
      (if node=0#64 then (none,source) else evaluateHOLFiniteState source cacheAllocated) := by
    simp [cacheGuard,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,nodeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [choice] at guardRun
  have middleFacts : middle.locals.lookup (ofString "nd")=some (.val (.word node)) ∧ PersistentNormalFrame source middle frontier := by
    by_cases zero : node=0#64
    · rw [if_pos zero] at guardRun
      have same : middle=source:=(congrArg Prod.snd guardRun).symm
      rw [same]
      exact ⟨nodeCell,⟨⟨heap,heapCell,heapArena,heapBound,aligned,beforeHeap⟩,rfl,by intros; rfl,by intros; rfl⟩⟩
    · rw [if_neg zero] at guardRun
      obtain ⟨fresh,nodeBound⟩:=bounds.resolve_left zero
      exact current_cache_allocated_frame source middle heap frontier root node rootCell nodeCell beforeHeap fresh nodeBound
        heapCell heapArena heapBound aligned arena guardRun
  obtain ⟨read,endpoint⟩:=return_normal middle post (localVar "nd") value footerRun
  have expected : eval middle (localVar "nd")=some (.val (.word node)):=by simp [eval,evalHOLExact,localVar,toExact,middleFacts.1]
  exact ⟨Option.some.inj (read.symm.trans expected),middleFacts.2.of_erase source middle source post frontier rfl (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.current_cache_guard_never
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.current_suffix_normal_frame
