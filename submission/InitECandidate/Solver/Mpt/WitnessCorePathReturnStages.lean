import InitECandidate.Solver.Mpt.WitnessCorePathBranchScope
import InitECandidate.Solver.Mpt.WitnessCorePathExtension

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual original return-stage dispatch retains the complete active
registry on branch advance or on either genuine parent-pop path. -/
theorem ActiveRegistry.return_stages_paths_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap finalHeap cursor limit child slot : BitVec 64) (entry : Entry) (rest : List Entry)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩) (paths : registry.PathModel)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (owned : ResultOwned source entry.mark heap.toNat child)
    (frontierLower : 2713731432≤frontier) (frontierBefore : frontier≤heap.toNat)
    (fresh : frontier≤entry.data.payload.startAddress) (dbUpper : db.toNat≤33806089496)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word slot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 0#64)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (actualHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
    (normal : evaluateHOLFiniteState source returnStages=(none,post)) :
    BranchPathResult post frontier db finalHeap cursor entry rest := by
  have head:=view.records entry List.mem_cons_self
  rw [return_stages_choice source entry.record db entry.data head topCell] at normal
  cases payload : entry.data.payload with
  | extension nibbles length=>
    rw [payload] at normal
    have registryPost:=registry.extension_paths_normal source post frontier db heap finalHeap cursor limit nibbles length child entry rest paths view payload owned frontierLower frontierBefore
      (by simpa only [payload,WitnessRecord.Payload.startAddress] using fresh)
      topCell resultCell heapCell heapArena heapAligned arena installed actualHeap normal
    obtain ⟨next,nextCell,nextArena,aligned,grows,scratch,tail,resultOwned,actualTop,actualResult,globals,other,memory,domain,endian,code,rank,extensionView,frame,before⟩:=
      return_extension_stack_normal source post db heap cursor limit nibbles length child entry rest view payload owned topCell resultCell heapCell heapArena heapAligned arena installed normal
    have actualMode : post.locals.lookup (ofString "mode")=some (.val (.word 0#64)) :=
      (other "mode" (by decide) (by decide) (by decide) (by decide)).trans modeCell
    exact Or.inr ⟨actualMode,registryPost⟩
  | branch node index occupied=>
    rw [payload] at normal
    obtain ⟨step,globals,scratch,other,domain,endian,code,memory⟩:=return_branch_stack_normal source post db heap cursor limit node child slot entry rest index occupied
      view payload topCell resultCell slotCell modeCell arena installed normal
    have actualSourceHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by rw [globals]; exact heapCell
    have same : finalHeap=heap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualHeap.symm.trans actualSourceHeap)))
    subst finalHeap
    exact registry.branch_paths_normal source post frontier db heap cursor limit node child slot entry rest index occupied paths view payload frontierLower
      (by simpa only [payload,WitnessRecord.Payload.startAddress] using fresh) dbUpper topCell resultCell slotCell modeCell arena installed normal

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.return_stages_paths_normal
