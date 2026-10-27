import InitECandidate.Solver.PanDeclarations
import InitECandidate.Solver.Input.VarList.LoopReturn

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def initial (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first : BitVec 64) := bind (bind source "i" 0#64) "prev" first
def restoreInitial (source : PanSemStateFiniteExact 64 Guest.HostMemory) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "i" (restore (bind source "i" 0#64) "prev" target)

/-- Entire fixed tail after record-array allocation: both initialization scopes,
all record-loop outcomes, final length store and pair return. The allocator
itself must supply the stated fresh-array plan and local binding. -/
theorem allocated_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (first total : BitVec 64) (heap : Blob.HeapInput source input plan.inputPointer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word plan.array)))
    (p : source.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (c : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : plan.count+1≤source.clock) :
    ∃ result target paid,
      evaluateHOLFiniteState source allocatedTail=(result,target) ∧ paid≤plan.count+1 ∧ target.clock=source.clock-paid ∧
      WitnessRadix.BackingLayout.control target=WitnessRadix.BackingLayout.control source ∧ Blob.HeapInput target input plan.inputPointer ∧ ArrayFrame source target input plan ∧
      ((result=some (.returned (pairValue plan.array plan.count)) ∧ paid=plan.count ∧ Complete target input plan total ∧
          ∀ position,position<plan.count→Offsets.ValidAt first total (currentWord input plan.start) position) ∨
        result=some (.exception (ofString "SszErr") (.val (.word 23#64)))) := by
  let entered:=initial source first
  have savedF : (bind source "i" 0#64).locals.lookup (ofString "first")=some (.val (.word first)) :=
    (bind_lookup_other source "i" "first" 0#64 (by decide)).trans f
  have read : eval (bind source "i" 0#64) (localVar "first") = some (.val (.word first)) := by
    simpa [eval, localVar, evalHOLExact, toExact] using savedF
  have setup : WitnessRadix.BuildEntry.Initializes source [("i", .const 0#64), ("prev", localVar "first")] entered (restoreInitial source) :=
    WitnessRadix.BuildEntry.Initializes.step 0#64 rfl (.step first read (.done _))
  have enteredHeap : Blob.HeapInput entered input plan.inputPointer :=
    Blob.HeapInput.bind (bind source "i" 0#64) input plan.inputPointer "prev" first (Blob.HeapInput.bind source input plan.inputPointer "i" 0#64 heap)
  have ea : entered.locals.lookup (ofString "arr")=some (.val (.word (plan.array))) :=
    (bind_lookup_other (bind source "i" 0#64) "prev" "arr" first (by decide)).trans ((bind_lookup_other source "i" "arr" 0#64 (by decide)).trans a)
  have ep : entered.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))) :=
    (bind_lookup_other (bind source "i" 0#64) "prev" "p" first (by decide)).trans ((bind_lookup_other source "i" "p" 0#64 (by decide)).trans p)
  have ef : entered.locals.lookup (ofString "first")=some (.val (.word (first))) :=
    (bind_lookup_other (bind source "i" 0#64) "prev" "first" first (by decide)).trans ((bind_lookup_other source "i" "first" 0#64 (by decide)).trans f)
  have en : entered.locals.lookup (ofString "len")=some (.val (.word (total))) :=
    (bind_lookup_other (bind source "i" 0#64) "prev" "len" first (by decide)).trans ((bind_lookup_other source "i" "len" 0#64 (by decide)).trans n)
  have ec : entered.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))) :=
    (bind_lookup_other (bind source "i" 0#64) "prev" "count" first (by decide)).trans ((bind_lookup_other source "i" "count" 0#64 (by decide)).trans c)
  have ei : entered.locals.lookup (ofString "i")=some (.val (.word 0#64)) :=
    (bind_lookup_other (bind source "i" 0#64) "prev" "i" first (by decide)).trans (bind_lookup_same _ _ _)
  obtain ⟨result,target,paid,run,bound,clock,control,heapAfter,arrayFrame,outcome⟩:=loop_return entered input plan first total enteredHeap domain ea ei ep (bind_lookup_same _ _ _) ef en ec failCode exceptionShape enough
  have declared:=WitnessRadix.BuildEntry.declarations_execute setup (.seq loop afterLoop)
  rw [run] at declared
  let final:=restoreInitial source target
  have finalHeap : Blob.HeapInput final input plan.inputPointer :=
    Blob.HeapInput.restore source _ input plan.inputPointer "i" (Blob.HeapInput.restore (bind source "i" 0#64) target input plan.inputPointer "prev" heapAfter)
  have finalControl : WitnessRadix.BackingLayout.control final=WitnessRadix.BackingLayout.control source := by
    exact control
  have finalFrame : ArrayFrame source final input plan := by
    intro query outside
    exact arrayFrame query outside
  refine ⟨result,final,paid,?_,bound,clock,finalControl,finalHeap,finalFrame,?_⟩
  · rw [allocated_tail_shape]
    exact declared
  · rcases outcome with normal|fault
    · exact Or.inl ⟨normal.1,normal.2.1,normal.2.2.1,normal.2.2.2⟩
    · exact Or.inr fault

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.allocated_execute
