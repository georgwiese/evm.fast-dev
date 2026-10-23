import InitECandidate.Solver.Mpt.DeleteFrameStack
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Original node mutation helpers write above the low scratch ceiling.
Their actual prefix memory frame retains every live stack word. -/
theorem Stack.of_before (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff : Nat) (top : BitVec 64)
    (frames : List Saved) (stack : Stack source cursor top frames) (above : ceiling≤cutoff)
    (memory : ∀ query : BitVec 64,query.toNat<cutoff→target.memory query=source.memory query) :
    Stack target cursor top frames :=
  stack.of_memory source target cursor top frames (by intro query _lower upper; exact memory query (upper.trans_le above))

/-- Execute the original pop through the true initialized PREV cell.
The resulting active stack has exactly one fewer actual saved record. -/
theorem pop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (top : BitVec 64)
    (frames : List Saved) (stack : Stack source cursor top frames) (active : top≠0#64)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word top)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (normal : evaluateHOLFiniteState source DeleteBody.pop=(none,target)) :
    ∃ saved tail,frames=saved::tail ∧ top=saved.pointer ∧ target=QueryBranch.bind source "top" saved.previous ∧
      Stack target cursor saved.previous tail ∧ tail.length+1=frames.length := by
  obtain ⟨saved,tail,framesEq,topEq,view,previousCell,rest,decreases⟩:=stack.pop source cursor top frames active
  have mapped : source.memaddrs (top+0#64):=by
    rw [BitVec.add_zero,topEq]
    simpa only [byteAddress,BitVec.add_zero] using field_mapped source saved.pointer view.arena view.aligned domain 0 (by decide) (by decide)
  have read : eval source (DeleteBody.field "top" 0#64)=some (.val (.word saved.previous)):=
    DeleteExtension.field_read source "top" top 0#64 saved.previous topCell mapped (by simpa only [BitVec.add_zero] using previousCell)
  rw [DeleteBody.unwind_shapes.2.2.2.2] at normal
  have endpoint:=Input.assign_none source target "top" _ saved.previous read normal
  refine ⟨saved,tail,framesEq,topEq,endpoint,?_,decreases⟩
  rw [endpoint]
  exact rest.of_memory source (QueryBranch.bind source "top" saved.previous) cursor saved.previous tail (by intros; rfl)

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Stack.of_before
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.pop_normal
