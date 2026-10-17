import InitECandidate.Solver.Input.VarList.StepStores

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete actual valid per-record step: the real guard, optional previous
length store, current pointer store and both assignments. It costs no body
clocks and preserves all copied input bytes, even at clock zero. -/
theorem valid_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (small : index<plan.count) (current previous first total : BitVec 64)
    (heap : Blob.HeapInput source input plan.inputPointer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word plan.array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (o : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (p : source.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))))
    (previousLocal : source.locals.lookup (ofString "prev")=some (.val (.word previous)))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (valid : ¬badRecord current first total previous) :
    evaluateHOLFiniteState source step=(none,stepState source input plan index current previous) ∧
      Blob.HeapInput (stepState source input plan index current previous) input plan.inputPointer := by
  classical
  have test:=record_test_read source current first total previous o f n previousLocal
  simp only [if_neg valid,eval] at test
  have guarded : evaluateHOLFiniteState source recordGuard=(none,source) := by
    rw [recordGuard,evaluateHOLFiniteState_ite,test]
    simp
  obtain ⟨priorRun,priorHeap⟩:=prior_store source input plan index small current previous heap domain a i o previousLocal
  obtain ⟨pointerRun,pointerHeap⟩:=pointer_store source input plan index small current previous priorHeap domain a i o p
  have updates:=step_updates source input plan index current previous i o previousLocal
  refine ⟨?_,?_⟩
  · rw [step,WitnessRadix.StateSteps.next_sequence source source recordGuard _ guarded (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence source (priorState source plan.array index current previous) priorLengthStore _ priorRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence (priorState source plan.array index current previous) (pointerState source input plan index current previous)
        rowPointerStore _ pointerRun (Nat.le_refl _)]
    exact updates
  · exact Blob.HeapInput.of_fields (pointerState source input plan index current previous) (stepState source input plan index current previous)
      input plan.inputPointer rfl rfl rfl pointerHeap

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.valid_step
