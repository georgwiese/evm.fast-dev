import InitECandidate.Solver.Input.InputImageFrame
import InitECandidate.Solver.Input.CurrentStartup.AllocationFrontier
import InitECandidate.Solver.Input.CurrentStartup.CanonicalHeader
import InitECandidate.Solver.Input.RequestProgram

namespace InitECandidate.Solver.Input.CurrentStartup.RequestCut
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def actions : List CallPrefix.Action :=
  [.declare (ofString "o_npr") .one (.load .one Header.offsets),
   .declare (ofString "o_wit") .one (.load .one (Scalar.plus Header.offsets 8)),
   .scoped (ofString "si") .one (Code.name .alloc) [.const 96#64],
   .command Request.chainStore,
   .declare (ofString "np") .one Request.pointerExpression,
   .declare (ofString "nlen") .one Request.lengthExpression]

def tail : ProgHOL 64 := .seq Request.lengthGuard Request.requestBody

theorem source_shape : Header.continuation = CallPrefix.program actions tail := by
  simpa only [Request.prefixBody, actions, tail, CallPrefix.program, Code.name] using Request.prefix_shape

theorem actions_safe : actions.all (fun action => action.keeps (ofString "unused")) = true := by decide

theorem actions_heap (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Preserves code (CallPrefix.program actions .skip) := by
  simp only [actions, CallPrefix.program]
  refine NormalHeapEffects.declared code _ _ _ _ (NormalHeapEffects.declared code _ _ _ _ ?_)
  refine NormalHeapEffects.scoped_body code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) ?_
  exact NormalHeapEffects.sequence code _ _ (NormalHeapEffects.store code _ _)
    (NormalHeapEffects.declared code _ _ _ _ (NormalHeapEffects.declared code _ _ _ _ (NormalHeapEffects.skip code)))

/-- Genuine decoder return exposes the live six lexical actions through its
record store, retaining both the original observation and lower heap frontier. -/
theorem reached (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower : Nat)
    (installed : OriginalCode.Installed source.code) (heap : NormalHeapEffects.AtLeast lower source)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source Header.continuation = (some (.returned value), post)) :
    ∃ current inner, CallPrefix.Execution source actions current ∧ NormalHeapEffects.AtLeast lower current ∧
      evaluateHOLFiniteState current tail = (some (.returned value), inner) ∧
      post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner := by
  rw [source_shape] at actual
  have never : NoReturn.Never (CallPrefix.program actions .skip) := @CallPrefix.kept_never actions (ofString "unused") (by
    intro action member
    exact List.all_eq_true.mp actions_safe action member)
  obtain ⟨current, inner, execution, remaining, clock, frame⟩ := CallPrefix.normal_frame_trace source post actions tail value never actual
  exact ⟨current, inner, execution, NormalHeapEffects.execution execution (actions_heap source.code installed) lower heap, remaining, clock, frame⟩

/-- The observed six-action trace allocates the current frontier as its
record pointer, with derived room. This is the real si binding after the store. -/
theorem record_pointer {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (lower : Nat)
    (installed : OriginalCode.Installed source.code) (heap : NormalHeapEffects.AtLeast lower source)
    (actual : CallPrefix.Execution source actions target) :
    ∃ pointer : BitVec 64, lower ≤ pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
      pointer.toNat + 96 ≤ 2952790016 ∧ target.locals.lookup (ofString "si") = some (.val (.word pointer)) := by
  cases actual with
  | @step _ firstState _ _ _ first rest =>
    cases rest with
    | @step _ loadedState _ _ _ second rest =>
      cases rest with
      | @step _ allocatedState _ _ _ allocated rest =>
        have firstHeap := NormalHeapEffects.execution (.step first (.done _))
          (NormalHeapEffects.declared source.code _ _ _ _ (NormalHeapEffects.skip source.code)) lower heap
        have secondHeap := NormalHeapEffects.execution (.step second (.done _))
          (NormalHeapEffects.declared firstState.code _ _ _ _ (NormalHeapEffects.skip firstState.code)) lower firstHeap
        have sameCode := second.runtime.2.2.2.1.trans first.runtime.2.2.2.1
        have currentInstalled : OriginalCode.Installed loadedState.code := by rw [sameCode]; exact installed
        obtain ⟨pointer, heapCell, low, aligned, room, stateEq⟩ := allocation_frontier (ofString "si") 96#64 lower currentInstalled secondHeap allocated
        have binding : allocatedState.locals.lookup (ofString "si") = some (.val (.word pointer)) := by
          rw [stateEq]
          simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
        have kept := rest.keeps (ofString "si") (by
          intro action member
          simp only [actions, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> decide)
        exact ⟨pointer, low, aligned, room, kept.trans binding⟩

/-- Copied bytes survive the real record allocation/store and local setup.
The record destination is separated by the incoming derived heap frontier. -/
theorem input_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (input : Guest.InputBlob) (pointer : BitVec 64) (installed : OriginalCode.Installed source.code)
    (heap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) source)
    (image : Blob.HeapInput source input pointer) (aligned : pointer.toNat % 8 = 0)
    (room : pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016)
    (actual : CallPrefix.Execution source actions target) : Blob.HeapInput target input pointer := by
  cases actual with
  | @step _ firstState _ _ _ first rest =>
    cases rest with
    | @step _ loadedState _ _ _ second rest =>
      cases rest with
      | @step _ allocatedState _ _ _ allocated rest =>
        have firstHeap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) firstState := by cases first; exact heap
        have secondHeap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) loadedState := by cases second; exact firstHeap
        have firstBytes : Blob.HeapInput firstState input pointer := by cases first; exact image
        have secondBytes : Blob.HeapInput loadedState input pointer := by cases second; exact firstBytes
        have sameCode := second.runtime.2.2.2.1.trans first.runtime.2.2.2.1
        have currentInstalled : OriginalCode.Installed loadedState.code := by rw [sameCode]; exact installed
        obtain ⟨record, cell, low, recordAligned, recordRoom, stateEq⟩ := allocation_frontier (ofString "si") 96#64 _ currentInstalled secondHeap allocated
        have allocatedBytes : Blob.HeapInput allocatedState input pointer := Blob.HeapInput.of_fields loadedState allocatedState input pointer
          (by rw [stateEq]; rfl) (by rw [stateEq]; rfl) (by rw [stateEq]; rfl) secondBytes
        have binding : allocatedState.locals.lookup (ofString "si") = some (.val (.word record)) := by
          rw [stateEq]
          simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
        cases rest with
        | @step _ chainedState _ _ _ chain remainder =>
          have storeNormal : evaluateHOLFiniteState allocatedState Request.chainStore = (none, chainedState) := by cases chain; assumption
          have read : WitnessRadix.QueryBranch.eval allocatedState (WitnessRadix.QueryBranch.localVar "si") = some (.val (.word record)) := by
            simpa [WitnessRadix.QueryBranch.eval, WitnessRadix.QueryBranch.localVar, evalHOLExact, toExact] using binding
          have addressRead := Scalar.plus_read allocatedState (WitnessRadix.QueryBranch.localVar "si") record 88 read
          have addressNumber : (record + 88#64).toNat = record.toNat + 88 := by
            rw [BitVec.toNat_add_of_lt (by change record.toNat + 88 < 2^64; change record.toNat + 96 ≤ 2952790016 at recordRoom; omega)]
            rfl
          have chainedBytes : Blob.HeapInput chainedState input pointer := Blob.HeapInput.op_store_separate allocatedState chainedState input pointer
            (record + 88#64) (Scalar.plus (WitnessRadix.QueryBranch.localVar "si") 88) .or _ allocatedBytes aligned (by omega)
            (Or.inr (by rw [addressNumber]; omega)) addressRead storeNormal
          cases remainder with
          | step np last =>
            cases last with
            | step nlen done =>
              cases done
              cases nlen
              cases np
              exact chainedBytes

end InitECandidate.Solver.Input.CurrentStartup.RequestCut

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCut.source_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCut.actions_safe
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCut.actions_heap
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCut.reached
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCut.record_pointer

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCut.input_frame
