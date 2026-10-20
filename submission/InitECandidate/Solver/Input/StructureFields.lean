import InitECandidate.Solver.Input.StructureStore
import InitECandidate.Solver.Input.PayloadFields

namespace InitECandidate.Solver.Input.StructureStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

abbrev Field := Payload.Field

def fieldProgram (baseName : String) : List Field → ProgHOL 64
  | [] => .return (localVar baseName)
  | field :: rest => .seq (.store (Scalar.plus (localVar baseName) field.1) field.2.1) (fieldProgram baseName rest)

/-- Execute actual scalar structure fields and return their allocated base.
All reads are justified at the current intermediate memory; input bytes and
all non-memory fields are retained by the exact final state. -/
theorem fields_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor : BitVec 64)
    (size : Nat) (baseName : String) (heap : Blob.HeapInput source input pointer)
    (binding : source.locals.lookup (ofString baseName) = some (.val (.word cursor)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : Arena cursor size)
    (pointerAligned : pointer.toNat % 8 = 0) (cursorAligned : cursor.toNat % 8 = 0)
    (afterInput : pointer.toNat + input.length % 2^64 + 8 ≤ cursor.toNat)
    (fields : List Field) (valid : ∀ field ∈ fields,field.1 + 8 ≤ size ∧ field.1 % 8 = 0)
    (reads : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.locals = source.locals → Blob.HeapInput current input pointer →
      ∀ field ∈ fields,eval current field.2.1 = some (.val (.word field.2.2))) :
    evaluateHOLFiniteState source (fieldProgram baseName fields) =
      (some (.returned (.val (.word cursor))),emptyLocalsHOLFinite (Payload.applyFields source cursor fields)) ∧
      Blob.HeapInput (Payload.applyFields source cursor fields) input pointer := by
  induction fields generalizing source with
  | nil =>
    refine ⟨?_,heap⟩
    simp [fieldProgram,Payload.applyFields,Payload.fieldMemory,evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,binding,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  | cons field rest ih =>
    have firstValid := valid field (by simp)
    obtain ⟨firstRun,firstHeap,firstCell,firstFrame⟩ := execute source input pointer cursor size field.1 baseName field.2.1 field.2.2 heap binding
      (reads source rfl heap field (by simp)) domain arena pointerAligned cursorAligned firstValid.1 firstValid.2 afterInput
    let first := stored source cursor field.1 field.2.2
    have restValid : ∀ entry ∈ rest,entry.1 + 8 ≤ size ∧ entry.1 % 8 = 0 := fun entry member => valid entry (by simp [member])
    have restReads : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.locals = first.locals → Blob.HeapInput current input pointer →
        ∀ entry ∈ rest,eval current entry.2.1 = some (.val (.word entry.2.2)) := by
      intro current locals currentHeap entry member
      exact reads current locals currentHeap entry (by simp [member])
    obtain ⟨tailRun,tailHeap⟩ := ih first firstHeap binding domain restValid restReads
    refine ⟨?_,tailHeap⟩
    rw [fieldProgram,StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _)]
    exact tailRun

end InitECandidate.Solver.Input.StructureStore

#print axioms InitECandidate.Solver.Input.StructureStore.fields_execute
