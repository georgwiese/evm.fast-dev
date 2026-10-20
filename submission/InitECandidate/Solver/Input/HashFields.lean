import InitECandidate.Solver.Input.MainHashesTrace
import InitECandidate.Solver.Input.StructureStore

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

def hashPointerStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 8) (.op .add [localVar "np",localVar "o_vh"])
def hashCountStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 16) (localVar "nvh")
def parentRootStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 24) (Scalar.plus (localVar "np") 8)
def requestsCall : ProgHOL 64 := match afterHashes with | .seq _ (.seq _ (.seq _ rest)) => rest | _ => .skip

theorem hash_fields_shape : afterHashes = .seq hashPointerStore (.seq hashCountStore (.seq parentRootStore requestsCall)) := by
  simp only [requestsCall,afterHashes,hashesCall,afterPayload,continuation,requestBody,prefixBody,Header.continuation,Header.afterHeader,Header.body,
    Guest.guestFn_decode_stateless_input,progToHOL,shapeToHOL,Option.map_none,hashPointerStore,hashCountStore,parentRootStore,
    Scalar.plus,localVar,expToHOL,List.map_cons,List.map_nil]

def hashFieldsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si np hashes count : BitVec 64) :=
  StructureStore.stored (StructureStore.stored (StructureStore.stored source si 8 (np + hashes)) si 16 count) si 24 (np + 8#64)

/-- The three original SI hash/parent-root stores and the next real request
call, retaining any later result. Only the allocated SI fields are written. -/
theorem hash_fields_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer si np hashes count : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (siLocal : source.locals.lookup (ofString "si") = some (.val (.word si)))
    (npLocal : source.locals.lookup (ofString "np") = some (.val (.word np)))
    (hashLocal : source.locals.lookup (ofString "o_vh") = some (.val (.word hashes)))
    (countLocal : source.locals.lookup (ofString "nvh") = some (.val (.word count)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : Arena si 96)
    (pointerAligned : pointer.toNat % 8 = 0) (siAligned : si.toNat % 8 = 0)
    (afterInput : pointer.toNat + input.length % 2^64 + 8 ≤ si.toNat) :
    evaluateHOLFiniteState source afterHashes = evaluateHOLFiniteState (hashFieldsStored source si np hashes count) requestsCall ∧
      Blob.HeapInput (hashFieldsStored source si np hashes count) input pointer ∧
      (∀ query,query ≠ byteAddress si 8 → query ≠ byteAddress si 16 → query ≠ byteAddress si 24 →
        (hashFieldsStored source si np hashes count).memory query = source.memory query) := by
  have firstRead : eval source (.op .add [localVar "np",localVar "o_vh"]) = some (.val (.word (np + hashes))) := by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,npLocal,hashLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨firstRun,firstHeap,firstCell,firstFrame⟩ := StructureStore.execute source input pointer si 96 8 "si" _ (np + hashes) heap siLocal firstRead domain arena pointerAligned siAligned (by decide) (by decide) afterInput
  let first := StructureStore.stored source si 8 (np + hashes)
  have secondRead : eval first (localVar "nvh") = some (.val (.word count)) := local_word first "nvh" count countLocal
  obtain ⟨secondRun,secondHeap,secondCell,secondFrame⟩ := StructureStore.execute first input pointer si 96 16 "si" _ count firstHeap siLocal secondRead domain arena pointerAligned siAligned (by decide) (by decide) afterInput
  let second := StructureStore.stored first si 16 count
  have thirdRead : eval second (Scalar.plus (localVar "np") 8) = some (.val (.word (np + 8#64))) :=
    Scalar.plus_read second (localVar "np") np 8 (local_word second "np" np npLocal)
  obtain ⟨thirdRun,thirdHeap,thirdCell,thirdFrame⟩ := StructureStore.execute second input pointer si 96 24 "si" _ (np + 8#64) secondHeap siLocal thirdRead domain arena pointerAligned siAligned (by decide) (by decide) afterInput
  refine ⟨?_,thirdHeap,?_⟩
  · rw [hash_fields_shape,hashPointerStore,hashCountStore,parentRootStore,
      StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
      StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
      StateSteps.next_sequence second (hashFieldsStored source si np hashes count) _ _ thirdRun (Nat.le_refl _)]
  · intro query firstAway secondAway thirdAway
    exact (thirdFrame query thirdAway).trans ((secondFrame query secondAway).trans (firstFrame query firstAway))

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.hash_fields_shape
#print axioms InitECandidate.Solver.Input.Request.hash_fields_execute
