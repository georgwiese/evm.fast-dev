import InitECandidate.Solver.Input.PayloadWordStore
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.StructureStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

def stored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (offset : Nat) (value : BitVec 64) :=
  {source with memory := StoreWord.put source.memory (byteAddress base offset) value}

/-- An actual scalar field store into a naturally allocated structure. The
real mapping and separation prove the execution and copied-input frame;
all other words, globals, FFI state and source clock remain unchanged. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer base : BitVec 64)
    (size offset : Nat) (baseName : String) (expression : ExpHOL 64) (value : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (binding : source.locals.lookup (ofString baseName) = some (.val (.word base)))
    (read : eval source expression = some (.val (.word value)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : Arena base size)
    (pointerAligned : pointer.toNat % 8 = 0) (baseAligned : base.toNat % 8 = 0)
    (inside : offset + 8 ≤ size) (offsetAligned : offset % 8 = 0)
    (afterInput : pointer.toNat + input.length % 2^64 + 8 ≤ base.toNat) :
    evaluateHOLFiniteState source (.store (Scalar.plus (localVar baseName) offset) expression) = (none,stored source base offset value) ∧
      Blob.HeapInput (stored source base offset value) input pointer ∧
      (stored source base offset value).memory (byteAddress base offset) = .word value ∧
      (∀ query,query ≠ byteAddress base offset → (stored source base offset value).memory query = source.memory query) := by
  have upper := arena.upper
  have number := byteAddress_toNat base offset (by omega)
  have address := Scalar.plus_read source (localVar baseName) base offset (Request.local_word source baseName base binding)
  refine ⟨StoreWord.execute source _ _ _ _ address read (word_mapped source base size offset domain arena (by omega) baseAligned offsetAligned),?_,?_,?_⟩
  · exact Blob.HeapInput.store_separate source input pointer _ _ heap pointerAligned (by omega) (Or.inr (by rw [number]; omega))
  · simp [stored,StoreWord.put]
  · intro query different
    simp [stored,StoreWord.put,different]

end InitECandidate.Solver.Input.StructureStore

#print axioms InitECandidate.Solver.Input.StructureStore.execute
