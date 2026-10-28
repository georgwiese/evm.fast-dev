import InitECandidate.Solver.Headers.CurrentValidate.Transport
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def storedHeader (source : PanSemStateFiniteExact 64 Guest.HostMemory) (hs header : BitVec 64) (index : Nat) :=
  {source with memory:=StoreWord.put source.memory (byteAddress hs (8*index)) header}

/-- The real scalar header-pointer store is mapped by the actual hs array.
Its exact memory update preserves all original input rows and loop context. -/
theorem store_header (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count) (header : BitVec 64)
    (headerLocal : source.locals.lookup (ofString "h")=some (.val (.word header))) :
    evaluateHOLFiniteState source (.store headerCell (localVar "h"))=(none,storedHeader source data.hs header index) ∧
      RoundState data origin (storedHeader source data.hs header index) index ∧
      (storedHeader source data.hs header index).memory (byteAddress data.hs (8*index))=.word header := by
  have destination : eval source headerCell=some (.val (.word (byteAddress data.hs (8*index)))) := by
    simp [headerCell,localVar,eval,evalHOLExact,evalListHOLExact,toExact,state.hsCell,state.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      byteAddress,BitVec.ofNat_mul,Nat.mul_comm]
  have value : eval source (localVar "h")=some (.val (.word header)) := by simp [eval,evalHOLExact,localVar,toExact,headerLocal]
  have mapped:=AllocatedBytes.word_mapped source data.hs (8*data.count+8) (8*index) state.arena.domain layout.hs (by omega) layout.hsAligned (by omega)
  have actual:=StoreWord.execute source headerCell (localVar "h") (byteAddress data.hs (8*index)) header destination value mapped
  have addressNumber : (byteAddress data.hs (8*index)).toNat=data.hs.toNat+8*index :=
    MemoryBytes.offset_toNat data.hs (8*index) (by have h:=layout.hs.upper; omega)
  have frame : Input.HashInput.Frame source (storedHeader source data.hs header index) data.lower data.upper := by
    refine ⟨?_⟩
    intro query lower upper
    change StoreWord.put source.memory (byteAddress data.hs (8*index)) header query=source.memory query
    apply if_neg
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [addressNumber] at equal
    have before:=layout.inputBefore
    omega
  exact ⟨actual,state.transport data origin source _ index rfl rfl (fun _=>rfl) (fun _=>rfl) frame,by simp [storedHeader,StoreWord.put]⟩

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.store_header
