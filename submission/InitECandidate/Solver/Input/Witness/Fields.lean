import InitECandidate.Solver.Input.Witness.Program
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.Input.VarList.RecordsFrame

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

def pairStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64) (offset : Nat)
    (array count : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  {source with memory:=StoreWord.put (StoreWord.put source.memory (byteAddress si offset) array) (byteAddress si (offset+8)) count}

/-- Actual tuple field stores into the allocated 96-byte stateless input.
The stores pay no source clock and preserve every other word. -/
theorem pair_stores (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si array count : BitVec 64)
    (name : String) (offset : Nat) (continuation : ProgHOL 64)
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (tupleLocal : source.locals.lookup (ofString name)=some (VarList.pairValue array count.toNat))
    (domain : source.memaddrs=InitE.ordinaryDomain) (siArena : Arena si 96) (siAligned : si.toNat%8=0)
    (inside : offset+16≤96) (offsetAligned : offset%8=0) :
    evaluateHOLFiniteState source (.seq (pointerStore name offset) (.seq (countStore name offset) continuation))=
      evaluateHOLFiniteState (pairStored source si offset array count) continuation ∧
      (pairStored source si offset array count).memory (byteAddress si offset)=.word array ∧
      (pairStored source si offset array count).memory (byteAddress si (offset+8))=.word count ∧
      (∀ query,query≠byteAddress si offset → query≠byteAddress si (offset+8) →
        (pairStored source si offset array count).memory query=source.memory query) := by
  classical
  let first : PanSemStateFiniteExact 64 Guest.HostMemory:=
    {source with memory:=StoreWord.put source.memory (byteAddress si offset) array}
  have firstRead : eval source (.rfield 0 (localVar name))=some (.val (.word array)) := by
    simp [eval,localVar,VarList.pairValue,evalHOLExact,toExact,tupleLocal]
  have secondRead : eval first (.rfield 1 (localVar name))=some (.val (.word count)) := by
    have saved : first.locals.lookup (ofString name)=some (VarList.pairValue array count.toNat):=tupleLocal
    simp [eval,localVar,VarList.pairValue,evalHOLExact,toExact,saved,BitVec.setWidth_eq]
  have firstAddress : eval source (Scalar.plus (localVar "si") offset)=some (.val (.word (byteAddress si offset))) :=
    Scalar.plus_read source (localVar "si") si offset (Request.local_word source "si" si siLocal)
  have secondAddress : eval first (Scalar.plus (localVar "si") (offset+8))=some (.val (.word (byteAddress si (offset+8)))) :=
    Scalar.plus_read first (localVar "si") si (offset+8) (Request.local_word first "si" si siLocal)
  have firstRun:=StoreWord.execute source _ _ _ array firstAddress firstRead
    (word_mapped source si 96 offset domain siArena (by omega) siAligned offsetAligned)
  have secondRun:=StoreWord.execute first _ _ _ count secondAddress secondRead
    (word_mapped first si 96 (offset+8) domain siArena (by omega) siAligned (by omega))
  have different : byteAddress si offset≠byteAddress si (offset+8):=
    byteAddress_ne si offset (offset+8) (by have:=siArena.upper;omega) (by have:=siArena.upper;omega) (by omega)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [pointerStore,countStore]
    rw [StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
      StateSteps.next_sequence first (pairStored source si offset array count) _ _ secondRun (Nat.le_refl _)]
  · simp [pairStored,StoreWord.put,different]
  · simp [pairStored,StoreWord.put]
  · intro query firstAway secondAway
    simp [pairStored,StoreWord.put,firstAway,secondAway]

/-- Input-structure stores are earlier than every decoded record-array cell. -/
theorem records_after_pair_stores (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer records si storedArray storedCount : BitVec 64) (start length offset : Nat)
    (decoded : VarList.Records source input pointer records start length)
    (siArena : Arena si 96) (inside : offset+16≤96) (before : si.toNat+96≤records.toNat) :
    VarList.Records (pairStored source si offset storedArray storedCount) input pointer records start length := by
  classical
  by_cases empty : length=0
  · exact Or.inl empty
  · rcases decoded with impossible|⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩
    · exact False.elim (empty impossible)
    · have decoded : VarList.Records source input pointer records start length:=
        Or.inr ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩
      have countValue : VarList.decodedCount input start length=plan.count := by
        simp only [VarList.decodedCount,if_neg empty];exact countEq.symm
      apply VarList.Records.of_cells source _ input pointer records start length decoded
      intro index indexInside
      have indexBound : index<plan.count := by rw [←countValue];exact indexInside
      have rowNat:=plan.row_nat index indexBound
      have lengthNat:=plan.length_nat index indexBound
      rw [arrayEq] at rowNat lengthNat
      have firstNat:=byteAddress_toNat si offset (by have:=siArena.upper;omega)
      have secondNat:=byteAddress_toNat si (offset+8) (by have:=siArena.upper;omega)
      have frame (query : BitVec 64) (lower : records.toNat≤query.toNat) :
          (pairStored source si offset storedArray storedCount).memory query=source.memory query := by
        have firstAway : query≠byteAddress si offset := by intro equal;have:=congrArg BitVec.toNat equal;omega
        have secondAway : query≠byteAddress si (offset+8) := by intro equal;have:=congrArg BitVec.toNat equal;omega
        simp [pairStored,StoreWord.put,firstAway,secondAway]
      simp only [VarList.decodedArray,if_neg empty]
      exact ⟨frame _ (by rw [rowNat];omega),frame _ (by rw [lengthNat];omega)⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.pair_stores
#print axioms InitECandidate.Solver.Input.Witness.records_after_pair_stores
