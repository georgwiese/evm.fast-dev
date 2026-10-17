import InitECandidate.Solver.Input.HeaderProgram

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def firstWord (input : Guest.InputBlob) : BitVec 64 := BitVec.ofNat 64 (Guest.GasLimit.le32 input 2)
def secondWord (input : Guest.InputBlob) : BitVec 64 := BitVec.ofNat 64 (Guest.GasLimit.le32 input 6)
def firstState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {source with memory:=WitnessRadix.StoreWord.put source.memory array (firstWord input)}
def pairState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {firstState source input array with memory:=WitnessRadix.StoreWord.put (firstState source input array).memory (array+8#64) (secondWord input)}

/-- Actual first container-offset stores, including both scalar reads and exact
memory/byte frames. Mapping and separation follow from natural arena geometry. -/
theorem pair_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 10≤input.length%2^64)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+16≤pointer.toNat) :
    evaluateHOLFiniteState source (.seq storeFirst storeSecond)=(none,pairState source input array) ∧
    Blob.HeapInput (pairState source input array) input pointer ∧
    (pairState source input array).memory array=.word (firstWord input) ∧
    (pairState source input array).memory (array+8#64)=.word (secondWord input) ∧
    evaluateHOLFiniteState source storeFirst=(none,firstState source input array) ∧
    evaluateHOLFiniteState (firstState source input array) storeSecond=(none,pairState source input array) ∧
    source.memaddrs array ∧ source.memaddrs (array+8#64) := by
  classical
  have arrayNext : (array+8#64).toNat=array.toNat+8 := by
    rw [BitVec.toNat_add_of_lt (by change array.toNat+8<2^64; omega)]
    rfl
  have firstMapped : source.memaddrs array := by
    rw [domain]
    exact WitnessRadix.BackingLayout.ordinary_mapped array arrayLower (by omega) arrayAligned
  have secondMapped : source.memaddrs (array+8#64) := by
    rw [domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [arrayNext]; omega
    · rw [arrayNext]; omega
    · rw [arrayNext]; omega
  have baseRead : eval source (localVar "p")=some (.val (.word (pointer+2#64))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using pointerLocal
  have arrayRead : eval source offsets=some (.val (.word array)) := by
    simpa [eval,offsets,evalHOLExact,toExact] using arrayGlobal
  obtain ⟨firstRun,firstHeap⟩:=Scalar.store_le32 source input pointer (pointer+2#64) array (localVar "p") offsets [] 2 heap
    (by omega) baseRead (by simp) arrayRead firstMapped pointerAligned (by omega) (Or.inl (by omega))
  have secondBase : eval (firstState source input array) (localVar "p")=some (.val (.word (pointer+2#64))) := by
    simpa [eval,localVar,evalHOLExact,toExact,firstState] using pointerLocal
  have secondArray : eval (firstState source input array) offsets=some (.val (.word array)) := by
    simpa [eval,offsets,evalHOLExact,toExact,firstState] using arrayGlobal
  have destinationRead:=Scalar.plus_read (firstState source input array) offsets array 8 secondArray
  obtain ⟨secondRun,secondHeap⟩:=Scalar.store_le32 (firstState source input array) input pointer (pointer+2#64) (array+8#64)
    (localVar "p") (Scalar.plus offsets 8) [4] 6 firstHeap (by omega) secondBase
    (by simp [BitVec.add_assoc]) destinationRead secondMapped pointerAligned (by omega) (Or.inl (by rw [arrayNext]; omega))
  have first : evaluateHOLFiniteState source storeFirst=(none,firstState source input array) := firstRun
  have second : evaluateHOLFiniteState (firstState source input array) storeSecond=(none,pairState source input array) := secondRun
  have different : array+8#64≠array := by
    intro equal
    have number:=congrArg BitVec.toNat equal
    rw [arrayNext] at number
    omega
  refine ⟨?_,secondHeap,?_,?_,first,second,firstMapped,secondMapped⟩
  · rw [WitnessRadix.StateSteps.next_sequence source (firstState source input array) _ _ first (Nat.le_refl _)]
    exact second
  · simp [pairState,firstState,WitnessRadix.StoreWord.put,Ne.symm different]
  · simp [pairState,WitnessRadix.StoreWord.put]

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.pair_execute
