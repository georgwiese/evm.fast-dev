import InitECandidate.Solver.WitnessRadix.Keccak256AfterProgram

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def outMemory (memory : WordWrites.Memory) (stp out : BitVec 64) (offset : Nat) : WordWrites.Memory :=
  StoreWord.put memory (byteAddress out offset) (MemoryBytes.wordBits (memory (byteAddress stp offset)))
def outMemoryMany (memory : WordWrites.Memory) (stp out : BitVec 64) : List Nat → WordWrites.Memory
  | [] => memory
  | offset::rest => outMemoryMany (outMemory memory stp out offset) stp out rest
def outStores : List Nat → ProgHOL 64 → ProgHOL 64
  | [],tail => tail
  | offset::rest,tail => .seq (outStore offset) (outStores rest tail)

theorem out_address_read {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (pointer : BitVec 64) (offset : Nat)
    (localFact : source.locals.lookup (ofString name)=some (.val (.word pointer))) :
    eval source (outAddress name offset)=some (.val (.word (byteAddress pointer offset))) := by
  by_cases zero : offset=0
  · subst offset
    simpa [eval,outAddress,localVar,evalHOLExact,toExact,byteAddress] using localFact
  · simp [eval,outAddress,zero,localVar,addConst,evalHOLExact,evalListHOLExact,toExact,localFact,
      valueIsWord,valueWord,wordOpHOL,wordOp,byteAddress]

theorem out_store_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (stp out : BitVec 64) (offset : Nat)
    (stpLocal : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (stateMapped : source.memaddrs (byteAddress stp offset)) (outputMapped : source.memaddrs (byteAddress out offset)) :
    evaluateHOLFiniteState source (outStore offset)=(none,{source with memory := outMemory source.memory stp out offset}) := by
  have stpRead := out_address_read source "stp" stp offset stpLocal
  have outRead := out_address_read source "out" out offset outLocal
  have valueRead : eval source (.load .one (outAddress "stp" offset))=some (.val (.word (MemoryBytes.wordBits (source.memory (byteAddress stp offset))))) := by
    simp only [eval] at stpRead ⊢
    cases cell : source.memory (byteAddress stp offset) with
    | word value => simp [evalHOLExact,stpRead,memLoadHOLExact,stateMapped,cell,MemoryBytes.wordBits]
  exact StoreWord.execute source _ _ _ _ outRead valueRead outputMapped

theorem out_stores_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (stp out : BitVec 64) (offsets : List Nat) (tail : ProgHOL 64)
    (stpLocal : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (stateMapped : ∀ offset∈offsets,source.memaddrs (byteAddress stp offset))
    (outputMapped : ∀ offset∈offsets,source.memaddrs (byteAddress out offset)) :
    evaluateHOLFiniteState source (outStores offsets tail)=evaluateHOLFiniteState {source with memory := outMemoryMany source.memory stp out offsets} tail := by
  induction offsets generalizing source with
  | nil => rfl
  | cons offset rest ih =>
    rw [outStores,StateSteps.next_sequence source {source with memory := outMemory source.memory stp out offset} _ _
      (out_store_execute source stp out offset stpLocal outLocal (stateMapped offset (by simp)) (outputMapped offset (by simp))) (Nat.le_refl _)]
    exact ih _ stpLocal outLocal
      (by intro offset member; exact stateMapped offset (List.mem_cons_of_mem _ member))
      (by intro offset member; exact outputMapped offset (List.mem_cons_of_mem _ member))

theorem out_words_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (stp out : BitVec 64)
    (stpLocal : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (stateMapped : ∀ offset<32,offset%8=0 → source.memaddrs (byteAddress stp offset))
    (outputMapped : ∀ offset<32,offset%8=0 → source.memaddrs (byteAddress out offset)) :
    evaluateHOLFiniteState source outWords=(none,{source with memory := outMemoryMany source.memory stp out [0,8,16,24]}) := by
  change evaluateHOLFiniteState source (outStores [0,8,16] (outStore 24))=_
  rw [out_stores_execute source stp out [0,8,16] _ stpLocal outLocal
    (by intro offset member; simp at member; rcases member with rfl|rfl|rfl <;> exact stateMapped _ (by decide) (by decide))
    (by intro offset member; simp at member; rcases member with rfl|rfl|rfl <;> exact outputMapped _ (by decide) (by decide))]
  exact out_store_execute _ stp out 24 stpLocal outLocal (stateMapped _ (by decide) (by decide)) (outputMapped _ (by decide) (by decide))

theorem out_memory_away (memory : WordWrites.Memory) (stp out query : BitVec 64) (offsets : List Nat)
    (away : ∀ offset∈offsets,query≠byteAddress out offset) : outMemoryMany memory stp out offsets query=memory query := by
  induction offsets generalizing memory with
  | nil => rfl
  | cons offset rest ih =>
    rw [outMemoryMany,ih _ (by intro offset member; exact away offset (List.mem_cons_of_mem _ member))]
    exact if_neg (away offset (by simp))

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.out_address_read
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.out_store_execute
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.out_stores_execute
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.out_words_execute
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.out_memory_away
