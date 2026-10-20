import InitECandidate.Solver.Input.RlpWrite.U256Store
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input.InitializerQuads
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
abbrev Words := RlpWrite.U256Value.Words

def expression (words : Words) : ExpHOL 64 := .rstruct [.const (words 0),.const (words 1),.const (words 2),.const (words 3)]
def address (name : String) (offset : Nat) : ExpHOL 64 :=
  if offset = 0 then .var .global (ofString name) else .op .add [.var .global (ofString name),.const (BitVec.ofNat 64 offset)]
def stores (name : String) : Nat → List Words → ProgHOL 64 → ProgHOL 64
  | _,[],tail => tail
  | offset,words :: rest,tail => .seq (.store (address name offset) (expression words)) (stores name (offset + 32) rest tail)
def writes (pointer : BitVec 64) : Nat → List Words → List (BitVec 64 × BitVec 64)
  | _,[] => []
  | offset,words :: rest => RlpWrite.U256Value.wordWrites (pointer + BitVec.ofNat 64 offset) words ++ writes pointer (offset + 32) rest
def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List Words) :=
  {source with memory := WordWrites.write source.memory (writes pointer offset words)}

private theorem write_append (memory : WordWrites.Memory) (first second : List (BitVec 64 × BitVec 64)) :
    WordWrites.write memory (first ++ second) = WordWrites.write (WordWrites.write memory first) second := by
  induction first generalizing memory with
  | nil => rfl
  | cons item rest ih => exact ih (StoreWord.put memory item.1 item.2)

private theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64) (offset : Nat)
    (binding : source.globals.lookup (ofString name) = some (.val (.word pointer))) :
    QueryBranch.eval source (address name offset) = some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
  by_cases zero : offset = 0
  · subst offset
    simpa [address,QueryBranch.eval,evalHOLExact,toExact] using binding
  · simp [address,zero,QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- The original literal tuple stores execute at their real mapped addresses,
retaining their complete memory effect and resuming the actual suffix. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (offset extent : Nat) (words : List Words) (tail : ProgHOL 64)
    (binding : source.globals.lookup (ofString name) = some (.val (.word pointer)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer extent)
    (pointerAligned : pointer.toNat % 8 = 0) (offsetAligned : offset % 8 = 0) (inside : offset + 32 * words.length ≤ extent) :
    evaluateHOLFiniteState source (stores name offset words tail) = evaluateHOLFiniteState (written source pointer offset words) tail := by
  induction words generalizing source offset with
  | nil => rfl
  | cons words rest ih =>
    have mapped (index : Fin 4) : source.memaddrs (pointer + BitVec.ofNat 64 offset + BitVec.ofNat 64 (8 * index.val)) := by
      have current := AllocatedBytes.word_mapped source pointer extent (offset + 8 * index.val) domain arena (by simp only [List.length_cons] at inside; omega) pointerAligned (by omega)
      simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using current
    have firstRun := RlpWrite.U256Value.store_execute source (address name offset) (expression words) (pointer + BitVec.ofNat 64 offset) words
      (address_read source name pointer offset binding) rfl mapped
    let middle := {source with memory := WordWrites.write source.memory (RlpWrite.U256Value.wordWrites (pointer + BitVec.ofNat 64 offset) words)}
    rw [stores,StateSteps.next_sequence source middle _ _ firstRun (Nat.le_refl _)]
    have following := ih middle (offset + 32) binding domain (by omega) (by simp only [List.length_cons] at inside; omega)
    simpa only [written,writes,write_append,middle] using following

theorem written_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List Words) (clock : Nat) :
    written {source with clock := clock} pointer offset words = {written source pointer offset words with clock := clock} := rfl

theorem written_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List Words) :
    InitializerAllocations.context (written source pointer offset words) = InitializerAllocations.context source :=
  InitializerAllocations.context_memory source _

end InitECandidate.Solver.Input.InitializerQuads

#print axioms InitECandidate.Solver.Input.InitializerQuads.execute
#print axioms InitECandidate.Solver.Input.InitializerQuads.written_clock
#print axioms InitECandidate.Solver.Input.InitializerQuads.written_context
