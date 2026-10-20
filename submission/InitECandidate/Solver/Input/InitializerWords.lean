import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.WitnessRadix.WordWrites
import InitECandidate.Solver.WitnessRadix.StateSteps
import InitECandidate.Solver.Rlp.SliceArrayModel

namespace InitECandidate.Solver.Input.InitializerWords
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def stores (name : String) : Nat → List (BitVec 64) → ProgHOL 64 → ProgHOL 64
  | _,[],tail => tail
  | offset,word :: rest,tail => .seq (.store (.op .add [.var .global (ofString name),.const (BitVec.ofNat 64 offset)]) (.const word)) (stores name (offset + 8) rest tail)
def writes (pointer : BitVec 64) : Nat → List (BitVec 64) → List (BitVec 64 × BitVec 64)
  | _,[] => []
  | offset,word :: rest => (pointer + BitVec.ofNat 64 offset,word) :: writes pointer (offset + 8) rest
def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List (BitVec 64)) :=
  {source with memory := WordWrites.write source.memory (writes pointer offset words)}

/-- Fixed literal word stores execute at their actual mapped destinations.
Their source clock is unchanged; the straight-line stores remain in the AST. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer : BitVec 64)
    (offset extent : Nat) (words : List (BitVec 64)) (tail : ProgHOL 64)
    (binding : source.globals.lookup (ofString name) = some (.val (.word pointer)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer extent)
    (pointerAligned : pointer.toNat % 8 = 0) (offsetAligned : offset % 8 = 0)
    (inside : offset + 8 * words.length ≤ extent) :
    evaluateHOLFiniteState source (stores name offset words tail) = evaluateHOLFiniteState (written source pointer offset words) tail := by
  induction words generalizing source offset with
  | nil => rfl
  | cons word rest ih =>
    have destination : eval source (.op .add [.var .global (ofString name),.const (BitVec.ofNat 64 offset)]) = some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp]
    have available : offset + 8 * (rest.length + 1) ≤ extent := inside
    have mapped := AllocatedBytes.word_mapped source pointer extent offset domain arena (by omega) pointerAligned offsetAligned
    have firstRun := StoreWord.execute source _ (.const word) _ word destination rfl mapped
    let middle := {source with memory := StoreWord.put source.memory (pointer + BitVec.ofNat 64 offset) word}
    rw [stores,StateSteps.next_sequence source middle _ _ firstRun (Nat.le_refl _)]
    have next := ih middle (offset + 8) binding domain (by omega) (by omega)
    exact next

theorem writes_inside (pointer : BitVec 64) (offset : Nat) (words : List (BitVec 64)) :
    ∀ entry,entry ∈ writes pointer offset words → ∃ index : Nat,offset ≤ index ∧ index < offset + 8 * words.length ∧ entry.1 = pointer + BitVec.ofNat 64 index := by
  induction words generalizing offset with
  | nil => intro entry member; cases member
  | cons word rest ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | found
    · exact ⟨offset,Nat.le_refl _,by simp only [List.length_cons]; omega,rfl⟩
    · obtain ⟨index,lower,upper,address⟩ := ih (offset + 8) entry found
      exact ⟨index,by omega,by simp only [List.length_cons]; omega,address⟩

theorem window (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset extent : Nat) (words : List (BitVec 64))
    (arena : AllocatedBytes.Arena pointer extent) (inside : offset + 8 * words.length ≤ extent) :
    Rlp.Slices.Window source (written source pointer offset words) pointer.toNat (pointer.toNat + extent) := by
  intro query away
  apply WordWrites.write_away
  intro found
  obtain ⟨entry,member,same⟩ := List.mem_map.mp found
  obtain ⟨index,lower,upper,address⟩ := writes_inside pointer offset words entry member
  have number := byteAddress_toNat pointer index (by have := arena.upper; omega)
  change (pointer + BitVec.ofNat 64 index).toNat = pointer.toNat + index at number
  have equal := congrArg BitVec.toNat (same.symm.trans address)
  rw [number] at equal
  rcases away with before | after <;> omega

theorem written_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List (BitVec 64)) (clock : Nat) :
    written {source with clock := clock} pointer offset words = {written source pointer offset words with clock := clock} := rfl

end InitECandidate.Solver.Input.InitializerWords

#print axioms InitECandidate.Solver.Input.InitializerWords.execute
#print axioms InitECandidate.Solver.Input.InitializerWords.writes_inside
#print axioms InitECandidate.Solver.Input.InitializerWords.window
#print axioms InitECandidate.Solver.Input.InitializerWords.written_clock
