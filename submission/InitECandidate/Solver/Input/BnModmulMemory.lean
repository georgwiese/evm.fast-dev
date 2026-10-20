import InitECandidate.Solver.Input.BnArithmeticFrame
import InitECandidate.Solver.Input.RlpWrite.U256Store

namespace InitECandidate.Solver.Input.BnModmul
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual twenty current memory words, including the old result words. -/
def inputWords (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) : List Guest.Word :=
  List.ofFn (fun index : Fin 20 => MemoryBytes.wordBits (source.memory (byteAddress pointer (8 * index.val))))

theorem input_length (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) : (inputWords source pointer).length = 20 := by
  simp [inputWords]

theorem input_stored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (index : Fin (inputWords source pointer).length) :
    source.memory (byteAddress pointer (8 * index.val)) = .word ((inputWords source pointer)[index.val]) := by
  have inside : index.val < 20 := by simpa only [input_length] using index.isLt
  simp only [inputWords,List.getElem_ofFn]
  cases source.memory (byteAddress pointer (8 * index.val)) <;> rfl

def operands (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words) :=
  {source with memory := WordWrites.write (WordWrites.write source.memory (RlpWrite.U256Value.wordWrites pointer a)) (RlpWrite.U256Value.wordWrites (pointer + 32#64) b)}

/-- All words outside the two operand tuples retain their actual contents. -/
theorem operands_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (a b : Words)
    (away : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat),query ≠ byteAddress pointer offset) :
    (operands source pointer a b).memory query = source.memory query := by
  change WordWrites.write (WordWrites.write source.memory (RlpWrite.U256Value.wordWrites pointer a)) (RlpWrite.U256Value.wordWrites (pointer + 32#64) b) query = source.memory query
  rw [WordWrites.write_away,WordWrites.write_away]
  all_goals simp only [RlpWrite.U256Value.wordWrites,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,Prod.fst]
  all_goals simp only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] at away
  · simpa [not_or,byteAddress,BitVec.add_assoc] using And.intro (away 0 (by simp)) (And.intro (away 8 (by simp)) (And.intro (away 16 (by simp)) (away 24 (by simp))))
  · simpa [not_or,byteAddress,BitVec.add_assoc] using And.intro (away 32 (by simp)) (And.intro (away 40 (by simp)) (And.intro (away 48 (by simp)) (away 56 (by simp))))

/-- The actual operand stores cannot change any zero/modulus word. -/
theorem operands_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words)
    (offset : Nat) (lower : 64 ≤ offset) (upper : offset < 128) :
    (operands source pointer a b).memory (byteAddress pointer offset) = source.memory (byteAddress pointer offset) := by
  apply operands_away
  intro other member same
  have equal : BitVec.ofNat 64 offset = BitVec.ofNat 64 other := by simpa only [byteAddress,BitVec.add_right_inj] using same
  have numbers := congrArg BitVec.toNat equal
  have range : other = 0 ∨ other = 8 ∨ other = 16 ∨ other = 24 ∨ other = 32 ∨ other = 40 ∨ other = 48 ∨ other = 56 := by simpa using member
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at numbers
  omega

/-- Nonzero modulus is derived from the initialized four physical words. -/
theorem input_modulus (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (stored : ∀ index : Fin 4,source.memory (byteAddress pointer (96 + 8 * index.val)) = .word (Main.BnAccelInitialization.modulus index)) :
    BnArithmetic.modulusOf (inputWords source pointer) ≠ 0 := by
  have words : ((inputWords source pointer).drop 12).take 4 = List.ofFn Main.BnAccelInitialization.modulus := by
    apply List.ext_getElem
    · simp [inputWords]
    · intro index left right
      have inside : index < 4 := by simpa using right
      simp only [List.getElem_take,List.getElem_drop,inputWords,List.getElem_ofFn]
      have point : 8 * (12 + index) = 96 + 8 * index := by omega
      rw [point,stored ⟨index,inside⟩]
      rfl
  unfold BnArithmetic.modulusOf
  rw [words]
  decide

/-- The actual buffer reader is derived from its current mapped cells. -/
theorem read_input (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 160 < 2 ^ 64) (little : source.be = false)
    (mapped : ∀ index : Fin 20,source.memaddrs (byteAddress pointer (8 * index.val))) :
    readBytearrayWordHOL (byteWidth := 8) pointer 160
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun query => Classical.propDecidable (source.memaddrs query)) source.be) =
      some (WordArrayCodec.bits (inputWords source pointer)) := by
  have run := WordArrayRead.read_packed source pointer (inputWords source pointer) aligned
    (by rw [input_length]; exact fits) little (by intro index; exact mapped ⟨index.val,by simpa only [input_length] using index.isLt⟩) (input_stored source pointer)
  simpa only [input_length] using run

end InitECandidate.Solver.Input.BnModmul

#print axioms InitECandidate.Solver.Input.BnModmul.input_length
#print axioms InitECandidate.Solver.Input.BnModmul.input_stored
#print axioms InitECandidate.Solver.Input.BnModmul.operands_away
#print axioms InitECandidate.Solver.Input.BnModmul.operands_prefix
#print axioms InitECandidate.Solver.Input.BnModmul.input_modulus
#print axioms InitECandidate.Solver.Input.BnModmul.read_input
