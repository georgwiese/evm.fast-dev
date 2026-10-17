import InitECandidate.Solver.WitnessRadix.ByteStore

namespace InitECandidate.Solver.WitnessRadix.ByteRegion
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

noncomputable def read {F : Type} (source : PanSemStateFiniteExact 64 F) (address : BitVec 64) : Option (BitVec 8) :=
  @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
    (fun pointer => Classical.propDecidable (source.memaddrs pointer)) source.be address
def value {F : Type} (source : PanSemStateFiniteExact 64 F) (address : BitVec 64) : BitVec 8 :=
  panGetByteWord8HOL address (MemoryBytes.wordBits (source.memory (panByteAlignHOL (width := 64) address))) source.be
def Reads {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length : Nat) (bytes : Nat → BitVec 8) : Prop :=
  ∀ offset < length, read source (byteAddress pointer offset) = some (bytes offset)

theorem mapped_read {F : Type} (source : PanSemStateFiniteExact 64 F) (address : BitVec 64)
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) address)) : read source address = some (value source address) := by
  cases stored : source.memory (panByteAlignHOL (width := 64) address) with
  | word word => simp [read, value, panMemLoadByteWord8HOL, mapped, stored, MemoryBytes.wordBits]

theorem mapped_region {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length : Nat)
    (mapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset))) :
    Reads source pointer length (fun offset => value source (byteAddress pointer offset)) := by
  intro offset inside
  exact mapped_read source _ (mapped offset inside)

theorem read_of_cell {F : Type} (source target : PanSemStateFiniteExact 64 F) (address : BitVec 64)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (memory : source.memory (panByteAlignHOL (width := 64) address) = target.memory (panByteAlignHOL (width := 64) address)) :
    read source address = read target address := by
  classical
  by_cases mapped : target.memaddrs (panByteAlignHOL (width := 64) address)
  all_goals simp [read, panMemLoadByteWord8HOL, domain, endian, memory, mapped]

theorem of_cells {F : Type} (source target : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length : Nat) (bytes : Nat → BitVec 8)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (memory : ∀ offset < length, source.memory (panByteAlignHOL (width := 64) (byteAddress pointer offset)) =
      target.memory (panByteAlignHOL (width := 64) (byteAddress pointer offset)))
    (reads : Reads source pointer length bytes) : Reads target pointer length bytes := by
  intro offset inside
  rw [← read_of_cell source target _ domain endian (memory offset inside)]
  exact reads offset inside

theorem load_expression {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64)
    (address : BitVec 64) (byte : BitVec 8)
    (readAddress : QueryBranch.eval source expression = some (.val (.word address)))
    (loaded : read source address = some byte) :
    QueryBranch.eval source (.loadByte expression) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
  simp only [QueryBranch.eval] at readAddress ⊢
  change @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
    (fun pointer => Classical.propDecidable (source.memaddrs pointer)) source.be address = some byte at loaded
  simp [evalHOLExact, readAddress, panMemLoadByteHOL_eq_word8_projection, loaded]

end InitECandidate.Solver.WitnessRadix.ByteRegion

#print axioms InitECandidate.Solver.WitnessRadix.ByteRegion.mapped_region
#print axioms InitECandidate.Solver.WitnessRadix.ByteRegion.of_cells
#print axioms InitECandidate.Solver.WitnessRadix.ByteRegion.load_expression
