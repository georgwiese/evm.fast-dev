import InitECandidate.Solver.WitnessRadix.CopyByteProgram

namespace InitECandidate.Solver.WitnessRadix.CopyWords
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def stores : List Nat → ProgHOL 64 → ProgHOL 64
  | [], tail => tail
  | offset :: rest, tail => .seq (Copy32.wordStore offset) (stores rest tail)

theorem loop_shapes : Copy32.loop32 = .while (Copy32.condition 32#64) (stores [0,8,16,24] (CopyBytes.increment 32#64)) ∧
    Copy32.loopWord = .while (Copy32.condition 8#64) (stores [0] (CopyBytes.increment 8#64)) := by
  constructor
  · rw [Copy32.loop32_shape]; rfl
  · simp only [Copy32.loopWord, Copy32.body, BuildProgram.loops, Guest.guestFn_memcpy,
      progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
      List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      stores, CopyBytes.increment, Copy32.wordStore, Copy32.address, Copy32.condition, localVar, addConst, ↓reduceIte]

def copyMemory (memory : WordWrites.Memory) (src dst index : BitVec 64) (offset : Nat) : WordWrites.Memory :=
  StoreWord.put memory (dst + index + BitVec.ofNat 64 offset)
    (MemoryBytes.wordBits (memory (src + index + BitVec.ofNat 64 offset)))
def written {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offset : Nat) : PanSemStateFiniteExact 64 F :=
  { source with memory := copyMemory source.memory src dst index offset }

theorem store_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offset : Nat)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (sourceMapped : source.memaddrs (src + index + BitVec.ofNat 64 offset))
    (destinationMapped : source.memaddrs (dst + index + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState source (Copy32.wordStore offset) = (none, written source src dst index offset) := by
  have srcRead := CopyBytes.address_read source "src" src index offset srcLocal indexLocal
  have dstRead := CopyBytes.address_read source "dst" dst index offset dstLocal indexLocal
  have valueRead : eval source (.load .one (Copy32.address "src" offset)) =
      some (.val (.word (MemoryBytes.wordBits (source.memory (src + index + BitVec.ofNat 64 offset))))) := by
    cases cell : source.memory (src + index + BitVec.ofNat 64 offset) with
    | word value =>
      simp only [eval] at srcRead ⊢
      simp [evalHOLExact, srcRead, memLoadHOLExact, sourceMapped, cell, MemoryBytes.wordBits]
  exact StoreWord.execute source _ _ _ _ dstRead valueRead destinationMapped

end InitECandidate.Solver.WitnessRadix.CopyWords

#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.loop_shapes
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.store_execute
