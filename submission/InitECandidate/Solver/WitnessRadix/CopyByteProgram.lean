import InitECandidate.Solver.WitnessRadix.Copy32Program
import InitECandidate.Solver.WitnessRadix.ByteRegion

namespace InitECandidate.Solver.WitnessRadix.CopyBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def store (offset : Nat) : ProgHOL 64 := .storeByte (Copy32.address "dst" offset) (.loadByte (Copy32.address "src" offset))
def stores : List Nat → ProgHOL 64 → ProgHOL 64
  | [], tail => tail
  | offset :: rest, tail => .seq (store offset) (stores rest tail)
def increment (step : BitVec 64) : ProgHOL 64 := .assign .local (ofString "i") (addConst (localVar "i") step)
def byteBody : ProgHOL 64 := stores [0,1,2,3,4,5,6,7] (increment 8#64)
def tailBody : ProgHOL 64 := .seq (store 0) (increment 1#64)

theorem loop_shapes : Copy32.loopBytes = .while (Copy32.condition 8#64) byteBody ∧
    Copy32.loopTail = .while (.cmp .lower (localVar "i") (localVar "n")) tailBody := by
  simp only [Copy32.loopBytes, Copy32.loopTail, Copy32.body, BuildProgram.loops, Guest.guestFn_memcpy,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    byteBody, tailBody, stores, store, increment, Copy32.address, Copy32.condition, localVar, addConst, ↓reduceIte]
  exact ⟨by rfl, True.intro⟩

def copyMemory (memory : WordWrites.Memory) (be : Bool) (src dst index : BitVec 64) (offset : Nat) : WordWrites.Memory :=
  ByteStore.put memory be (dst + index + BitVec.ofNat 64 offset)
    (panGetByteWord8HOL (src + index + BitVec.ofNat 64 offset)
      (MemoryBytes.wordBits (memory (panByteAlignHOL (width := 64) (src + index + BitVec.ofNat 64 offset)))) be)
def written {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offset : Nat) : PanSemStateFiniteExact 64 F :=
  { source with memory := copyMemory source.memory source.be src dst index offset }

theorem address_read {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (base index : BitVec 64) (offset : Nat)
    (baseLocal : source.locals.lookup (ofString name) = some (.val (.word base)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index))) :
    eval source (Copy32.address name offset) = some (.val (.word (base + index + BitVec.ofNat 64 offset))) := by
  by_cases zero : offset = 0
  · subst offset
    simpa [eval, Copy32.address, localVar, evalHOLExact, evalListHOLExact, toExact, baseLocal, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  · simp [eval, Copy32.address, zero, localVar, evalHOLExact, evalListHOLExact, toExact, baseLocal, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_assoc]

theorem store_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offset : Nat)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (sourceMapped : source.memaddrs (panByteAlignHOL (width := 64) (src + index + BitVec.ofNat 64 offset)))
    (destinationMapped : source.memaddrs (panByteAlignHOL (width := 64) (dst + index + BitVec.ofNat 64 offset))) :
    evaluateHOLFiniteState source (store offset) = (none, written source src dst index offset) := by
  have srcRead := address_read source "src" src index offset srcLocal indexLocal
  have dstRead := address_read source "dst" dst index offset dstLocal indexLocal
  have loaded := ByteRegion.mapped_read source _ sourceMapped
  have valueRead := ByteRegion.load_expression source _ _ _ srcRead loaded
  exact ByteStore.execute source _ _ _ _ dstRead valueRead destinationMapped

end InitECandidate.Solver.WitnessRadix.CopyBytes

#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.loop_shapes
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.address_read
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.store_execute
