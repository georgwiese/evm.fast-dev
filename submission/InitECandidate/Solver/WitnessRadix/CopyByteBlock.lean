import InitECandidate.Solver.WitnessRadix.CopyByteProgram
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.WitnessRadix.CopyBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def writeMany {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) : List Nat → PanSemStateFiniteExact 64 F
  | [] => source
  | offset :: rest => writeMany (written source src dst index offset) src dst index rest

theorem writeMany_fields {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) :
    (writeMany source src dst index offsets).locals = source.locals ∧
    (writeMany source src dst index offsets).memaddrs = source.memaddrs ∧
    (writeMany source src dst index offsets).clock = source.clock := by
  induction offsets generalizing source with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons offset rest ih => exact ih (written source src dst index offset)

theorem stores_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat)
    (tail : ProgHOL 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (sourceMapped : ∀ offset ∈ offsets, source.memaddrs (panByteAlignHOL (width := 64) (src + index + BitVec.ofNat 64 offset)))
    (destinationMapped : ∀ offset ∈ offsets, source.memaddrs (panByteAlignHOL (width := 64) (dst + index + BitVec.ofNat 64 offset))) :
    evaluateHOLFiniteState source (stores offsets tail) = evaluateHOLFiniteState (writeMany source src dst index offsets) tail := by
  induction offsets generalizing source with
  | nil => rfl
  | cons offset rest ih =>
    rw [stores, StateSteps.next_sequence source (written source src dst index offset) _ _
      (store_execute source src dst index offset srcLocal dstLocal indexLocal
        (sourceMapped offset (by simp)) (destinationMapped offset (by simp))) (Nat.le_refl _)]
    exact ih _ srcLocal dstLocal indexLocal
      (by intro offset member; exact sourceMapped offset (List.mem_cons_of_mem _ member))
      (by intro offset member; exact destinationMapped offset (List.mem_cons_of_mem _ member))

def advance {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) (step : BitVec 64) :
    PanSemStateFiniteExact 64 F := bind (writeMany source src dst index offsets) "i" (index + step)

theorem block_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) (step : BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (sourceMapped : ∀ offset ∈ offsets, source.memaddrs (panByteAlignHOL (width := 64) (src + index + BitVec.ofNat 64 offset)))
    (destinationMapped : ∀ offset ∈ offsets, source.memaddrs (panByteAlignHOL (width := 64) (dst + index + BitVec.ofNat 64 offset))) :
    evaluateHOLFiniteState source (stores offsets (increment step)) = (none, advance source src dst index offsets step) := by
  rw [stores_execute source src dst index offsets _ srcLocal dstLocal indexLocal sourceMapped destinationMapped]
  have same := (writeMany_fields source src dst index offsets).1
  have nextIndex : (writeMany source src dst index offsets).locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [same]; exact indexLocal
  exact StateSteps.assign_execute _ "i" _ index (index + step) nextIndex
    (by simp [eval, increment, localVar, addConst, evalHOLExact, evalListHOLExact, toExact, nextIndex,
      valueIsWord, valueWord, wordOpHOL, wordOp])

end InitECandidate.Solver.WitnessRadix.CopyBytes

#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.writeMany_fields
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.stores_execute
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.block_execute
