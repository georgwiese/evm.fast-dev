import InitECandidate.Solver.WitnessRadix.CopyByteBlock

namespace InitECandidate.Solver.WitnessRadix.CopyBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def memoryMany (memory : WordWrites.Memory) (be : Bool) (src dst index : BitVec 64) : List Nat → WordWrites.Memory
  | [] => memory
  | offset :: rest => memoryMany (copyMemory memory be src dst index offset) be src dst index rest

theorem writeMany_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) :
    writeMany source src dst index offsets = { source with memory := memoryMany source.memory source.be src dst index offsets } := by
  induction offsets generalizing source with
  | nil => rfl
  | cons offset rest ih => rw [writeMany, ih]; rfl

theorem memoryMany_away (memory : WordWrites.Memory) (be : Bool) (src dst index query : BitVec 64) (offsets : List Nat)
    (away : ∀ offset ∈ offsets, query ≠ panByteAlignHOL (width := 64) (dst + index + BitVec.ofNat 64 offset)) :
    memoryMany memory be src dst index offsets query = memory query := by
  induction offsets generalizing memory with
  | nil => rfl
  | cons offset rest ih =>
    rw [memoryMany, ih _ (by intro offset member; exact away offset (List.mem_cons_of_mem _ member))]
    exact ByteStore.away _ _ _ _ _ (away offset (by simp))

theorem advance_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) (step : BitVec 64) :
    emptyLocalsHOLFinite (advance source src dst index offsets step) =
      emptyLocalsHOLFinite { source with memory := memoryMany source.memory source.be src dst index offsets } := by
  rw [advance, writeMany_frame]
  rfl

theorem advance_index {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) (step : BitVec 64) :
    (advance source src dst index offsets step).locals.lookup (ofString "i") = some (.val (.word (index + step))) :=
  bind_lookup_same _ _ _

theorem advance_other {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) (step : BitVec 64)
    (name : MlS) (different : ofString "i" ≠ name) :
    (advance source src dst index offsets step).locals.lookup name = source.locals.lookup name := by
  simp [advance, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different,
    (writeMany_fields source src dst index offsets).1]

end InitECandidate.Solver.WitnessRadix.CopyBytes

#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.writeMany_frame
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.memoryMany_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.advance_frame
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.advance_index
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.advance_other
