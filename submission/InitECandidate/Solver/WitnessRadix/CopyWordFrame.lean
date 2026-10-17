import InitECandidate.Solver.WitnessRadix.CopyWordBlock

namespace InitECandidate.Solver.WitnessRadix.CopyWords
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def memoryMany (memory : WordWrites.Memory) (src dst index : BitVec 64) : List Nat → WordWrites.Memory
  | [] => memory
  | offset :: rest => memoryMany (copyMemory memory src dst index offset) src dst index rest

theorem writeMany_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) :
    writeMany source src dst index offsets = { source with memory := memoryMany source.memory src dst index offsets } := by
  induction offsets generalizing source with
  | nil => rfl
  | cons offset rest ih => rw [writeMany, ih]; rfl

theorem memoryMany_away (memory : WordWrites.Memory) (src dst index query : BitVec 64) (offsets : List Nat)
    (away : ∀ offset ∈ offsets, query ≠ dst + index + BitVec.ofNat 64 offset) :
    memoryMany memory src dst index offsets query = memory query := by
  induction offsets generalizing memory with
  | nil => rfl
  | cons offset rest ih =>
    rw [memoryMany, ih _ (by intro offset member; exact away offset (List.mem_cons_of_mem _ member))]
    exact if_neg (away offset (by simp))

theorem advance_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst index : BitVec 64) (offsets : List Nat) (step : BitVec 64) :
    emptyLocalsHOLFinite (advance source src dst index offsets step) =
      emptyLocalsHOLFinite { source with memory := memoryMany source.memory src dst index offsets } := by
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

end InitECandidate.Solver.WitnessRadix.CopyWords

#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.writeMany_frame
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.memoryMany_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.advance_frame
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.advance_index
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.advance_other
