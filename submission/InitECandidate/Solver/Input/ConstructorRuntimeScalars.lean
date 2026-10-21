import InitECandidate.Solver.Input.ConstructorRuntimeFrame
import InitECandidate.Solver.Input.OriginalScalarGlobals

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- All original scalar globals remain typed when the three changed names
carry their actual current heap/hash-array/count words. -/
theorem ConstructorRuntimeFrame.scalars (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : ConstructorRuntimeFrame source target) (original : OriginalScalarGlobals.Scalars source.globals)
    (heap hashes count : BitVec 64)
    (heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (hashesCell : target.globals.lookup (ofString "block_hashes")=some (.val (.word hashes)))
    (countCell : target.globals.lookup (ofString "block_hashes_n")=some (.val (.word count))) :
    OriginalScalarGlobals.Scalars target.globals := by
  intro key member
  by_cases h : key=ofString "heap_ptr"
  · subst key; exact ⟨heap,heapCell⟩
  · by_cases b : key=ofString "block_hashes"
    · subst key; exact ⟨hashes,hashesCell⟩
    · by_cases n : key=ofString "block_hashes_n"
      · subst key; exact ⟨count,countCell⟩
      · obtain ⟨word,cell⟩ := original key member
        exact ⟨word,(frame.globals key h b n).trans cell⟩

theorem RunAttempt.constructor_hash_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count hashes : BitVec 64) (parent : ValueHOL 64) :
    (constructorEntry source count hashes parent).globals.lookup (ofString "block_hashes")=some (.val (.word hashes)) ∧
    (constructorEntry source count hashes parent).globals.lookup (ofString "block_hashes_n")=some (.val (.word count)) := by
  simp [constructorEntry,putGlobal,HolFiniteMapExact.update,FUPDATE,
    show ofString "block_hashes_n"≠ofString "block_hashes" from by decide]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.ConstructorRuntimeFrame.scalars
#print axioms InitECandidate.Solver.Input.RunAttempt.constructor_hash_cells
