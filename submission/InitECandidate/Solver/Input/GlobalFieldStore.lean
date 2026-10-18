import InitECandidate.Solver.MutableTable.MemoryRegionWord
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Actual scalar store through an owned global record pointer. Its physical
word mapping follows from the region geometry; it changes no clock/global. -/
theorem global_field_store {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (region : MemoryRegion.Region)
    (valid : MemoryRegion.Valid region) (domain : source.memaddrs = InitE.ordinaryDomain) (offset : Nat)
    (inside : offset + 8 ≤ region.length) (aligned : offset % 8 = 0)
    (base : source.globals.lookup (ofString name) = some (.val (.word (MemoryRegion.pointer region))))
    (expression : ExpHOL 64) (word : BitVec 64) (read : eval source expression = some (.val (.word word))) :
    evaluateHOLFiniteState source (.store (addConst (.var .global (ofString name)) (BitVec.ofNat 64 offset)) expression) =
      (none, {source with memory := StoreWord.put source.memory (MemoryRegion.address region offset) word}) := by
  have addressRead : eval source (addConst (.var .global (ofString name)) (BitVec.ofNat 64 offset)) =
      some (.val (.word (MemoryRegion.address region offset))) := by
    simp [eval, addConst, evalHOLExact, evalListHOLExact, toExact, base, valueIsWord, valueWord, wordOpHOL, wordOp,
      MemoryRegion.pointer, MemoryRegion.address, BitVec.ofNat_add]
  have mapped : source.memaddrs (MemoryRegion.address region offset) := by
    rw [domain]
    simpa only [MemoryRegion.byte_address] using MemoryRegion.word_mapped region valid offset inside aligned
  exact StoreWord.execute source _ _ _ _ addressRead read mapped

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.global_field_store
