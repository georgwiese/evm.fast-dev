import InitECandidate.Solver.Input.StoreWordsNormal
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- An actual normal scalar store derives its destination mapping and exact
memory effect from the two known expression reads. -/
theorem word_store_normal {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address word : BitVec 64)
    (addressRead : eval source destination = some (.val (.word address)))
    (wordRead : eval source expression = some (.val (.word word)))
    (normal : evaluateHOLFiniteState source (.store destination expression) = (none, target)) :
    source.memaddrs address ∧ target = {source with memory := WitnessRadix.StoreWord.put source.memory address word} := by
  classical
  obtain ⟨actual, memory, read, stores, frame⟩ := store_at_normal source target destination expression address addressRead normal
  have same : actual = .val (.word word) := Option.some.inj (read.symm.trans wordRead)
  subst actual
  by_cases mapped : source.memaddrs address
  · have memoryEq : memory = WitnessRadix.StoreWord.put source.memory address word := by
      change memory = (fun current => if current = address then .word word else source.memory current)
      simpa only [flattenHOL, panMemStoresHOL, panMemStoreHOL, if_pos mapped, Option.some.injEq] using stores.symm
    exact ⟨mapped, by rw [frame, memoryEq]⟩
  · simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, mapped] at stores

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.word_store_normal
