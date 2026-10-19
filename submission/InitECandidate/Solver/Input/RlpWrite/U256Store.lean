import InitECandidate.Solver.Input.RlpWrite.U256Value
import InitECandidate.Solver.WitnessRadix.WordWrites

namespace InitECandidate.Solver.Input.RlpWrite.U256Value
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def wordWrites (address : BitVec 64) (words : Words) : List (BitVec 64×BitVec 64) :=
  [(address,words 0),(address+8#64,words 1),(address+16#64,words 2),(address+24#64,words 3)]

/-- Exact actual four-limb store, retaining all nonmemory fields. The
current four mapped destinations supply execution, with no future result. -/
theorem store_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address : BitVec 64) (words : Words)
    (destinationRead : WitnessRadix.QueryBranch.eval source destination=some (.val (.word address)))
    (valueRead : WitnessRadix.QueryBranch.eval source expression=some (tuple words))
    (mapped : ∀ index : Fin 4,source.memaddrs (address+BitVec.ofNat 64 (8*index.val))) :
    evaluateHOLFiniteState source (.store destination expression)=
      (none,{source with memory:=WitnessRadix.WordWrites.write source.memory (wordWrites address words)}) := by
  classical
  simp only [WitnessRadix.QueryBranch.eval] at destinationRead valueRead
  have m0 : source.memaddrs address := by simpa using mapped 0
  have m1 : source.memaddrs (address+8#64) := mapped 1
  have m2 : source.memaddrs (address+16#64) := mapped 2
  have m3 : source.memaddrs (address+24#64) := mapped 3
  rw [evaluateHOLFiniteState_store,destinationRead,valueRead]
  simp [tuple,flattenHOL,panMemStoresHOL,panMemStoreHOL,panBytesInWord,BitVec.add_assoc,
    m0,m1,m2,m3,wordWrites,WitnessRadix.WordWrites.write,WitnessRadix.StoreWord.put]
  rfl

end InitECandidate.Solver.Input.RlpWrite.U256Value

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Value.store_execute
