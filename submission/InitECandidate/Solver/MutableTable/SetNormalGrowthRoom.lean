import InitECandidate.Solver.MutableTable.GrowRuntime.NormalRoom
import InitECandidate.Solver.MutableTable.SetGrowGuard
import InitECandidate.Solver.MutableTable.MemoryModelReads
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Only the actual absent-key, threshold-crossing normal setter suffix
has to establish new allocation room. An update at full threshold does not
inherit an unused future-growth premise. -/
theorem growth_layout_of_normal_tail (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (valid : Valid kind old) (start count : Nat) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start) (domain : source.memaddrs = InitE.ordinaryDomain)
    (countBound : count ≤ old.capacity) (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 count))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 old.capacity))))
    (threshold : old.capacity < 2 * count + 2)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterIndex = (some (.returned value), target)) :
    Valid kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
  have capRead := MemoryModel.Header.read source kind old valid domain _ header tableLocal 16 (by decide) (by decide)
    (BitVec.ofNat 64 old.capacity) (by simp [MemoryModel.headerEntries])
  have skip : evaluateHOLFiniteState source (.ite presentTest updateBranch .skip) = (none, source) := by
    simp only [eval] at capRead
    simp [evaluateHOLFiniteState_ite, presentTest, evalHOLExact, toExact, localVar, indexLocal, capRead,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have afterPresentRun := normal
  rw [afterIndex, StateSteps.next_sequence source source _ _ skip (Nat.le_refl _)] at afterPresentRun
  have safe : Input.LocalPrefix (ofString "t") (.ite growthTest growCall .skip) :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨grown, growRun, _, _⟩ := safe.normal_continue source target (.seq insertCall Insert.returnZero) value afterPresentRun
  have guard := growth_read source kind old valid domain count countBound header tableLocal threshold
  simp only [eval] at guard
  rw [evaluateHOLFiniteState_ite, guard] at growRun
  simp only [show (1#64 : BitVec 64) ≠ 0#64 from by decide, ↓reduceIte] at growRun
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "t"] = some (Grow.values (cell old .header 0)) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, tableLocal, Grow.values]
  exact GrowRuntime.normal_call_layout source grown kind old valid start count startBound startAligned earlier domain header heap code trapCode growCode [localVar "t"] args growRun

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.growth_layout_of_normal_tail
