import InitECandidate.Solver.WitnessRadix.TableLocals
import InitECandidate.Solver.WitnessRadix.ZeroSmallCall

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def usedAddress (plan : AllocatedLayout.Plan) : BitVec 64 := BitVec.ofNat 64 (plan.table + 72 + 40 * plan.capacity)
def clearCost (capacity : Nat) : Nat := if capacity = 4 then capacity + 1 else Zero.price capacity + 1
def clearMemory (memory : WordWrites.Memory) (be : Bool) (plan : AllocatedLayout.Plan) : WordWrites.Memory :=
  if plan.capacity = 4 then Zero.memoryByte memory be (usedAddress plan) 0 plan.capacity
  else Zero.finalMemory memory (usedAddress plan) plan.capacity
def clearState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  { source with
    memory := clearMemory source.memory source.be plan
    clock := source.clock - clearCost plan.capacity }
def clearCall : ProgHOL 64 :=
  .call (some (none, none)) (ofString "memzero") [localVar "used", localVar "cap"]

/-- The real used-array clearing call, with both cap=4 and word-multiple
capacities, from actual domain/heap layout and caller ABI/code facts. -/
theorem clear_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : plan.capacity = 4 ∨ plan.capacity % 8 = 0)
    (usedLocal : source.locals.lookup (ofString "used") = some (.val (.word (usedAddress plan))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (code : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : clearCost plan.capacity ≤ source.clock) :
    evaluateHOLFiniteState source clearCall = (none, clearState source plan) := by
  classical
  have fits := ready.fits
  have room := ready.room
  have lower := ready.recordsLower
  have beforeRecords := ready.recordsBefore
  have tableAligned := ready.tableAligned
  have usedSmall : plan.table + 72 + 40 * plan.capacity < 2 ^ 64 := by omega
  have number : (usedAddress plan).toNat = plan.table + 72 + 40 * plan.capacity := by
    rw [usedAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedSmall]
  have aligned : (usedAddress plan).toNat % 8 = 0 := by rw [number]; omega
  have srcFits : (usedAddress plan).toNat + 32 < 2 ^ 64 := by rw [number]; omega
  have baseMapped : source.memaddrs (usedAddress plan) := by
    rw [domain]
    apply BackingLayout.ordinary_mapped _ (by rw [number]; omega) (by rw [number]; omega) aligned
  have mapped (offset : Nat) (high : offset + 8 ≤ plan.capacity) (offsetAligned : offset % 8 = 0) :
      source.memaddrs (byteAddress (usedAddress plan) offset) := by
    rw [domain]
    have nowrap : (usedAddress plan).toNat + offset < 2 ^ 64 := by rw [number]; omega
    have address := byteAddress_toNat (usedAddress plan) offset nowrap
    apply BackingLayout.ordinary_mapped _ (by rw [address, number]; omega) (by rw [address, number]; omega)
      (byteAddress_aligned _ _ aligned offsetAligned nowrap)
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "used", localVar "cap"] = some (Zero.values (usedAddress plan) plan.capacity) := by
    simp [Zero.values, localVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, usedLocal, capLocal]
  by_cases four : plan.capacity = 4
  · have run := Zero.call_small source _ (usedAddress plan) plan.capacity args code (by omega) aligned srcFits baseMapped
      (by simpa only [clearCost, if_pos four] using enough)
    simpa only [clearCall, clearState, clearMemory, clearCost, if_pos four] using run
  · have multiple : plan.capacity % 8 = 0 := capacityShape.resolve_left four
    have run := Zero.call_execute source _ (usedAddress plan) plan.capacity args code (by omega) multiple aligned mapped
      (by simpa only [clearCost, if_neg four] using enough)
    simpa only [clearCall, clearState, clearMemory, clearCost, if_neg four] using run

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.clear_execute
