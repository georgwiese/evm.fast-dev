import InitECandidate.Solver.MutableTable.TableRuntime.PreClear
import InitECandidate.Solver.WitnessRadix.TableClear

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix
open NaturalLayout

def usedAddress (kind : KeyHash.Kind) (start capacity : Nat) : BitVec 64 := cell (fresh kind start capacity) .used 0

def clearMemory (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (start capacity : Nat) : WordWrites.Memory :=
  if capacity = 4 then Zero.memoryByte memory be (usedAddress kind start capacity) 0 capacity
  else Zero.finalMemory memory (usedAddress kind start capacity) capacity

def clearState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  {source with
    memory := (clearMemory source.memory source.be kind start capacity)
    clock := source.clock - TableNew.clearCost capacity}

/-- Actual original used-array clear, with both short-capacity and word-
multiple branches. Every mapping/no-wrap fact follows from fresh geometry. -/
theorem clear_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : capacity = 4 ∨ capacity % 8 = 0)
    (usedLocal : source.locals.lookup (ofString "used") = some (.val (.word (usedAddress kind start capacity))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))))
    (code : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : TableNew.clearCost capacity ≤ source.clock) :
    evaluateHOLFiniteState source TableNew.clearCall = (none, clearState source kind start capacity) := by
  classical
  have high := valid.upper .used
  have roundBounds := rounded_bounds capacity
  have positive : 0 < capacity := valid.positive
  have number : (usedAddress kind start capacity).toNat = start + 72 + stride kind * capacity + 8 * capacity := base_number kind _ valid .used
  have aligned : (usedAddress kind start capacity).toNat % 8 = 0 := by rw [number]; exact valid.aligned .used
  have srcFits : (usedAddress kind start capacity).toNat + 32 < 2 ^ 64 := by
    rw [number]
    change start + 72 + stride kind * capacity + 8 * capacity + rounded capacity ≤ 33806089496 at high
    omega
  have baseMapped : source.memaddrs (usedAddress kind start capacity) := by
    rw [domain]
    exact mapped kind (fresh kind start capacity) valid .used 0 (by change 0 < rounded capacity; omega) (by decide)
  have allMapped (offset : Nat) (inside : offset + 8 ≤ capacity) (offsetAligned : offset % 8 = 0) :
      source.memaddrs (byteAddress (usedAddress kind start capacity) offset) := by
    rw [domain]
    change InitE.ordinaryDomain (byteAddress (cell (fresh kind start capacity) .used 0) offset)
    rw [offset_cell]
    exact mapped kind (fresh kind start capacity) valid .used offset (by change offset < rounded capacity; omega) offsetAligned
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "used", localVar "cap"] =
      some (Zero.values (usedAddress kind start capacity) capacity) := by
    simp [Zero.values, localVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, usedLocal, capLocal]
  by_cases four : capacity = 4
  · have run := Zero.call_small source _ (usedAddress kind start capacity) capacity args code (by omega) aligned srcFits baseMapped
      (by simpa only [TableNew.clearCost, if_pos four] using enough)
    simpa only [TableNew.clearCall, clearState, clearMemory, TableNew.clearCost, if_pos four] using run
  · have multiple := capacityShape.resolve_left four
    have small : capacity + 32 < 2 ^ 64 := by
      change start + 72 + stride kind * capacity + 8 * capacity + rounded capacity ≤ 33806089496 at high
      omega
    have run := Zero.call_execute source _ (usedAddress kind start capacity) capacity args code small multiple aligned allMapped
      (by simpa only [TableNew.clearCost, if_neg four] using enough)
    simpa only [TableNew.clearCall, clearState, clearMemory, TableNew.clearCost, if_neg four] using run

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.clear_execute
