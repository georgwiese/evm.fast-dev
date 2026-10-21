import InitECandidate.Solver.MutableTable.WitnessRuntimeTable
import InitECandidate.Solver.MutableTable.WitnessDatabase
import InitECandidate.Solver.MutableTable.NodeDbOriginalCode
import InitECandidate.Solver.MutableTable.NodeDbAnyCost

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual main-constructed database bounds every original lookup,
including arbitrary or unreadable query pointers, at the tight probe price. -/
theorem Database.any_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch query : BitVec 64) (actual : Database source array table count maximum slices scratch)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (hashCell : source.locals.lookup (ofString "hash")=some (.val (.word query))) :
    source.clock-(evaluateHOLFiniteState source NodeDb.body).2.clock≤6*count+3 := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,rows⟩ := actual.data
  let plan:=Constructor.allocationPlan (effectiveRecords array table count) table.toNat count (2^bits)
  obtain ⟨order,bounded,runtime⟩ := runtime_of_built source plan ready actual.domain bits (by omega) rfl scratch stored input logical built history query
  have helpers:=original_helpers source.code installed
  have price:=NodeDb.any_body_cost source (BitVec.ofNat 64 plan.table) (Layout32.parameters plan query) runtime.header rfl bits runtime.small runtime.capacity order runtime.room
    runtime.binary runtime.covered runtime.fits runtime.mapped helpers.hashCode helpers.compareCode helpers.findCode (NodeDb.original_get_code source.code installed)
    (by simpa only [plan,Constructor.allocationPlan,BitVec.ofNat_toNat,BitVec.setWidth_eq] using dbCell) hashCell
  rw [length] at bounded
  exact price.trans (by omega)

theorem Database.any_body_readonly (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) : Input.LocalEffects.Preserves source.code NodeDb.body := by
  have helpers:=original_helpers source.code installed
  exact NodeDb.any_body_readonly source.code helpers.hashCode helpers.compareCode helpers.findCode (NodeDb.original_get_code source.code installed)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.any_body_cost
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.any_body_readonly
