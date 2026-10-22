import InitECandidate.Solver.MutableTable.TableRuntime.Cost
import InitECandidate.Solver.MutableTable.TableRuntime.Environment
import InitECandidate.Solver.MutableTable.WitnessBuildOriginalHelpers
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.ClockCostAssignedBody

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def costPrice (capacity : Nat) : Nat:=Input.ZeroAny.price capacity+14

/-- Complete actual constructor calls, including failures and timeouts.
Only the true arguments and installed original code are needed. -/
theorem assigned_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (capacity : Nat)
    (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) (small : capacity+32<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values kind capacity)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (destination,none)) (ofString "htab_new") arguments)).2.clock≤costPrice capacity:=by
  obtain ⟨callee,called,keyCell,capCell⟩:=environment source.code.lookup kind capacity (WitnessBuild.original_helpers source.code installed).tableCode
  exact Input.ClockCost.assigned_current source destination (ofString "htab_new") arguments (values kind capacity) TableNew.body callee .one
    (Input.ZeroAny.price capacity+13) args called (Cost.body_cost (callEntryStateHOLFinite source callee) capacity small installed capCell)

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (capacity : Nat)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat) (small : capacity+32<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values kind capacity))
    (tail : Input.ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "htab_new") arguments continuation)).2.clock≤costPrice capacity+tailPrice:=by
  obtain ⟨callee,called,keyCell,capCell⟩:=environment source.code.lookup kind capacity (WitnessBuild.original_helpers source.code installed).tableCode
  have cost:=Input.ClockCost.scoped_current source name .one (ofString "htab_new") arguments (values kind capacity) TableNew.body continuation callee .one
    (Input.ZeroAny.price capacity+13) tailPrice args called (Cost.body_cost (callEntryStateHOLFinite source callee) capacity small installed capCell) tail
  unfold costPrice
  omega

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.assigned_cost
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.scoped_cost
