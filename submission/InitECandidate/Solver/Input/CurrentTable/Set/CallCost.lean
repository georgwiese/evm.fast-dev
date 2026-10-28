import InitECandidate.Solver.Input.CurrentTable.Set.Cost
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- A real ordinary call to unchanged current htab_set adds one tick to
the815-tick body allowance, covering every evaluator outcome. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (view : FirstDiff.ByteView source pointer query) (validValue : ValueOf value)
    (installed : OriginalCode.Installed source.code) (little : source.be = false)
    (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word table),.val (.word pointer),.val (.word value)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htab_set") expressions)).2.clock ≤ 816 := by
  obtain ⟨callee,called,tableCell,keyCell,valueCell⟩ := word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value (by decide) (by decide) (by decide)
    (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have entryImage : Image entry table cap root next count valid bits left right keys ValueOf := image.of_frame rfl
  have price := body_cost entry table cap root pointer value next count valid bits left right keys query ValueOf entryImage available
    tableCell keyCell valueCell (view.of_frame rfl) validValue installed little aligned beforeTable
  exact ClockCost.call_current source destination (ofString "htab_set") expressions _ body callee .one 815 args called price

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.call_cost
