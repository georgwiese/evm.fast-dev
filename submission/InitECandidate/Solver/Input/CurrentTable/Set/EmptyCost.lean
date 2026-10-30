import InitECandidate.Solver.Input.CurrentTable.Set.FirstTrace
import InitECandidate.Solver.Input.CurrentTable.Set.ComparisonEntry
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

theorem empty_after_leaf_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap pointer value : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} (query : KeyBits.Key)
    (image : Image source table cap 0#64 next count valid bits left right keys ValueOf)
    (locals : Locals source table pointer value) (leafCell : source.locals.lookup (ofString "leaf") = some (.val (.word 0#64)))
    (installed : OriginalCode.Installed source.code) (little : source.be = false) (aligned : pointer.toNat%8 = 0)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (bytes : FirstDiff.ByteView source pointer query) (validValue : ValueOf value) :
    source.clock-(evaluateHOLFiniteState source afterLeaf).2.clock ≤ 4 := by
  let selected := keysEntry source table
  have data : Locals selected table pointer value := locals.with_local "keys" _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have currentImage : Image selected table cap 0#64 next count valid bits left right keys ValueOf := image.of_frame rfl
  have currentLeaf : selected.locals.lookup (ofString "leaf") = some (.val (.word 0#64)) :=
    (bind_lookup_other _ "keys" "leaf" _ (by decide)).trans leafCell
  rw [keys_setup image locals.tableCell]
  change source.clock-(evaluateHOLFiniteState selected afterKeys).2.clock ≤ 4
  rw [after_keys_empty selected currentLeaf]
  generalize run : evaluateHOLFiniteState selected emptyLeafCall = output
  obtain ⟨outcome,post⟩ := output
  rcases empty_leaf_trace query currentImage data installed little aligned beforeTable (bytes.of_frame rfl) validValue outcome run with stopped | returned
  · exact stopped.1
  · exact returned.2.1

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.after_keys_empty
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.empty_after_leaf_cost
