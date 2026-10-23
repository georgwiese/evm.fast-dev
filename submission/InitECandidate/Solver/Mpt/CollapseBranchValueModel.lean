import InitECandidate.Solver.Mpt.CollapseBranchScanModel

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Installing the genuine vl declaration retains every actual scan
counter, saved child index and nonnull selected-slot fact. -/
def ScanModel.with_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node value : BitVec 64) (model : ScanModel source node) :
    ScanModel (QueryBranch.bind source "vl" value) node := {
  index:=model.index
  count:=model.count
  selectedIndex:=model.selectedIndex
  nodeCell:=(bind_lookup_other source "vl" "node" value (by decide)).trans model.nodeCell
  counterCell:=(bind_lookup_other source "vl" "i" value (by decide)).trans model.counterCell
  countCell:=(bind_lookup_other source "vl" "count" value (by decide)).trans model.countCell
  indexCell:=(bind_lookup_other source "vl" "idx" value (by decide)).trans model.indexCell
  bounded:=model.bounded
  countBound:=model.countBound
  indexBound:=model.indexBound
  selectedBefore:=model.selectedBefore
  selectedNonzero:=model.selectedNonzero }

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.ScanModel.with_value
