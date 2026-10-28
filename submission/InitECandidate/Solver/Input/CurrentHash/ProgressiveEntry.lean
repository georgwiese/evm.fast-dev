import InitECandidate.Solver.Input.ProgressiveUpdates

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem pair_entry_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n off size : Nat) :
    CeilLog2.frozen (pairEntry source n off size)=CeilLog2.frozen source ∧ (pairEntry source n off size).clock=source.clock :=
  capped_frame (bind source "cnt" (BitVec.ofNat 64 (n-off))) size (n-off)

theorem pair_entry_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n off size : Nat) (name : String)
    (different : ofString "cnt"≠ofString name) :
    (pairEntry source n off size).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (capped_other (bind source "cnt" (BitVec.ofNat 64 (n-off))) size (n-off) name different).trans
    (bind_lookup_other source "cnt" name (BitVec.ofNat 64 (n-off)) different)

theorem pair_entry_count (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n off size : Nat) :
    (pairEntry source n off size).locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 (min size (n-off))))) :=
  capped_count (bind source "cnt" (BitVec.ofNat 64 (n-off))) size (n-off) (bind_lookup_same _ _ _)

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.pair_entry_frame
#print axioms InitECandidate.Solver.Input.Progressive.pair_entry_other
#print axioms InitECandidate.Solver.Input.Progressive.pair_entry_count
