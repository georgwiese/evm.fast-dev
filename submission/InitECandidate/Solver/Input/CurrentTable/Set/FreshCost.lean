import InitECandidate.Solver.Input.CurrentTable.Set.FreshAllocationTrace

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Both original constructors plus every original parent/child/root
rewiring outcome cost at most six actual source ticks in total. -/
theorem fresh_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value : BitVec 64}
    {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} (query : KeyBits.Key)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (locals : Locals source table pointer value)
    (differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference))))
    (installed : OriginalCode.Installed source.code) (little : source.be = false) (aligned : pointer.toNat%8 = 0)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (bytes : FirstDiff.ByteView source pointer query) :
    source.clock-(evaluateHOLFiniteState source newLeafCall).2.clock ≤ 6 := by
  generalize run : evaluateHOLFiniteState source newLeafCall = output
  obtain ⟨outcome,post⟩ := output
  rcases fresh_allocation_trace query image available locals differenceCell installed little aligned beforeTable bytes outcome run with stopped | reached
  · exact stopped.1
  · obtain ⟨leafTarget,leafPost,internalTarget,inner,frame,forward,cost,spliced,innerEndpoint,endpoint⟩ := reached
    let resumed := CallNormal.continuationEntry
      (CallNormal.continuationEntry source leafTarget "nl" (.val (.word (BitVec.ofNat 64 next))))
      internalTarget "ni" (.val (.word (BitVec.ofNat 64 (next+1))))
    have quiet := splice_quiet resumed.code resumed rfl
    rw [spliced] at quiet
    change inner.clock = internalTarget.clock at quiet
    rw [endpoint,innerEndpoint]
    change source.clock-inner.clock ≤ 6
    rw [quiet]
    exact cost

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_cost
