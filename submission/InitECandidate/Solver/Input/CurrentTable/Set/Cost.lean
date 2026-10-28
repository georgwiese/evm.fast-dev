import InitECandidate.Solver.Input.CurrentTable.Set.NonemptyCost
import InitECandidate.Solver.Input.CurrentTable.Set.EmptyCost

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- One complete unchanged current32-byte-key htab_set costs at most815
source body ticks from its reached insertion image and real remaining
capacity. All errors, allocation/copy failures and timeouts are included. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (view : FirstDiff.ByteView source pointer query) (validValue : ValueOf value)
    (installed : OriginalCode.Installed source.code) (little : source.be = false)
    (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat) :
    source.clock-(evaluateHOLFiniteState source body).2.clock ≤ 815 := by
  generalize run : evaluateHOLFiniteState source body = output
  obtain ⟨outcome,post⟩ := output
  change source.clock-post.clock ≤ 815
  rcases lookup_trace source post table cap root pointer next count valid bits left right keys query ValueOf
    image tableCell keyCell view installed outcome run with stopped | reached
  · have price := stopped.1
    omega
  · obtain ⟨target,leaf,inner,found,frame,forward,cost,continued,endpoint⟩ := reached
    let resumed := CallNormal.continuationEntry (strideEntry source) target "leaf" (.val (.word leaf))
    have data : Locals resumed table pointer value := (initial_locals source table pointer value tableCell keyCell valueCell).after_call target "leaf" _
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentImage : Image resumed table cap root next count valid bits left right keys ValueOf := image.of_frame frame
    have currentInstalled : OriginalCode.Installed resumed.code := by rw [LocalEffects.code_of_erase source resumed frame]; exact installed
    have currentLittle := (LocalEffects.endian_of_erase source resumed frame).trans little
    have leafCell := CallNormal.continuation_lookup_same (strideEntry source) target "leaf" (.val (.word leaf))
    have tail : target.clock-inner.clock ≤ 557 := by
      rcases found with empty | nonempty
      · obtain ⟨rootZero,leafZero⟩ := empty
        subst root
        subst leaf
        have price := empty_after_leaf_cost query currentImage data leafCell currentInstalled currentLittle aligned beforeTable (view.of_frame frame) validValue
        rw [continued] at price
        change target.clock-inner.clock ≤ 4 at price
        omega
      · obtain ⟨member,marked,route⟩ := nonempty
        have price := nonempty_after_leaf_cost resumed table cap root pointer value leaf next count valid bits left right keys query ValueOf
          currentImage available data leafCell member marked route (view.of_frame frame) currentInstalled currentLittle aligned beforeTable
        rw [continued] at price
        exact price
    rw [endpoint]
    change source.clock-inner.clock ≤ 815
    omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.body_cost
