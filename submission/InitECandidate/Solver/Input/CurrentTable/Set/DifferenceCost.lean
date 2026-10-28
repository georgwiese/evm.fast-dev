import InitECandidate.Solver.Input.CurrentTable.Set.DifferenceTrace
import InitECandidate.Solver.Input.CurrentTable.Set.FreshCost

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The genuine failed-equality path includes the first mismatch, second
search, both fresh constructors and every original rewiring outcome. -/
theorem difference_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value leaf : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (locals : LookupLocals source table pointer value leaf)
    (member : valid leaf) (marked : bits leaf = 256) (route : Route bits left right query root leaf)
    (different : keys leaf ≠ query) (eqCell : source.locals.lookup (ofString "eq") = some (.val (.word 0#64)))
    (view : FirstDiff.ByteView source pointer query) (installed : OriginalCode.Installed source.code)
    (little : source.be = false) (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat) :
    source.clock-(evaluateHOLFiniteState source afterCompare).2.clock ≤ 552 := by
  generalize run : evaluateHOLFiniteState source afterCompare = output
  obtain ⟨outcome,post⟩ := output
  change source.clock-post.clock ≤ 552
  rcases difference_trace source post table cap root pointer value leaf next count valid bits left right keys query ValueOf
    image locals member marked route different eqCell view installed outcome run with stopped | reached
  · have price := stopped.1
    omega
  · obtain ⟨entry,target,inner,node,parent,data,state,live,strict,suffix,parentLink,frame,forward,cost,called,endpoint⟩ := reached
    have targetImage := image.of_frame frame
    have targetInstalled : OriginalCode.Installed target.code := by rw [LocalEffects.code_of_erase source target frame]; exact installed
    have targetLittle := (LocalEffects.endian_of_erase source target frame).trans little
    have tail := fresh_cost query targetImage available data.locals state.differenceCell targetInstalled targetLittle aligned beforeTable (view.of_frame frame)
    rw [called] at tail
    change target.clock-inner.clock ≤ 6 at tail
    rw [endpoint]
    change source.clock-inner.clock ≤ 552
    omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.difference_cost
