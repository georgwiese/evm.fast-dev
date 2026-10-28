import InitECandidate.Solver.Input.CurrentTable.Set.DifferenceCost
import InitECandidate.Solver.Input.CurrentTable.Set.Update

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem nonempty_after_leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value leaf : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (locals : Locals source table pointer value)
    (leafCell : source.locals.lookup (ofString "leaf") = some (.val (.word leaf)))
    (member : valid leaf) (marked : bits leaf = 256) (route : Route bits left right query root leaf)
    (view : FirstDiff.ByteView source pointer query) (installed : OriginalCode.Installed source.code)
    (little : source.be = false) (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat) :
    source.clock-(evaluateHOLFiniteState source afterLeaf).2.clock ≤ 557 := by
  classical
  generalize run : evaluateHOLFiniteState source afterLeaf = output
  obtain ⟨outcome,post⟩ := output
  change source.clock-post.clock ≤ 557
  have fits : pointer.toNat+32 < 2^64 := by have := image.geometry.table.upper; omega
  rcases comparison_trace source post table cap root pointer value leaf next count valid bits left right keys query ValueOf
    image locals leafCell member marked view fits little installed outcome run with stopped | reached
  · have price := stopped.1
    omega
  · obtain ⟨target,inner,frame,forward,cost,continued,endpoint⟩ := reached
    let selected := keysEntry source table
    have selectedLocals : LookupLocals selected table pointer value leaf := LookupLocals.after_keys locals leafCell
    by_cases same : keys leaf = query
    · rw [if_pos same] at continued
      let resumed := CallNormal.continuationEntry selected target "eq" (.val (.word 1#64))
      have currentImage : Image resumed table cap root next count valid bits left right keys ValueOf := image.of_frame frame
      have data : LookupLocals resumed table pointer value leaf := selectedLocals.after_call target "eq" _
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have eqCell := CallNormal.continuation_lookup_same selected target "eq" (.val (.word 1#64))
      have updated := after_compare_one currentImage data member eqCell
      rw [updated] at continued
      have clock := congrArg PanSemStateFiniteExact.clock (congrArg Prod.snd continued)
      change target.clock = inner.clock at clock
      rw [endpoint]
      change source.clock-inner.clock ≤ 557
      omega
    · rw [if_neg same] at continued
      let resumed := CallNormal.continuationEntry selected target "eq" (.val (.word 0#64))
      have currentImage : Image resumed table cap root next count valid bits left right keys ValueOf := image.of_frame frame
      have data : LookupLocals resumed table pointer value leaf := selectedLocals.after_call target "eq" _
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have eqCell := CallNormal.continuation_lookup_same selected target "eq" (.val (.word 0#64))
      have currentInstalled : OriginalCode.Installed resumed.code := by rw [LocalEffects.code_of_erase source resumed frame]; exact installed
      have currentLittle := (LocalEffects.endian_of_erase source resumed frame).trans little
      have tail := difference_cost resumed table cap root pointer value leaf next count valid bits left right keys query ValueOf
        currentImage available data member marked route same eqCell (view.of_frame frame) currentInstalled currentLittle aligned beforeTable
      rw [continued] at tail
      change target.clock-inner.clock ≤ 552 at tail
      rw [endpoint]
      change source.clock-inner.clock ≤ 557
      omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.nonempty_after_leaf_cost
