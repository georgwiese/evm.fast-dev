import InitECandidate.Solver.Input.CurrentTable.Set.NonemptyReturned
import InitECandidate.Solver.Input.CurrentTable.Set.EmptyReturned

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Every real normal whole htab_set return preserves a complete current
table image, adds at most one leaf and protects all earlier decoded input.
This is the original callee run, including either comparison outcome. -/
theorem body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (countRoom : count+1 ≤ cap.toNat)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (view : FirstDiff.ByteView source pointer query) (valueMember : ValueOf value)
    (installed : OriginalCode.Installed source.code) (little : source.be = false)
    (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat)
    (answer : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned answer),post)) :
    answer = .val (.word 0#64) ∧ Result source post table cap count ValueOf := by
  rcases lookup_trace source post table cap root pointer next count valid bits left right keys query ValueOf
    image tableCell keyCell view installed (some (.returned answer)) normal with stopped | reached
  · exact (stopped.2 answer rfl).elim
  · obtain ⟨target,leaf,inner,found,frame,forward,cost,continued,endpoint⟩ := reached
    let resumed := CallNormal.continuationEntry (strideEntry source) target "leaf" (.val (.word leaf))
    have data : Locals resumed table pointer value := (initial_locals source table pointer value tableCell keyCell valueCell).after_call target "leaf" _
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentImage : Image resumed table cap root next count valid bits left right keys ValueOf := image.of_frame frame
    have currentInstalled : OriginalCode.Installed resumed.code := by rw [LocalEffects.code_of_erase source resumed frame]; exact installed
    have currentLittle := (LocalEffects.endian_of_erase source resumed frame).trans little
    have leafCell := CallNormal.continuation_lookup_same (strideEntry source) target "leaf" (.val (.word leaf))
    have tail : answer = .val (.word 0#64) ∧ Result resumed inner table cap count ValueOf := by
      rcases found with empty | nonempty
      · obtain ⟨rootZero,leafZero⟩ := empty
        subst root
        subst leaf
        exact empty_after_leaf_returned query currentImage data leafCell currentInstalled currentLittle aligned beforeTable (view.of_frame frame) valueMember answer continued
      · obtain ⟨member,marked,route⟩ := nonempty
        exact nonempty_after_leaf_returned resumed inner table cap root pointer value leaf next count valid bits left right keys query ValueOf
          currentImage available countRoom data leafCell member marked route (view.of_frame frame) valueMember currentInstalled currentLittle aligned beforeTable answer continued
    exact ⟨tail.1,tail.2.of_frames frame (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.body_returned
