import InitECandidate.Solver.Input.CurrentTable.Set.DifferenceTrace
import InitECandidate.Solver.Input.CurrentTable.Set.FreshReturned
import InitECandidate.Solver.Input.CurrentTable.Set.ResultModels

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The real failed-comparison continuation, first mismatch, second search
and fresh insertion return a full builder result in the same actual run. -/
theorem difference_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value leaf : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (countRoom : count+1 ≤ cap.toNat) (locals : LookupLocals source table pointer value leaf)
    (member : valid leaf) (marked : bits leaf = 256) (route : Route bits left right query root leaf)
    (different : keys leaf ≠ query) (eqCell : source.locals.lookup (ofString "eq") = some (.val (.word 0#64)))
    (view : FirstDiff.ByteView source pointer query) (valueMember : ValueOf value) (installed : OriginalCode.Installed source.code)
    (little : source.be = false) (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat)
    (answer : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCompare = (some (.returned answer),post)) :
    answer = .val (.word 0#64) ∧ Result source post table cap count ValueOf := by
  rcases difference_trace source post table cap root pointer value leaf next count valid bits left right keys query ValueOf
    image locals member marked route different eqCell view installed (some (.returned answer)) normal with stopped | reached
  · exact (stopped.2 answer rfl).elim
  · obtain ⟨entry,target,inner,node,parent,data,state,live,strict,suffix,parentLink,frame,forward,cost,called,endpoint⟩ := reached
    have currentImage : Image target table cap root next count valid bits left right keys ValueOf := image.of_frame frame
    have currentLittle := (LocalEffects.endian_of_erase source target frame).trans little
    have currentInstalled : OriginalCode.Installed target.code := by rw [LocalEffects.code_of_erase source target frame]; exact installed
    have inside : KeyBits.first query (keys leaf) < 256 := by have := image.nodes.bitBound node live; omega
    have fresh := Splice.fresh_from_image currentImage live suffix parentLink (KeyBits.first_spec query (keys leaf)) inside strict
    have context : InsertContext target table cap root pointer value node parent next count (KeyBits.first query (keys leaf)) valid bits left right keys query ValueOf :=
      ⟨currentImage,available,countRoom,fresh,parentLink,currentLittle,aligned,beforeTable,view.of_frame frame,valueMember⟩
    obtain ⟨zero,returnedFrame,returnedImage⟩ := fresh_returned context data.locals state currentInstalled answer called
    have innerResult : Result target inner table cap count ValueOf := (inserted_result context).of_frames rfl returnedFrame
    exact ⟨zero,innerResult.of_frames frame (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.difference_returned
