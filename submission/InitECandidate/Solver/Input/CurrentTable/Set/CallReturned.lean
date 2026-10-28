import InitECandidate.Solver.Input.CurrentTable.Set.Returned
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- A real normal ignored-result htab_set call supplies the next builder
image and preserves its caller's complete local map. -/
theorem call_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (countRoom : count+1 ≤ cap.toNat)
    (view : FirstDiff.ByteView source pointer query) (valueMember : ValueOf value)
    (installed : OriginalCode.Installed source.code) (little : source.be = false)
    (aligned : pointer.toNat%8 = 0) (beforeTable : pointer.toNat+32 ≤ table.toNat)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word table),.val (.word pointer),.val (.word value)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") expressions) = (none,post)) :
    Result source post table cap count ValueOf ∧ post.locals = source.locals := by
  obtain ⟨callee,called,tableCell,keyCell,valueCell⟩ := word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value (by decide) (by decide) (by decide)
    (original_code source.code installed)
  obtain ⟨funded,values,actual,actualCallee,shape,target,answer,read,looked,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htab_set") expressions normal
  have valuesEq := Option.some.inj (read.symm.trans args)
  subst values
  have triple := Option.some.inj (looked.symm.trans called)
  have bodyEq := congrArg Prod.fst triple
  have calleeEq := congrArg (fun row => row.2.1) triple
  change actual = body at bodyEq
  change actualCallee = callee at calleeEq
  rw [bodyEq,calleeEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have currentImage : Image entry table cap root next count valid bits left right keys ValueOf := image.of_frame rfl
  obtain ⟨zero,result⟩ := body_returned entry target table cap root pointer value next count valid bits left right keys query ValueOf
    currentImage available countRoom tableCell keyCell valueCell (view.of_frame rfl) valueMember installed little aligned beforeTable answer bodyRun
  exact ⟨result.of_frames rfl (by rw [endpoint]; rfl),by rw [endpoint]⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.call_returned
