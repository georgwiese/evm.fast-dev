import InitECandidate.Solver.Input.CurrentTable.Get.Returned
import InitECandidate.Solver.Input.CurrentTable.Get.Cost
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The original two-word lookup caller either stops within264ticks or
resumes with the genuine absent/stored-value result and full physical frame. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (installed : OriginalCode.Installed source.code) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=
      some [.val (.word table),.val (.word pointer)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "htab_get") expressions continuation)=(outcome,post)) :
    (source.clock-post.clock≤264 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ target value inner,
      Result ValueOf value ∧ LocalEffects.erase target=LocalEffects.erase source ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤264 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(outcome,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,tableCell,keyCell⟩ := word_pair_environment source.code.lookup (ofString "htab_get") (ofString "t") (ofString "key")
    body resultShape table pointer (by decide) (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have entryImage : Image entry table cap root next count valid bits left right keys ValueOf := image.of_frame rfl
  have price := body_cost entry (evaluateHOLFiniteState entry body).2 table cap root pointer next count valid bits left right keys ValueOf
    entryImage tableCell keyCell installed (evaluateHOLFiniteState entry body).1 rfl
  rcases CallNormal.scoped_classified source post name resultShape (ofString "htab_get") expressions _ body continuation callee resultShape
    263 args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨result,frame⟩ := body_returned entry target table cap root pointer next count valid bits left right keys ValueOf entryImage tableCell keyCell installed value bodyRun
    exact Or.inr ⟨target,value,inner,result,frame,forward,cost,continued,endpoint⟩

theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (installed : OriginalCode.Installed source.code) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=
      some [.val (.word table),.val (.word pointer)]) (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "htab_get") expressions continuation)=(some (.returned returned),post)) :
    ∃ target value inner,Result ValueOf value ∧ LocalEffects.erase target=LocalEffects.erase source ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤264 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  rcases scoped_trace source post table cap root pointer next count valid bits left right keys ValueOf image installed name expressions continuation args
    (some (.returned returned)) run with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · exact reached

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.scoped_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.Get.scoped_returned
