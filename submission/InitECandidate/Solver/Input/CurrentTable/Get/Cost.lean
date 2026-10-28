import InitECandidate.Solver.Input.CurrentTable.Get.TailCost
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Every actual original32-byte lookup costs≤263body ticks. Mapping or
contents of the incoming query buffer and successful reads are not premises. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤263 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) lookupArguments=
      some [.val (.word table),.val (.word pointer)] := by
    simp [lookupArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,tableCell,keyCell]
  rw [body_shape] at run
  rcases FindLeaf.scoped_trace source post table pointer (New.nodesPointer table cap) root valid bits left right
    image.lookup_context installed "leaf" lookupArguments afterLeaf args outcome run with stopped|reached
  · exact Nat.le_trans stopped.1 (by omega)
  · obtain ⟨target,leaf,inner,found,frame,forward,cost,continued,endpoint⟩ := reached
    let current := CallNormal.continuationEntry source target "leaf" (.val (.word leaf))
    have currentImage : Image current table cap root next count valid bits left right keys ValueOf := image.of_frame frame
    have currentTable := (CallNormal.continuation_lookup_other source target "leaf" "t" (.val (.word leaf)) (by decide)).trans tableCell
    have currentKey := (CallNormal.continuation_lookup_other source target "leaf" "key" (.val (.word leaf)) (by decide)).trans keyCell
    have currentLeaf := CallNormal.continuation_lookup_same source target "leaf" (.val (.word leaf))
    have currentCode : OriginalCode.Installed current.code := by rw [LocalEffects.code_of_erase source current frame]; exact installed
    have tailPrice := after_leaf_cost currentImage currentTable currentKey currentLeaf currentCode
    rw [continued] at tailPrice
    change target.clock-inner.clock≤5 at tailPrice
    have postClock : post.clock=inner.clock := by rw [endpoint]; rfl
    rw [postClock]
    omega

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=
      some [.val (.word table),.val (.word pointer)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htab_get") expressions)).2.clock≤264 := by
  obtain ⟨callee,called,tableCell,keyCell⟩ := word_pair_environment source.code.lookup (ofString "htab_get") (ofString "t") (ofString "key")
    body resultShape table pointer (by decide) (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have price := body_cost entry (evaluateHOLFiniteState entry body).2 table cap root pointer next count valid bits left right keys ValueOf
    (image.of_frame rfl) tableCell keyCell installed (evaluateHOLFiniteState entry body).1 rfl
  exact ClockCost.call_current source destination (ofString "htab_get") expressions _ body callee resultShape 263 args called price

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.body_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Get.call_cost
