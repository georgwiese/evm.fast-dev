import InitECandidate.Solver.Mpt.NodeRlpBeginBranch
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem branch_tag_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (mapped : source.memaddrs node) (stored : source.memory node=.word 3#64) :
    eval source (nodeField 0)=some (.val (.word 3#64)) := by
  simp [eval,nodeField,evalHOLExact,evalListHOLExact,toExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

/-- The real ignored begin call used by the fill traversal installs all
three zero frame words, preserves other source fields exactly and spends
one caller tick. No completed frame, mapped destination or later finish
success is assumed. -/
theorem branch_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (mapped : source.memaddrs node) (stored : source.memory node=.word 3#64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word frame),.val (.word node)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_begin") arguments)=(none,target)) :
    target={source with clock:=source.clock-1,memory:=storedMemory source.memory frame 0#64 0#64 0#64} ∧
      source.memaddrs (frame+24#64) ∧ source.memaddrs (frame+32#64) ∧ source.memaddrs (frame+40#64) := by
  obtain ⟨callee,called,frameCell,nodeCell⟩:=environment source.code.lookup frame node (original_code source.code installed)
  obtain ⟨funded,childTarget,returned,run⟩:=Input.CallNormal.ignored_callee_return source target (ofString "_node_rlp_begin") arguments _ body callee .one args called normal
  obtain ⟨answer,childFrame,firstMapped,secondMapped,thirdMapped⟩:=branch_normal (callEntryStateHOLFinite source callee) childTarget frame frameCell
    (branch_tag_read (callEntryStateHOLFinite source callee) node nodeCell mapped stored) returned run
  have actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_begin") arguments)=(none,{childTarget with locals:=source.locals}):=by
    rw [evaluateHOLFiniteState_call,args]
    simp only
    rw [called]
    simp only
    rw [if_neg (show source.clock≠0 by omega),run,answer]
    simp [shapeOfHOLExact,shapeEqHOL]
  have endpoint : target={childTarget with locals:=source.locals}:=congrArg Prod.snd (normal.symm.trans actual)
  have restored:=congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>{current with locals:=source.locals}) childFrame
  change {childTarget with locals:=source.locals}={source with clock:=source.clock-1,memory:=storedMemory source.memory frame 0#64 0#64 0#64} at restored
  exact ⟨endpoint.trans restored,firstMapped,secondMapped,thirdMapped⟩

theorem branch_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (mapped : source.memaddrs node) (stored : source.memory node=.word 3#64)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word frame),.val (.word node)]) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "_node_rlp_begin") arguments)).2.clock≤1 := by
  obtain ⟨callee,called,_frameCell,nodeCell⟩:=environment source.code.lookup frame node (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "_node_rlp_begin") arguments _ body callee .one 0 args called
    (branch_cost (callEntryStateHOLFinite source callee) (branch_tag_read (callEntryStateHOLFinite source callee) node nodeCell mapped stored))

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.branch_tag_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.branch_call_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.branch_call_cost
