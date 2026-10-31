import InitECandidate.Solver.Mpt.NodeRlpBeginNormal
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString
open KeyToNibbles (writeMetadata)

def Entry.call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property) (callee : HolFiniteMapExact MlS (ValueHOL 64)) :
    Entry (callEntryStateHOLFinite source callee) node heap lower limit property :={
  graph:=data.graph,member:=data.member,active:=data.active,nonHash:=data.nonHash,values:=data.values,regions:=data.regions
  heapCell:=data.heapCell,heapLower:=data.heapLower,heapUpper:=data.heapUpper,heapAligned:=data.heapAligned,domain:=data.domain }

/-- The real ignored begin call used by260 derives its actual frame
descriptors, heap update, older-word frame and restored caller locals from
the current graph and arguments, with one caller tick added. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (valueFits : limit+19≤2^63) (installed : Input.OriginalCode.Installed source.code)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word frame),.val (.word node)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_begin") arguments)=(none,target)) :
    target.locals=source.locals ∧ Nonempty (Output source target node heap frame limit (.val (.word 0#64)) (bodyAllowance source.memory node+1)) := by
  obtain ⟨callee,called,frameCell,nodeCell⟩:=environment source.code.lookup frame node (original_code source.code installed)
  obtain ⟨funded,childTarget,returned,run⟩:=Input.CallNormal.ignored_callee_return source target (ofString "_node_rlp_begin") arguments _ body callee .one args called normal
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨output⟩:=body_normal entry childTarget node heap frame lower limit property (data.call source node heap lower limit property callee)
    valueFits installed nodeCell frameCell returned run
  have actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_begin") arguments)=(none,{childTarget with locals:=source.locals}):=by
    rw [evaluateHOLFiniteState_call,args]
    simp only
    rw [called]
    simp only
    rw [if_neg (show source.clock≠0 by omega),run,output.answer]
    simp [shapeOfHOLExact,shapeEqHOL]
  have endpoint : target={childTarget with locals:=source.locals}:=congrArg Prod.snd (normal.symm.trans actual)
  have baseMetadata : writeMetadata (preparationBase entry node heap)=writeMetadata (preparationBase source node heap):=by
    have tagEq : wordAt entry.memory node=wordAt source.memory node:=rfl
    by_cases branch : wordAt source.memory node=3#64
    · simp only [preparationBase,tagEq,if_pos branch]
      rfl
    · simp only [preparationBase,tagEq,if_neg branch]
      rfl
  rw [endpoint]
  refine ⟨rfl,⟨{
    buffer:=output.buffer,length:=output.length,payload:=output.payload,answer:=rfl
    bufferStored:=output.bufferStored,lengthStored:=output.lengthStored,payloadStored:=output.payloadStored,mapped:=output.mapped
    branch:=output.branch,path:=output.path,fields:=output.fields.trans baseMetadata,older:=output.older,outside:=output.outside
    price:=?_ }⟩⟩
  have price:=output.price
  change source.clock-1-childTarget.clock≤bodyAllowance source.memory node at price
  change source.clock-childTarget.clock≤bodyAllowance source.memory node+1
  omega

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (valueFits : limit+19≤2^63) (installed : Input.OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word frame),.val (.word node)]) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "_node_rlp_begin") arguments)).2.clock≤bodyAllowance source.memory node+1 := by
  obtain ⟨callee,called,_frameCell,nodeCell⟩:=environment source.code.lookup frame node (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "_node_rlp_begin") arguments _ body callee .one (bodyAllowance source.memory node) args called
    (body_cost (callEntryStateHOLFinite source callee) node heap lower limit property (data.call source node heap lower limit property callee) valueFits installed nodeCell)

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Entry.call
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.call_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.call_cost
