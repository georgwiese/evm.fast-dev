import InitECandidate.Solver.Mpt.ValueEncodedLenNormal
import InitECandidate.Solver.Input.CallPrefixScopedActual

namespace InitECandidate.Solver.Mpt.ValueEncodedLen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real scoped serializer call derives its actual size and complete
read-only caller frame from its present word arguments and execution. -/
theorem scoped_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (expressions : List (ExpHOL 64)) (pointer length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word pointer),.val (.word length)])
    (reached : Input.CallPrefix.Reaches source (.scoped name .one (ofString "rlp_value_encoded_len") expressions) target) :
    ∃ encoded,length.toNat≤encoded ∧ encoded≤length.toNat+9 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      target.locals.lookup name=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧ source.clock-target.clock≤12 := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee actualShape returned childTarget args called funded run checked=>
    have sameValues : actualValues=[.val (.word pointer),.val (.word length)]:=Option.some.inj (args.symm.trans argsRead)
    subst actualValues
    obtain ⟨expected,expectedCall,_pCell,nCell⟩:=environment source.code.lookup pointer length (original_code source.code installed)
    have same:=Option.some.inj (called.symm.trans expectedCall)
    have bodyEq:=congrArg Prod.fst same
    have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
    change actualBody=body at bodyEq
    change callee=expected at mapEq
    change actualShape=.one at shapeEq
    subst actualBody
    subst callee
    subst actualShape
    obtain ⟨encoded,lower,upper,number,answer,price,frame⟩:=body_normal (callEntryStateHOLFinite source expected) childTarget length fits installed nCell returned run
    refine ⟨encoded,lower,upper,number,?_,?_,frame,?_⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
    · intro other different
      simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
    · change source.clock-1-childTarget.clock≤11 at price
      change source.clock-childTarget.clock≤12
      omega

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word pointer),.val (.word length)]) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_value_encoded_len") expressions)).2.clock≤12 := by
  obtain ⟨callee,called,_pCell,nCell⟩:=environment source.code.lookup pointer length (original_code source.code installed)
  have price:=body_cost (callEntryStateHOLFinite source callee) length fits installed nCell
  exact Input.ClockCost.call_current source destination (ofString "rlp_value_encoded_len") expressions _ body callee .one 11 args called price

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word pointer),.val (.word length)]) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "rlp_value_encoded_len") expressions .skip)).2.clock≤12 := by
  obtain ⟨callee,called,_pCell,nCell⟩:=environment source.code.lookup pointer length (original_code source.code installed)
  have price:=body_cost (callEntryStateHOLFinite source callee) length fits installed nCell
  exact Input.ClockCost.scoped_current source name .one (ofString "rlp_value_encoded_len") expressions _ body .skip callee .one 11 0 args called price (Input.ClockCost.skip source.code)

end InitECandidate.Solver.Mpt.ValueEncodedLen

#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.scoped_normal
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.call_cost
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.scoped_cost
