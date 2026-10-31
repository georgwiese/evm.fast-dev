import InitECandidate.Solver.Input.RlpLength.BytesSizeGeneral
import InitECandidate.Solver.Input.OriginalRlpCodes
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.Input.CallPrefixScopedActual

namespace InitECandidate.Solver.Input.RlpLength.BytesSize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The original scoped byte-size call derives its true encoded length
and full caller frame for arbitrary safe physical sizes. The old input-size
cap is unnecessary for stored compact paths. -/
theorem scoped_normal_exact {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (expressions : List (ExpHOL 64)) (first length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word first),.val (.word length)])
    (reached : Input.CallPrefix.Reaches source (.scoped name .one (ofString "rlp_bytes_encoded_len") expressions) target) :
    ∃ encoded,encoded=encodedLength first length ∧ length.toNat≤encoded ∧ encoded≤length.toNat+9 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      target.locals.lookup name=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧ source.clock-target.clock≤11 := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee actualShape returned childTarget args called funded run checked=>
    have sameValues : actualValues=[.val (.word first),.val (.word length)]:=Option.some.inj (args.symm.trans argsRead)
    subst actualValues
    obtain ⟨expected,expectedCall,firstCell,nCell⟩:=environment source.code.lookup first length (Input.OriginalRlp.rlp_bytes_encoded_len source.code installed)
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
    obtain ⟨encoded,exactCount,lower,upper,number,answer,price,frame⟩:=body_normal_exact (callEntryStateHOLFinite source expected) childTarget first length fits firstCell nCell
      (Input.OriginalRlp.rlp_header_len source.code installed) (Input.OriginalRlp.rlp_be_len source.code installed) returned run
    refine ⟨encoded,exactCount,lower,upper,number,?_,?_,frame,?_⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
    · intro other different
      simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
    · change source.clock-1-childTarget.clock≤10 at price
      change source.clock-childTarget.clock≤11
      omega

theorem scoped_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (expressions : List (ExpHOL 64)) (first length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word first),.val (.word length)])
    (reached : Input.CallPrefix.Reaches source (.scoped name .one (ofString "rlp_bytes_encoded_len") expressions) target) :
    ∃ encoded,length.toNat≤encoded ∧ encoded≤length.toNat+9 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      target.locals.lookup name=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧ source.clock-target.clock≤11 := by
  obtain ⟨encoded,_exactCount,lower,upper,number,cell,kept,frame,price⟩:=scoped_normal_exact name expressions first length fits installed argsRead reached
  exact ⟨encoded,lower,upper,number,cell,kept,frame,price⟩

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word first),.val (.word length)]) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_bytes_encoded_len") expressions)).2.clock≤11 := by
  obtain ⟨callee,called,firstCell,nCell⟩:=environment source.code.lookup first length (Input.OriginalRlp.rlp_bytes_encoded_len source.code installed)
  have price:=body_cost (callEntryStateHOLFinite source callee) first length fits firstCell nCell
    (Input.OriginalRlp.rlp_header_len source.code installed) (Input.OriginalRlp.rlp_be_len source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "rlp_bytes_encoded_len") expressions _ body callee .one 10 args called price

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word first),.val (.word length)]) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "rlp_bytes_encoded_len") expressions .skip)).2.clock≤11 := by
  obtain ⟨callee,called,firstCell,nCell⟩:=environment source.code.lookup first length (Input.OriginalRlp.rlp_bytes_encoded_len source.code installed)
  have price:=body_cost (callEntryStateHOLFinite source callee) first length fits firstCell nCell
    (Input.OriginalRlp.rlp_header_len source.code installed) (Input.OriginalRlp.rlp_be_len source.code installed)
  exact Input.ClockCost.scoped_current source name .one (ofString "rlp_bytes_encoded_len") expressions _ body .skip callee .one 10 0 args called price (Input.ClockCost.skip source.code)

end InitECandidate.Solver.Input.RlpLength.BytesSize

#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.scoped_normal
#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.call_cost
#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.scoped_cost

#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.scoped_normal_exact
