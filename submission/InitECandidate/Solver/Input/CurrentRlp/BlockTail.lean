import InitECandidate.Solver.Input.CurrentRlp.BlockCodes

namespace InitECandidate.Solver.Input.CurrentRlp.BlockLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpLength

/-- Actual release and both real length loops, with the physically decoded
records retained from the preceding actual header return. -/
theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload buffer headerStart : BitVec 64) (txStart txLength wdStart wdCount headerLength : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Block.Data source input pointer array payload txStart txLength wdStart wdCount)
    (installed : OriginalCode.Installed source.code) (headerBound : headerLength≤916)
    (he : source.locals.lookup (ofString "he")=some (HeaderEncoding.encodedPair headerStart headerLength))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (mark : source.locals.lookup (ofString "mark")=some (.val (.word buffer)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (HeaderEncoding.cursor buffer))))
    (enough : tailPrice input txStart txLength wdCount≤source.clock) :
    ∃ target encoded paid,25*wdCount≤encoded ∧ encoded≤817879876+57*wdCount ∧ paid≤tailPrice input txStart txLength wdCount ∧
      (BitVec.ofNat 64 encoded).toNat=encoded ∧ evaluateHOLFiniteState source Block.afterHeader=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite (HeapScope.releasePost {source with clock:=source.clock-paid} buffer) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "mark"]=some [.val (.word buffer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,mark]
  have releaseRun:=HeapScope.release_call_execute source buffer (HeaderEncoding.cursor buffer) [localVar "mark"] args heap
    (HeapScope.release_original_code source.code installed) (by unfold tailPrice at enough; omega)
  let released:=HeapScope.releasePost {source with clock:=source.clock-1} buffer
  have releasedData:=Block.Data.of_fields source released input pointer array payload txStart txLength wdStart wdCount rfl rfl rfl data
  obtain ⟨target,encoded,paid,lower,upper,bound,number,run,frame⟩:=Block.after_release_execute released input pointer array payload headerStart
    txStart txLength wdStart wdCount headerLength domain releasedData (codes released installed) headerBound he pl
    (by change 12*VarList.decodedCount input txStart txLength+43*wdCount+33≤source.clock-1; unfold tailPrice at enough; omega)
  refine ⟨target,encoded,paid+1,lower,upper,by unfold tailPrice at *; omega,number,?_,?_⟩
  · rw [Block.afterHeader,StateSteps.next_sequence source released _ _ releaseRun (by change source.clock-1≤source.clock; omega)]
    exact run
  · change emptyLocalsHOLFinite target=emptyLocalsHOLFinite (HeapScope.releasePost {source with clock:=source.clock-1-paid} buffer) at frame
    have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
    simpa only [subtract] using frame

/-- Every entry clock and outcome of the released block tail is covered. -/
theorem tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload buffer headerStart : BitVec 64) (txStart txLength wdStart wdCount headerLength : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Block.Data source input pointer array payload txStart txLength wdStart wdCount)
    (installed : OriginalCode.Installed source.code) (headerBound : headerLength≤916)
    (he : source.locals.lookup (ofString "he")=some (HeaderEncoding.encodedPair headerStart headerLength))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (mark : source.locals.lookup (ofString "mark")=some (.val (.word buffer)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (HeaderEncoding.cursor buffer)))) :
    source.clock-(evaluateHOLFiniteState source Block.afterHeader).2.clock≤tailPrice input txStart txLength wdCount := by
  by_cases funded : tailPrice input txStart txLength wdCount≤source.clock
  · obtain ⟨target,encoded,paid,lower,upper,bound,number,run,frame⟩:=tail_execute source input pointer array payload buffer headerStart
      txStart txLength wdStart wdCount headerLength domain data installed headerBound he pl mark heap funded
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clock
    rw [run]
    change source.clock-target.clock≤_
    omega
  · omega

/-- True normal tail returns recover the actual nonwrapping length,
withdrawal lower bound, unchanged memory and restored heap metadata. -/
theorem tail_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload buffer headerStart : BitVec 64) (txStart txLength wdStart wdCount headerLength : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Block.Data source input pointer array payload txStart txLength wdStart wdCount)
    (installed : OriginalCode.Installed source.code) (headerBound : headerLength≤916)
    (he : source.locals.lookup (ofString "he")=some (HeaderEncoding.encodedPair headerStart headerLength))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (mark : source.locals.lookup (ofString "mark")=some (.val (.word buffer)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (HeaderEncoding.cursor buffer))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Block.afterHeader=(some (.returned value),target)) :
    ∃ encoded,25*wdCount≤encoded ∧ encoded≤817879876+57*wdCount ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ LocalEffects.erase target=LocalEffects.erase (HeapScope.releasePost source buffer) := by
  let padding:=tailPrice input txStart txLength wdCount
  let padded:={source with clock:=source.clock+padding}
  have paddedData:=Block.Data.of_fields source padded input pointer array payload txStart txLength wdStart wdCount rfl rfl rfl data
  obtain ⟨post,encoded,paid,lower,upper,bound,number,run,frame⟩:=tail_execute padded input pointer array payload buffer headerStart
    txStart txLength wdStart wdCount headerLength domain paddedData installed headerBound he pl mark heap (by change padding≤source.clock+padding; omega)
  have lifted:=panPropsEvaluateAddClockEq Block.afterHeader source (some (.returned value)) target padding ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+padding}=post at endpoint
  rw [←endpoint] at frame
  have physical:=congrArg LocalEffects.erase frame
  exact ⟨encoded,lower,upper,number,answer,physical⟩

end InitECandidate.Solver.Input.CurrentRlp.BlockLength

#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.tail_execute
#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.tail_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.tail_normal
