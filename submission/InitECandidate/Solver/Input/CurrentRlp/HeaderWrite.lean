import InitECandidate.Solver.Input.CurrentRlp.BeLength
import InitECandidate.Solver.Input.CurrentRlp.PutBe
import InitECandidate.Solver.Input.RlpWrite.HeaderWriteCall
import InitECandidate.Solver.Input.ByteStoreFrame
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostCurrentGuard

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch RlpWrite

abbrev body:=Code.body .writeHeader

theorem current_body : body=RlpWrite.HeaderWrite.body:=rfl

theorem short_cost (code) (tag : ExpHOL 64) : ClockCost.Bound code (shortForm tag) 0 :=
  ClockCost.sequence code _ _ 0 0 (ClockCost.store_byte code _ _) (ClockCost.returned code _)

theorem short_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : ExpHOL 64) :
    (evaluateHOLFiniteState source (shortForm tag)).1≠none := by
  rw [shortForm,evaluateHOLFiniteState_seq_line780]
  generalize stored : evaluateHOLFiniteState source (.storeByte (localVar "dst") tag)=output
  obtain ⟨result,current⟩:=output
  cases result with
  | none=>simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  | some result=>simp

/-- The tag store may fail; only an actual normal store supplies the real
caller state for the following reverse-byte writer. -/
theorem length_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64) (count : Nat)
    (parameter : String) (tag : ExpHOL 64) (small : count≤8) (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word word)))
    (ll : source.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count)))) :
    source.clock-(evaluateHOLFiniteState source (lengthTail parameter tag)).2.clock≤count+1 := by
  have dstRead : eval source (localVar "dst")=some (.val (.word dst)):=by simpa only [eval,evalHOLExact,toExact,localVar] using d
  rw [lengthTail]
  have price:=ClockCost.sequence_reached_current source (.storeByte (localVar "dst") tag)
    (.seq (.call (some (none,none)) (ofString "rlp_put_be") [.op .add [localVar "dst",.const 1#64],localVar parameter,localVar "ll"]) RlpLength.returnOnePlus)
    0 (count+1) (ClockCost.store_byte source.code _ _ source rfl) (by
      intro current normal
      have frame:=byte_store_normal_frame source current (localVar "dst") tag dst dstRead normal
      have currentD : current.locals.lookup (ofString "dst")=some (.val (.word dst)):=by rw [frame.1]; exact d
      have currentV : current.locals.lookup (ofString parameter)=some (.val (.word word)):=by rw [frame.1]; exact v
      have currentLl : current.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=by rw [frame.1]; exact ll
      have currentInstalled : OriginalCode.Installed current.code:=by rw [frame.1]; exact installed
      have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address))
          [.op .add [localVar "dst",.const 1#64],localVar parameter,localVar "ll"]=
          some [.val (.word (dst+1#64)),.val (.word word),.val (.word (BitVec.ofNat 64 count))]:=by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentD,currentV,currentLl,valueIsWord,valueWord,wordOpHOL,wordOp]
      have callPrice:=CurrentRlp.PutBe.call_cost current _ (dst+1#64) word (BitVec.ofNat 64 count) currentInstalled args
      have number : (BitVec.ofNat 64 count).toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      rw [number] at callPrice
      exact ClockCost.sequence_current current _ RlpLength.returnOnePlus (count+1) 0 callPrice (ClockCost.returned current.code _))
  simpa only [Nat.zero_add] using price

/-- The genuine current length-helper result bounds the long form. Neither
readable output nor any future successful put_be call is assumed. -/
theorem long_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (parameter : String) (tag : ExpHOL 64) (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word word)))
    (dstNe : ofString "ll"≠ofString "dst") (parameterNe : ofString "ll"≠ofString parameter) :
    source.clock-(evaluateHOLFiniteState source (longForm parameter tag)).2.clock≤18 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar parameter]=some [.val (.word word)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,v]
  obtain ⟨callee,called,valueCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_be_len") "v" BeLength.body word (BeLength.original_code source.code installed)
  rw [longForm]
  apply ClockCost.scoped_reached_current source "ll" .one (ofString "rlp_be_len") [localVar parameter] _ BeLength.body (lengthTail parameter tag) callee .one 8 9 args called
    (BeLength.body_cost (callEntryStateHOLFinite source callee) word valueCell)
  intro built returned run checked
  obtain ⟨count,bounded,answer,price,frame⟩:=BeLength.body_normal (callEntryStateHOLFinite source callee) built word valueCell returned run
  let ready:=CallNormal.continuationEntry source built "ll" returned
  have currentD : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (CallNormal.continuation_lookup_other source built "ll" "dst" returned dstNe).trans d
  have currentV : ready.locals.lookup (ofString parameter)=some (.val (.word word)):=
    (CallNormal.continuation_lookup_other source built "ll" parameter returned parameterNe).trans v
  have currentLl : ready.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=by
    rw [CallNormal.continuation_lookup_same,answer]
  have code:=LocalEffects.code_of_erase (callEntryStateHOLFinite source callee) built frame
  have cost:=length_tail_cost ready dst word count parameter tag bounded (by change OriginalCode.Installed built.code; rw [code]; exact installed) currentD currentV currentLl
  change built.clock-(evaluateHOLFiniteState ready (lengthTail parameter tag)).2.clock≤9
  change built.clock-(evaluateHOLFiniteState ready (lengthTail parameter tag)).2.clock≤count+1 at cost
  omega

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word word))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤18 := by
  rw [current_body,RlpWrite.HeaderWrite.body_shape]
  simpa only [Nat.max_eq_right (show 0≤18 by omega)] using
    ClockCost.stopping_guard_current source RlpWrite.HeaderWrite.condition (shortForm RlpWrite.HeaderWrite.shortTag) (longForm "n" RlpWrite.HeaderWrite.longTag) 0 18
      (short_stops source RlpWrite.HeaderWrite.shortTag) (short_cost source.code _ source rfl)
      (long_cost source dst word "n" RlpWrite.HeaderWrite.longTag installed d n (by decide) (by decide))


theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_write_header")=some (RlpWrite.HeaderWrite.formals,body,.one) := by
  have known:=Code.installed code installed .writeHeader
  simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_write_header,RlpWrite.HeaderWrite.formals,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using known

/-- The fixed current ABI adds one caller tick to the all-outcome18-tick
body allowance, with no mapped-output or successful-call premise. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst base word : BitVec 64) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word dst),.val (.word base),.val (.word word)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_write_header") arguments)).2.clock≤19 := by
  obtain ⟨callee,called,dCell,bCell,nCell⟩:=RlpWrite.HeaderWrite.environment source.code.lookup dst base word (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "rlp_write_header") arguments _ body callee .one 18 args called
    (body_cost (callEntryStateHOLFinite source callee) dst word installed dCell nCell)

end InitECandidate.Solver.Input.CurrentRlp.HeaderWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.short_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.short_stops
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.length_tail_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.long_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.body_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.call_cost
