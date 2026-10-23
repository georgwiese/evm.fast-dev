import InitECandidate.Solver.Mpt.ValueEncodedLenProgram
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.ValueEncodedLen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpLength

theorem tail_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first length : BitVec 64)
    (fbCell : source.locals.lookup (ofString "fb")=some (.val (.word first)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word first),.val (.word length)] := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,fbCell,nCell]

/-- The actual tail helper call costs at most eleven source ticks for
every outcome, including malformed operand reads and exhaustion. -/
theorem tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (fbCell : source.locals.lookup (ofString "fb")=some (.val (.word first)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length))) :
    source.clock-(evaluateHOLFiniteState source tail).2.clock≤11 := by
  obtain ⟨callee,called,fb,len⟩:=BytesSize.environment source.code.lookup first length (Input.OriginalRlp.rlp_bytes_encoded_len source.code installed)
  have price:=BytesSize.body_cost (callEntryStateHOLFinite source callee) first length fits fb len
    (Input.OriginalRlp.rlp_header_len source.code installed) (Input.OriginalRlp.rlp_be_len source.code installed)
  exact Input.ClockCost.call_current source none (ofString "rlp_bytes_encoded_len") arguments _ BytesSize.body callee .one 10
    (tail_arguments source first length fbCell nCell) called price

/-- The whole original262 value-size helper is priced without requiring
a future successful byte read or callee return. The positive-length
branch must actually continue before any tail facts are used. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤11 := by
  let entered:=bind source "fb" 0#64
  have len : entered.locals.lookup (ofString "n")=some (.val (.word length)):=
    (bind_lookup_other source "fb" "n" 0#64 (by decide)).trans nCell
  have suffix (current : PanSemStateFiniteExact 64 Guest.HostMemory) (run : evaluateHOLFiniteState entered guard=(none,current)) :
      current.clock-(evaluateHOLFiniteState current tail).2.clock≤11:=by
    obtain ⟨first,fb,nextLen,frame⟩:=guard_normal entered current length len (bind_lookup_same _ _ _) run
    have codes:=Input.LocalEffects.code_of_erase entered current frame
    exact tail_cost current first length fits (by rw [codes]; exact installed) fb nextLen
  have price:=Input.ClockCost.sequence_reached_current entered guard tail 0 11 (guard_cost source.code entered rfl) suffix
  rw [body_shape]
  exact Input.ClockCost.declared_current source "fb" (.const 0#64) 0#64 afterFirst 11 rfl price

end InitECandidate.Solver.Mpt.ValueEncodedLen

#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.tail_arguments
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.tail_cost
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.body_cost
