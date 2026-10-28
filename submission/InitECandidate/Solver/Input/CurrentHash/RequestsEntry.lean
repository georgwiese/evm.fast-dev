import InitECandidate.Solver.Input.CurrentHash.RequestsProgram
import InitECandidate.Solver.Input.CurrentHash.RequestListCallCost
import InitECandidate.Solver.Input.Requests.DecodedBudget
import InitECandidate.Solver.Input.Witness.LoadedOffsets
import InitECandidate.Solver.Input.ScalarProgram

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem kind_index (kind : RequestList.Kind) : kind.tag<5 := by cases kind <;> decide
theorem kind_size (kind : RequestList.Kind) : (Requests.elementSize kind.tag).toNat=kind.record.length := by cases kind <;> decide

theorem field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rq word : BitVec 64) (offset : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena rq 80) (aligned : rq.toNat%8=0)
    (inside : offset<80) (multiple : offset%8=0)
    (request : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (cell : source.memory (rq+BitVec.ofNat 64 offset)=.word word) : eval source (field offset)=some (.val (.word word)) := by
  have read : eval source (localVar "rq")=some (.val (.word rq)) := by simpa [eval,evalHOLExact,toExact,localVar] using request
  exact Witness.load_word_read source _ _ word (Scalar.plus_read source _ rq offset read)
    (AllocatedBytes.word_mapped source rq 80 offset domain arena inside aligned multiple) cell

theorem output_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) (index : Nat)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) : eval source (outputExpression index)=some (.val (.word (ch+BitVec.ofNat 64 (32*index)))) := by
  by_cases zero : index=0
  · subst index; simp [outputExpression,eval,evalHOLExact,toExact,localVar,chunks]
  · simp [outputExpression,zero,eval,evalHOLExact,evalListHOLExact,toExact,localVar,chunks,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Real RQ loads supply the actual five-word ABI for each parent list call. -/
theorem arguments_read {input : Guest.InputBlob} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq ch : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64) (kind : RequestList.Kind)
    (data : Requests.DecodedImage input source blob rq start size counts) (domain : source.memaddrs=InitE.ordinaryDomain)
    (request : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (arguments kind)=
      some (RequestList.values kind (blob+BitVec.ofNat 64 start+Requests.offsetWord input start kind.tag) (ch+BitVec.ofNat 64 (32*kind.tag)) (counts kind.tag).toNat) := by
  have index := kind_index kind
  have cells := data.image.cells kind.tag index
  have pointerRead := field_read source rq _ (16*kind.tag) domain data.cursorArena data.cursorAligned (by omega) (by omega) request cells.1
  have countRead := field_read source rq _ (16*kind.tag+8) domain data.cursorArena data.cursorAligned (by omega) (by omega) request cells.2
  have outputRead := output_read source ch kind.tag chunks
  simp only [eval] at pointerRead countRead outputRead
  simp only [evalListHOLFinite,arguments,evalListHOLExact,pointerRead,countRead,outputRead,RequestList.values,evalHOLExact,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem input_arena {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob rq : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (data : Requests.DecodedImage input source blob rq start size counts) (kind : RequestList.Kind) :
    AllocatedBytes.Arena (blob+BitVec.ofNat 64 start+Requests.offsetWord input start kind.tag) ((counts kind.tag).toNat*kind.record.length) := by
  simpa only [kind_size kind] using data.list_arena kind.tag (kind_index kind)

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.kind_index
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.kind_size
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.field_read
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.output_read
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.input_arena
