import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Cost
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.RowsRead
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.CurrentTable.NodeLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

def Result (data : NodeBuild.Data) (value : ValueHOL 64) : Prop :=
  value=absentValue ∨ ∃ index<data.total,value=presentValue (data.pointers index) (data.lengths index)

theorem after_get_absent (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rCell : source.locals.lookup (ofString "r")=some Get.absentValue) :
    evaluateHOLFiniteState source afterGet=evaluateHOLFiniteState source absent := by
  have read : eval source (.cmp .equal (.rfield 0 (localVar "r")) (.const 0#64))=some (.val (.word 1#64)) := by
    simp [eval,evalHOLExact,toExact,localVar,rCell,Get.absentValue,wordCmpHOL]
  simp only [eval] at read
  rw [afterGet,evaluateHOLFiniteState_seq_line780,guard,evaluateHOLFiniteState_ite,read]
  simp only [if_neg (show (1#64 : BitVec 64)≠0 from by decide)]
  generalize actual : evaluateHOLFiniteState source absent=output
  obtain ⟨outcome,post⟩ := output
  cases outcome with
  | none =>
    have stopped : NoFallthrough absent := NoFallthrough.returned _
    have no := stopped source
    rw [actual] at no
    exact (no rfl).elim
  | some result => rfl

theorem after_get_present (source : PanSemStateFiniteExact 64 Guest.HostMemory) (row : BitVec 64)
    (rCell : source.locals.lookup (ofString "r")=some (Get.presentValue row)) :
    evaluateHOLFiniteState source afterGet=evaluateHOLFiniteState source present := by
  have read : eval source (.cmp .equal (.rfield 0 (localVar "r")) (.const 0#64))=some (.val (.word 0#64)) := by
    simp [eval,evalHOLExact,toExact,localVar,rCell,Get.presentValue,wordCmpHOL]
  simp only [eval] at read
  rw [afterGet,evaluateHOLFiniteState_seq_line780,guard,evaluateHOLFiniteState_ite,read]
  simp [evaluateHOLFiniteState_skip]

/-- Every genuine database-lookup return is absent or supplies the exact
pointer/length of a real decoded record from the actual table's value set. -/
theorem body_returned (data : NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key)
    (image : Image source table cap root next count valid bits left right keys (NodeBuild.ValueOf data))
    (rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (hashCell : source.locals.lookup (ofString "hash")=some (.val (.word pointer)))
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Result data value ∧ LocalEffects.erase post=LocalEffects.erase source := by
  have physical := body_readonly source.code installed source rfl
  rw [run] at physical
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dbCell,hashCell]
  rw [body_shape] at run
  obtain ⟨target,answer,inner,result,frame,forward,cost,continued,endpoint⟩ := Get.scoped_returned source post table cap root pointer next count valid bits left right keys
    (NodeBuild.ValueOf data) image installed "r" arguments afterGet args value run
  let current := CallNormal.continuationEntry source target "r" answer
  have rCell : current.locals.lookup (ofString "r")=some answer := CallNormal.continuation_lookup_same source target "r" answer
  have memory := LocalEffects.memory_of_erase source current frame
  have currentRows := rows.of_frame source current data.array data.pointers data.lengths data.total data.lower data.upper
    ⟨by intro query lower upper; exact congrFun memory query⟩
  have currentDomain : current.memaddrs=InitE.ordinaryDomain := (congrArg PanSemStateFiniteExact.memaddrs frame).trans image.domain
  refine ⟨?_,physical⟩
  rcases result with absentAnswer|⟨row,answerEq,member⟩
  · rw [absentAnswer] at rCell
    rw [after_get_absent current rCell] at continued
    exact ReturnFacts.returned current _ absentValue (Result data) rfl (Or.inl rfl) inner value continued
  · rw [answerEq] at rCell
    rcases member with ⟨index,inside,rowEq⟩
    rw [rowEq] at rCell
    rw [after_get_present current _ rCell] at continued
    have read := present_read data current index currentRows inside currentDomain rCell
    exact ReturnFacts.returned current _ (presentValue (data.pointers index) (data.lengths index)) (Result data) read
      (Or.inr ⟨index,inside,rfl⟩) inner value continued

end InitECandidate.Solver.Input.CurrentTable.NodeLookup

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.body_returned
