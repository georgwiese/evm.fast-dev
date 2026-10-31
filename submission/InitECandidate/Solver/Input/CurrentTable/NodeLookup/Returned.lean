import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Cost
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.RowsRead
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LookupFrame

namespace InitECandidate.Solver.Input.CurrentTable.NodeLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

def Result (data : NodeBuild.Data) (value : ValueHOL 64) : Prop :=
  value=absentValue ∨ ∃ index<data.total,value=presentValue (data.pointers index) (data.lengths index)

/-- A current node database is its genuine Patricia value image together
with the actual decoded rows. Its input spans are bounded before the table;
no successful query or future allocation is assumed. -/
structure Database (source : PanSemStateFiniteExact 64 Guest.HostMemory) (data : NodeBuild.Data) : Prop where
  image : NodeBuild.ImageUpTo data source data.total
  rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper
  lengths : ∀ index<data.total,(data.lengths index).toNat≤1024
  lower : 2701131776≤data.lower
  before : data.upper≤data.table.toNat

/-- Local/clock changes retain the same physical database. -/
theorem Database.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {data : NodeBuild.Data}
    (database : Database source data) (frame : LocalEffects.erase target=LocalEffects.erase source) : Database target data := by
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bounded⟩:=database.image
  have memory:=LocalEffects.memory_of_erase source target frame
  exact ⟨⟨root,next,count,valid,bits,left,right,keys,image.of_frame frame,bounded⟩,
    database.rows.of_frame source target data.array data.pointers data.lengths data.total data.lower data.upper
      ⟨by intro query lower upper; exact congrFun memory query⟩,
    database.lengths,database.lower,database.before⟩

/-- Real decoder stages preserve the input rows and complete table image
whenever both precede their actual incoming persistent heap. -/
theorem Database.of_before {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {data : NodeBuild.Data}
    (database : Database source data) (heap : Nat)
    (tableBefore : (New.endPointer data.table data.cap).toNat≤heap)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,query.toNat<heap→target.memory query=source.memory query) : Database target data := by
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bounded⟩:=database.image
  have tableEnd : data.table.toNat+88≤(New.endPointer data.table data.cap).toNat:=by
    have a:=image.geometry.tableBefore
    have b:=image.geometry.keysBefore
    have c:=image.geometry.nodesBefore
    have d:=image.geometry.orderBefore
    omega
  exact ⟨database.image.of_interval domain endian (by intro query lower upper; exact memory query (upper.trans_le tableBefore)),
    database.rows.of_frame source target data.array data.pointers data.lengths data.total data.lower data.upper
      ⟨by intro query lower upper; exact memory query (by have before:=database.before; omega)⟩,
    database.lengths,database.lower,database.before⟩

/-- An actual returned lookup row supplies its own bounded ordinary input
span, regardless of alignment/readability of the original query pointer. -/
theorem Database.result {source : PanSemStateFiniteExact 64 Guest.HostMemory} {data : NodeBuild.Data}
    (database : Database source data) {value : ValueHOL 64} (result : Result data value) :
    value=absentValue ∨ ∃ pointer length,value=presentValue pointer length ∧ AllocatedBytes.Arena pointer length.toNat ∧
      length.toNat≤1024 ∧ 2701131776≤pointer.toNat ∧ pointer.toNat+length.toNat≤data.table.toNat := by
  rcases result with absent|⟨index,inside,same⟩
  · exact Or.inl absent
  · exact Or.inr ⟨data.pointers index,data.lengths index,same,database.rows.inputArena index inside,
      database.lengths index inside,database.lower.trans (database.rows.inputAfter index inside),
      (database.rows.inputBefore index inside).trans database.before⟩

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

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.Database.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.Database.of_before
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.Database.result
