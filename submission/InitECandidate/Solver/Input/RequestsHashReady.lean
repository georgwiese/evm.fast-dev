import InitECandidate.Solver.Input.RequestsHashProgram

namespace InitECandidate.Solver.Input.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The ten original decoded request pointer/count cells, with no digest
contents or future execution included. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rq : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) : Prop where
  fields : ∀ kind,source.memory (rq+BitVec.ofNat 64 (16*kind.tag))=.word (pointers kind) ∧
    source.memory (rq+BitVec.ofNat 64 (16*kind.tag+8))=.word (BitVec.ofNat 64 (counts kind))

structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rq ch out cursor stp accel chunk zeros : BitVec 64)
    (pointers : Kind→BitVec 64) (counts : Kind→Nat) : Prop where
  workspace : SszHash.Workspace source stp accel chunk zeros
  requests : source.locals.lookup (ofString "rq")=some (.val (.word rq))
  chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  image : Image source rq pointers counts
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))

structure Geometry (rq ch cursor : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat) : Prop where
  bounded : capacity≤134217728
  countsBound : ∀ kind,counts kind≤capacity
  requestsArena : AllocatedBytes.Arena rq 80
  requestsAligned : rq.toNat%8=0
  requestsBefore : rq.toNat+80≤ch.toNat
  rootsArena : AllocatedBytes.Arena ch 160
  rootsAligned : ch.toNat%8=0
  rootsBefore : ch.toNat+160≤cursor.toNat
  temporaryArena : AllocatedBytes.Arena cursor (96*capacity+1312)
  aligned : cursor.toNat%8=0
  inputs : ∀ kind,AllocatedBytes.Arena (pointers kind) (counts kind*kind.record.length)

/-- Separation of the initialized mutable SHA buffers from the real
request metadata. This contains no metadata values or preservation claim. -/
structure Separation (rq stp accel chunk : BitVec 64) : Prop where
  state : stp.toNat+64≤rq.toNat
  accelerator : accel.toNat+96≤rq.toNat
  lengthChunk : chunk.toNat+32≤rq.toNat

theorem Separation.at_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq stp accel chunk zeros : BitVec 64) (offset : Nat) (inside : offset<80)
    (workspace : SszHash.Workspace source stp accel chunk zeros) (arena : AllocatedBytes.Arena rq 80)
    (separation : Separation rq stp accel chunk) : SszHash.Protected source stp accel chunk zeros (rq+BitVec.ofNat 64 offset) := by
  have number : (rq+BitVec.ofNat 64 offset).toNat=rq.toNat+offset := byteAddress_toNat rq offset (by have h:=arena.upper; omega)
  refine ⟨workspace,?_,?_,?_⟩
  · exact CopyGeneral.Away.before stp _ 64 rq.toNat separation.state rq.isLt (by rw [number]; omega)
  · exact CopyGeneral.Away.before accel _ 96 rq.toNat separation.accelerator rq.isLt (by rw [number]; omega)
  · exact CopyGeneral.Away.before chunk _ 32 rq.toNat separation.lengthChunk rq.isLt (by rw [number]; omega)

/-- Read the actual original load expressions from those current ten cells. -/
theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (rq ch out cursor stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (arguments kind)=
      some (RequestListHash.values kind (pointers kind) (counts kind) (ch+BitVec.ofNat 64 (32*kind.tag))) := by
  have tagBound := tag_bound kind
  have pointerMapped := AllocatedBytes.word_mapped source rq 80 (16*kind.tag) ready.workspace.sha.domain geometry.requestsArena (by omega) geometry.requestsAligned (by omega)
  have countMapped := AllocatedBytes.word_mapped source rq 80 (16*kind.tag+8) ready.workspace.sha.domain geometry.requestsArena (by omega) geometry.requestsAligned (by omega)
  change source.memaddrs (rq+BitVec.ofNat 64 (16*kind.tag)) at pointerMapped
  change source.memaddrs (rq+BitVec.ofNat 64 (16*kind.tag+8)) at countMapped
  have pointerRead : eval source (.load .one (.op .add [localVar "rq",.const (BitVec.ofNat 64 (16*kind.tag))]))=some (.val (.word (pointers kind))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,ready.requests,valueIsWord,valueWord,wordOpHOL,wordOp,isWfShapeExactHOL,memLoadHOLExact,pointerMapped,(ready.image.fields kind).1]
  have countRead : eval source (.load .one (.op .add [localVar "rq",.const (BitVec.ofNat 64 (16*kind.tag+8))]))=some (.val (.word (BitVec.ofNat 64 (counts kind)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,ready.requests,valueIsWord,valueWord,wordOpHOL,wordOp,isWfShapeExactHOL,memLoadHOLExact,countMapped,(ready.image.fields kind).2]
  have outputRead : eval source (outputExpression kind)=some (.val (.word (ch+BitVec.ofNat 64 (32*kind.tag)))) := by
    by_cases zero : kind.tag=0
    · simp [eval,outputExpression,zero,evalHOLExact,toExact,localVar,ready.chunks]
    · simp [eval,outputExpression,zero,evalHOLExact,evalListHOLExact,toExact,localVar,ready.chunks,valueIsWord,valueWord,wordOpHOL,wordOp]
  simp only [eval] at pointerRead countRead outputRead
  simp only [evalListHOLFinite,arguments,evalListHOLExact,pointerRead,countRead,outputRead,RequestListHash.values]
  rfl

theorem step_geometry (rq ch cursor : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (geometry : Geometry rq ch cursor pointers counts capacity) (kind : Kind) :
    AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*kind.tag)) 32 ∧ AllocatedBytes.Arena cursor (96*counts kind+1312) :=
  ⟨AllocatedBytes.Arena.subrange ch 160 (32*kind.tag) 32 geometry.rootsArena (by have h:=tag_bound kind; omega),
    AllocatedBytes.Arena.weaken cursor (96*capacity+1312) _ geometry.temporaryArena (by have h:=geometry.countsBound kind; omega)⟩

/-- Every actual non-timeout original list call is charged by its actual
kind/count, including failures in its observed prefix. -/
theorem step_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (rq ch out cursor stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (step kind)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤RequestListHash.price kind (counts kind)+1 := by
  obtain ⟨outArena,temporary⟩ := step_geometry rq ch cursor pointers counts capacity geometry kind
  exact RequestListHash.call_cost source post kind (pointers kind) cursor (ch+BitVec.ofNat 64 (32*kind.tag)) stp accel chunk zeros (counts kind)
    (by have a:=geometry.countsBound kind; have b:=geometry.bounded; omega) ready.workspace ready.heap (geometry.inputs kind) temporary geometry.aligned outArena
    (some none) (arguments kind) (arguments_read source kind rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry) result run notTimeout

end InitECandidate.Solver.Input.RequestsHash

#print axioms InitECandidate.Solver.Input.RequestsHash.Separation.at_metadata
#print axioms InitECandidate.Solver.Input.RequestsHash.arguments_read
#print axioms InitECandidate.Solver.Input.RequestsHash.step_geometry
#print axioms InitECandidate.Solver.Input.RequestsHash.step_cost
