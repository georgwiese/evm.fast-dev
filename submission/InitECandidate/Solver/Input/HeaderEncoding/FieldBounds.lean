import InitECandidate.Solver.Input.HeaderEncoding.FieldPost

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  u256Code : source.code.lookup (ofString "rlp_put_u256")=some (RlpWrite.U256Put.formals,RlpWrite.U256Put.body,.one)
  u256Codes : RlpWrite.U256Put.Codes source
  wordCode : source.code.lookup (ofString "rlp_encode_word")=some (RlpWrite.WordWrite.formals,RlpWrite.WordWrite.body,.one)

def FieldRun (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (buffer : BitVec 64) (field : Field) : Prop :=
  ∃ memory encoded paid,1≤encoded ∧ encoded≤maxSize field ∧ paid≤maxCost field ∧
    evaluateHOLFiniteState source (call field)=(none,bind {source with memory:=memory,clock:=source.clock-paid} "w" (BitVec.ofNat 64 encoded)) ∧
    OldMemory memory original buffer

theorem Geometry.position_arena (header buffer : BitVec 64) (geometry : Geometry header buffer) (position size : Nat)
    (inside : position+size≤1024) : WitnessRadix.AllocatedBytes.Arena (address buffer position) size :=
  WitnessRadix.AllocatedBytes.Arena.subrange buffer 1056 position size (geometry.buffer_arena header buffer) (by omega)

theorem Geometry.position_number (header buffer : BitVec 64) (geometry : Geometry header buffer) (position : Nat) (inside : position≤1024) :
    (address buffer position).toNat=buffer.toNat+position :=
  WitnessRadix.byteAddress_toNat buffer position (by have h:=geometry.room; omega)

theorem Geometry.cursor_number (header buffer : BitVec 64) (geometry : Geometry header buffer) :
    (cursor buffer).toNat=buffer.toNat+1024 := by
  exact geometry.position_number header buffer 1024 (Nat.le_refl _)

theorem bytes_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer pointer old : BitVec 64)
    (field : Field) (position length : Nat) (expressions : List (ExpHOL 64))
    (context : Context source original header buffer) (codes : Codes source)
    (positivePosition : 9≤position) (inside : position+maxSize field≤1024) (small : length≤256)
    (sizeBound : length+9≤maxSize field) (costBound : length+21≤maxCost field)
    (arena : WitnessRadix.AllocatedBytes.Arena pointer length)
    (w : source.locals.lookup (ofString "w")=some (.val (.word old)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some [.val (.word (address buffer position)),.val (.word pointer),.val (.word (BitVec.ofNat 64 length))])
    (shape : call field=.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes") expressions)
    (enough : maxCost field≤source.clock) : FieldRun source original buffer field := by
  classical
  have destination:=context.geometry.position_arena header buffer position (length+9) (by omega)
  obtain ⟨byte,access⟩:=RlpWrite.bytes_access source (address buffer position) pointer length (by omega) context.domain arena destination
  obtain ⟨memory,encoded,paid,lower,encodedPositive,upper,bound,number,run,frame⟩:=RlpWrite.BytesWrite.assign_execute source (address buffer position) pointer old length byte
    "w" expressions w args codes.u256Codes.bytesCode access codes.u256Codes.bytesCodes (by omega)
  have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
  refine ⟨memory,encoded,paid+1,encodedPositive,by omega,by omega,?_,?_⟩
  · rw [shape]
    simpa only [subtract] using run
  · intro query before
    have addressNumber:=context.geometry.position_number header buffer position (by omega)
    have away:=before_away (address buffer position) query (length+9) buffer.toNat destination (by omega) context.geometry.bufferAligned before
    exact (frame query away).trans (context.oldMemory query before)

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.Geometry.position_arena
#print axioms InitECandidate.Solver.Input.HeaderEncoding.Geometry.position_number
#print axioms InitECandidate.Solver.Input.HeaderEncoding.Geometry.cursor_number
#print axioms InitECandidate.Solver.Input.HeaderEncoding.bytes_field
