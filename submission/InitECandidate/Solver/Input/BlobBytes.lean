import InitECandidate.Solver.Input.BlobExecute
import InitECandidate.Solver.Input.CopyBytes

namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact byte correspondence over the encoded input extent. This does not
replace the encoded extent with the arbitrary mathematical list's length. -/
def HeapInput (state : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64) : Prop :=
  ∀ offset<input.length%2^64,
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address=>Classical.propDecidable (state.memaddrs address)) state.be
      (pointer+BitVec.ofNat 64 offset)=some (Framing.convert ((input[offset]?).getD 0))

/-- Complete actual input_blob execution, exact copied bytes for the decoder,
and a uniform 16,777,215 source-clock ceiling on the successful copy path. -/
theorem execute_bytes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (lower : 2701131776≤pointer.toNat) (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (aligned : pointer.toNat%8=0) (little : source.be=false)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (oracleEq : source.ffi.oracle=InitE.sourceOracle) (host : source.ffi.ffiState=Guest.guestHostMemory input)
    (ordinary : source.memaddrs=InitE.ordinaryDomain) (shared : source.shMemaddrs=InitE.sharedDomain)
    (enough : copyRounds (input.length%2^64)+1≤source.clock) :
    ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source body=(some (.returned (pair pointer (input.length%2^64))),target) ∧
      target.clock=source.clock-(copyRounds (input.length%2^64)+1) ∧
      source.clock-target.clock≤16777215 ∧ HeapInput target input pointer := by
  classical
  obtain ⟨target,run,clock,globals,hostAfter,oracleAfter,memory,domain,endian⟩:=
    execute source input pointer bounded lower upper aligned heapGlobal allocCode oracleEq host ordinary shared enough
  refine ⟨target,run,clock,?_,?_⟩
  · have fit:=copyRounds_fit (input.length%2^64) bounded
    omega
  · intro offset inside
    rw [memory,domain,endian]
    have fit:=copyRounds_fit (input.length%2^64) bounded
    exact walk_byte (copyEntry (prepared source input pointer)) input pointer (input.length%2^64) offset
      bounded (by omega) lower upper aligned little ordinary host

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.execute_bytes
