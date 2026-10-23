import InitECandidate.Solver.Mpt.NibbleKeySecureAllocation
import InitECandidate.Solver.WitnessRadix.Keccak256CurrentCall
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem secure_hash_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key hash : BitVec 64) (length : Nat)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) hashArguments=some (Keccak256.values key hash length) := by
  simp [hashArguments,Keccak256.values,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,keyCell,lengthCell,hashCell]

/-- Whole actual secure key helper: genuine Keccak call, real fresh
allocation and conversion of its32 output bytes. The original unsecured
suffix is not run after that return. The control frame allows the real
hash event append; its protected-word frame excludes actual workspaces. -/
theorem secured_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m flag key stp pad hash heap : BitVec 64) (length : Nat) (small : length≤32)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word flag) (nonzero : flag≠0#64)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (data : Keccak256.EntryData source stp key pad hash length)
    (hashArena : AllocatedBytes.Arena hash 32) (before : hash.toNat+32≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    AllocatedBytes.Arena heap 64 ∧ value=output heap 32 ∧ TrieWalk.KeyView target.memory target.memaddrs target.be heap 64 ∧
      source.clock-target.clock≤Keccak256.price length+11 ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (PersistentAlloc.post source heap 64#64) ∧
      ∀ query : BitVec 64,Keccak256.Protected stp pad hash query→
        (query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat)→target.memory query=source.memory query := by
  rw [secured_run source m flag mCell mapped cell nonzero,secure_shapes.1] at normal
  obtain ⟨hashed,hashRun,allocatedRun⟩:=Input.sequence_returned source target hashCall secureAllocation value
    (Input.NoReturn.ignored_call (ofString "keccak256") hashArguments source) normal
  have args:=secure_hash_arguments source key hash length keyCell lengthCell hashCell
  obtain ⟨_locals,_upper,lower,control,hashMemory⟩:=Keccak256.call_normal source hashed hashArguments stp key pad hash length args
    (Keccak256.original_code source.code installed) data (by omega) hashRun
  have globalsEq : hashed.globals=source.globals:=by
    have projected:=congrArg PanSemStateFiniteExact.globals control
    exact projected
  have domainEq : hashed.memaddrs=source.memaddrs:=by
    have projected:=congrArg PanSemStateFiniteExact.memaddrs control
    exact projected
  have codeEq : hashed.code=source.code:=by
    have projected:=congrArg PanSemStateFiniteExact.code control
    exact projected
  have endianEq : hashed.be=source.be:=by
    have projected:=congrArg PanSemStateFiniteExact.be control
    exact projected
  obtain ⟨arena,answer,view,cost,fields,memory⟩:=secure_allocation_normal hashed target hash heap (by rw [codeEq]; exact installed)
    (domainEq.trans domain) (endianEq.trans little) (by rw [globalsEq]; exact hashCell) hashArena before (by rw [globalsEq]; exact heapCell) frontier aligned value allocatedRun
  have allocationControl : KeccakAbsorb.hashControl (PersistentAlloc.post hashed heap 64#64)=KeccakAbsorb.hashControl (PersistentAlloc.post source heap 64#64):=by
    have changed:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>PersistentAlloc.post state heap 64#64) control
    exact changed
  have finalControl:=KeccakAbsorb.hashControl_of_control (PersistentAlloc.post hashed heap 64#64) target fields
  exact ⟨arena,answer,view,(by omega),finalControl.trans allocationControl,
    fun query safe outside=>(memory query outside).trans (hashMemory query safe)⟩

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.secure_hash_arguments
#print axioms InitECandidate.Solver.Mpt.NibbleKey.secured_normal
