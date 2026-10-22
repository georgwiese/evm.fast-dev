import InitECandidate.Solver.Mpt.StateInitNormal

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The original hash workspace pointers, helper code and oracle function
survive the complete actual initializer, despite its other global updates. -/
theorem Output.hash_environment (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes stp pad : BitVec 64) (output : Output input source post workspace nodes rootHash codes)
    (environment : Keccak256.Environment source stp pad) : Keccak256.Environment post stp pad := by
  obtain ⟨installed,scalars,scratch,globals,code,domain,endian,oracle,rest⟩:=output
  exact {
    domain:=domain.trans environment.domain
    stateGlobal:=(globals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans environment.stateGlobal
    scratchGlobal:=(globals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans environment.scratchGlobal
    zeroCode:=by rw [code]; exact environment.zeroCode
    copyCode:=by rw [code]; exact environment.copyCode
    hashCode:=⟨by rw [code]; exact environment.hashCode.block,
      by rw [code]; exact environment.hashCode.perm,oracle.trans environment.hashCode.oracleEq⟩ }

/-- The actual final heap lies beyond the workspace, decoded trie and all
initializer allocations. Retain this separation for later fresh headers. -/
theorem Output.heap_geometry (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes : BitVec 64) (output : Output input source post workspace nodes rootHash codes) :
    ∃ heap,post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 0 ∧ heap.toNat%8=0 ∧ workspace.toNat+40≤heap.toNat := by
  obtain ⟨installed,scalars,scratch,globals,code,domain,endian,oracle,heap,root,storage,heapCell,arena,aligned,view,frozen,table,bs,
    registry,member,regions,block,older,workspaceBefore⟩:=output
  exact ⟨heap,heapCell,arena,aligned,workspaceBefore⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.Output.hash_environment
#print axioms InitECandidate.Solver.Mpt.StateInit.Output.heap_geometry
