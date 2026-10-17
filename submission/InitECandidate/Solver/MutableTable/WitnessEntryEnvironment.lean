import InitECandidate.Solver.MutableTable.WitnessBuildContext

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Fixed code/global metadata for witness construction. Decoded array contents,
allocation geometry and per-item size bounds are supplied separately. -/
structure EntryEnvironment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad scratch : BitVec 64) : Prop where
  global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch))
  keccakCode : source.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one)
  environment : Keccak256.Environment source stp pad
  aligned : scratch.toNat%8=0
  little : source.be=false
  hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one)
  copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one)
  insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one)
  memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)
  findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one)
  setCode : source.code.lookup (ofString "htab_set")=some (TableCall.formals,Set.body,.one)

theorem EntryEnvironment.context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (slices : Nat → Graph.Slice) (stp pad scratch : BitVec 64) (maximum : Nat)
    (entry : EntryEnvironment source stp pad scratch)
    (buffers : ∀ index<plan.count,Keccak256.Buffers stp (slices index).1 pad scratch (slices index).2.toNat)
    (before : stp.toNat+200≤plan.records ∧ pad.toNat+136≤plan.records ∧ scratch.toNat+32≤plan.records)
    (lengthBound : ∀ index<plan.count,(slices index).2.toNat≤maximum) : Context source plan slices stp pad scratch maximum :=
  ⟨entry.global,entry.keccakCode,entry.environment,buffers,before,entry.aligned,entry.little,entry.hashCode,entry.copyCode,
    entry.insertCode,entry.memeqCode,entry.findCode,entry.setCode,lengthBound⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.EntryEnvironment.context
