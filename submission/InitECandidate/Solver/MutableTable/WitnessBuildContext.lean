import InitECandidate.Solver.MutableTable.WitnessBuildRecordStep

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (maximum : Nat) : Prop where
  global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch))
  keccakCode : source.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one)
  environment : Keccak256.Environment source stp pad
  buffers : ∀ i<plan.count,Keccak256.Buffers stp (slices i).1 pad scratch (slices i).2.toNat
  before : stp.toNat+200≤plan.records ∧ pad.toNat+136≤plan.records ∧ scratch.toNat+32≤plan.records
  aligned : scratch.toNat%8=0
  little : source.be=false
  hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one)
  copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one)
  insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one)
  memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)
  findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one)
  setCode : source.code.lookup (ofString "htab_set")=some (TableCall.formals,Set.body,.one)
  lengthBound : ∀ i<plan.count,(slices i).2.toNat≤maximum

theorem Context.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (maximum : Nat)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source)
    (context : Context source plan slices stp pad scratch maximum) : Context target plan slices stp pad scratch maximum := by
  have globals : target.globals=source.globals:=congrArg (fun state=>state.globals) control
  have codes : target.code=source.code:=congrArg (fun state=>state.code) control
  have endian : target.be=source.be:=congrArg (fun state=>state.be) control
  refine ⟨?_,?_,Keccak256.Environment.of_control source target stp pad control context.environment,context.buffers,context.before,
    context.aligned,?_,?_,?_,?_,?_,?_,?_,context.lengthBound⟩
  · rw [globals];exact context.global
  · rw [codes];exact context.keccakCode
  · exact endian.trans context.little
  · rw [codes];exact context.hashCode
  · rw [codes];exact context.copyCode
  · rw [codes];exact context.insertCode
  · rw [codes];exact context.memeqCode
  · rw [codes];exact context.findCode
  · rw [codes];exact context.setCode

theorem recordPrice_mono (length maximum index count : Nat) (lengthBound : length≤maximum) (indexBound : index≤count) :
    recordPrice length index≤recordPrice maximum count := by
  unfold recordPrice Keccak256.price
  omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Context.of_control
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.recordPrice_mono
