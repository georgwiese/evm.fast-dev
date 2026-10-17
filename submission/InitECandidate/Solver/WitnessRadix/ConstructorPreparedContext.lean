import InitECandidate.Solver.WitnessRadix.ConstructorPrepare
import InitECandidate.Solver.WitnessRadix.ConstructorHashContext

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

theorem prepared_global_other {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) (name : MlS)
    (different : ofString "heap_ptr"≠name) : (preparedState source plan).globals.lookup name=source.globals.lookup name := by
  simp [preparedState,arrayEntry,TableNew.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]

theorem prepared_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan) (stp padScratch : BitVec 64)
    (environment : Keccak256.Environment source stp padScratch) : Keccak256.Environment (preparedState source plan) stp padScratch := by
  constructor
  · exact environment.domain
  · exact (prepared_global_other source plan (ofString "keccak_st") (by decide)).trans environment.stateGlobal
  · exact (prepared_global_other source plan (ofString "keccak_pad") (by decide)).trans environment.scratchGlobal
  · exact environment.zeroCode
  · exact environment.copyCode
  · exact ⟨environment.hashCode.block,environment.hashCode.perm,environment.hashCode.oracleEq⟩

theorem records_before_bases (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (pool : Pool) :
    plan.records≤(base (AllocatedLayout.layout plan) pool).toNat := by
  rw [AllocatedLayout.base_number plan ready pool]
  have before := ready.recordsBefore
  cases pool <;> simp only [AllocatedLayout.baseNat] <;> omega

/-- The real htab_new/array-load preparation preserves every hash code/global
entry fact except the heap cursor. Allocation order gives all pool frames. -/
theorem prepared_hash_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (sliceFor : BitVec 64 → Graph.Slice) (stp padScratch hashScratch : BitVec 64) (maximum : Nat)
    (environment : Keccak256.Environment source stp padScratch)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch)))
    (code : source.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one))
    (buffers : ∀ index<plan.count,Keccak256.Buffers stp (sliceFor (BitVec.ofNat 64 index)).1 padScratch hashScratch (sliceFor (BitVec.ofNat 64 index)).2.toNat)
    (before : stp.toNat+200≤plan.records ∧ padScratch.toNat+136≤plan.records ∧ hashScratch.toNat+32≤plan.records)
    (scratchAligned : hashScratch.toNat%8=0) (little : source.be=false)
    (lengthBound : ∀ index<plan.count,(sliceFor (BitVec.ofNat 64 index)).2.toNat≤maximum) :
    HashContext (preparedState source plan) (AllocatedLayout.layout plan) sliceFor stp padScratch hashScratch maximum := by
  constructor
  · exact (prepared_global_other source plan (ofString "mpt_hash_scratch") (by decide)).trans global
  · exact code
  · exact prepared_environment source plan stp padScratch environment
  · exact buffers
  · intro pool
    have h := records_before_bases plan ready pool
    exact ⟨by omega,by omega,by omega⟩
  · exact scratchAligned
  · exact little
  · exact lengthBound

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prepared_global_other
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prepared_environment
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.records_before_bases
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prepared_hash_context
