import InitECandidate.Solver.Input.RequestRootHashData

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

def Description.scratchBytes (data : Description) (budget : Nat) :=
  max (608+data.payload.scratchBytes budget) (max (96*budget+1472) (832+64*data.blobCount))
def cursor (ch : BitVec 64) := ch+128#64

structure Description.RuntimeGeometry (data : Description) (budget : Nat) (ch : BitVec 64) : Prop where
  arena : AllocatedBytes.Arena ch (128+data.scratchBytes budget)
  aligned : ch.toNat%8=0

theorem Description.scratch_bound (data : Description) (lower upper budget : Nat) (layout : data.Layout lower upper budget) :
    data.scratchBytes budget≤96*budget+4800 := by
  have payload := data.payload.scratch_bound lower upper budget layout.payload
  have blobs := layout.blobsBound
  unfold Description.scratchBytes
  omega

/-- One actual original shared roots/scratch layout covers all five phases. -/
theorem Description.common_geometry (data : Description) (budget : Nat) (ch : BitVec 64)
    (geometry : data.RuntimeGeometry budget ch) :
    (cursor ch).toNat=ch.toNat+128 ∧ (cursor ch).toNat%8=0 ∧ AllocatedBytes.Arena (cursor ch) (data.scratchBytes budget) ∧
      AllocatedBytes.Arena ch 256 ∧ (∀ slot<4,AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*slot)) 32) := by
  have size : 1472≤data.scratchBytes budget := by unfold Description.scratchBytes; omega
  have number : (cursor ch).toNat=ch.toNat+128 := byteAddress_toNat ch 128 (by have h:=geometry.arena.upper; omega)
  exact ⟨number,by rw [number]; have h:=geometry.aligned; omega,
    AllocatedBytes.Arena.subrange ch (128+data.scratchBytes budget) 128 _ geometry.arena (by omega),
    AllocatedBytes.Arena.weaken ch _ 256 geometry.arena (by omega),
    fun slot inside=>AllocatedBytes.Arena.subrange ch (128+data.scratchBytes budget) (32*slot) 32 geometry.arena (by omega)⟩

theorem Description.payload_geometry (data : Description) (budget : Nat) (ch : BitVec 64) (geometry : data.RuntimeGeometry budget ch) :
    data.payload.RuntimeGeometry budget (cursor ch) := by
  obtain ⟨number,aligned,arena,rest⟩ := data.common_geometry budget ch geometry
  exact ⟨AllocatedBytes.Arena.weaken _ _ (608+data.payload.scratchBytes budget) arena (Nat.le_max_left _ _),aligned⟩

theorem Description.blob_geometry (data : Description) (budget : Nat) (ch : BitVec 64) (geometry : data.RuntimeGeometry budget ch) :
    AllocatedBytes.Arena (cursor ch) (832+64*data.blobCount) :=
  AllocatedBytes.Arena.weaken _ _ _ (data.common_geometry budget ch geometry).2.2.1
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- Actual request202 arenas and metadata separation follow from the same
input frontier and shared scratch; no future allocator/hash success. -/
theorem Description.request_geometry (data : Description) (lower upper budget : Nat) (ch stp accel chunk : BitVec 64)
    (layout : data.Layout lower upper budget) (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (before : upper≤ch.toNat) :
    RequestsHash.Geometry data.requests (cursor ch) (cursor ch+160#64) data.requestPointer data.requestCount budget ∧
      RequestsHash.Separation data.requests stp accel chunk := by
  obtain ⟨number,aligned,scratch,roots,out⟩ := data.common_geometry budget ch geometry
  have fits : 96*budget+1472≤data.scratchBytes budget := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have nextNumber : (cursor ch+160#64).toNat=(cursor ch).toNat+160 := byteAddress_toNat (cursor ch) 160 (by have h:=scratch.upper; omega)
  refine ⟨⟨layout.payload.budgetBound,layout.requestCounts,layout.requestsArena,layout.requestsAligned,?_,
    AllocatedBytes.Arena.weaken _ _ 160 scratch (by omega),aligned,?_,?_,?_,layout.requestInputs⟩,
    ⟨?_,?_,?_⟩⟩
  · rw [number]; have h:=layout.requestsBefore; omega
  · rw [nextNumber]
  · exact AllocatedBytes.Arena.subrange (cursor ch) (data.scratchBytes budget) 160 (96*budget+1312) scratch (by omega)
  · rw [nextNumber]; omega
  · have a:=separation.state; have b:=layout.requestsLower; omega
  · have a:=separation.accelerator; have b:=layout.requestsLower; omega
  · have a:=separation.lengthChunk; have b:=layout.requestsLower; omega

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.Description.scratch_bound
#print axioms InitECandidate.Solver.Input.RequestRootHash.Description.common_geometry
#print axioms InitECandidate.Solver.Input.RequestRootHash.Description.payload_geometry
#print axioms InitECandidate.Solver.Input.RequestRootHash.Description.blob_geometry
#print axioms InitECandidate.Solver.Input.RequestRootHash.Description.request_geometry
