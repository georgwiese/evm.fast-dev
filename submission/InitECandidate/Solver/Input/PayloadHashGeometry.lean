import InitECandidate.Solver.Input.PayloadHashData

namespace InitECandidate.Solver.Input.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

def Description.scratchBytes (data : Description) (budget : Nat) :=
  4096+96*data.transactionCount+96*data.withdrawalCount+96*PackBytes.chunks budget

def rootsBytes (count : Nat) := 32*count+32
def afterRoots (cursor : BitVec 64) (count : Nat) := cursor+BitVec.ofNat 64 (rootsBytes count)
def chunksCursor (ch : BitVec 64) := ch+608#64

structure Description.RuntimeGeometry (data : Description) (budget : Nat) (ch : BitVec 64) : Prop where
  arena : AllocatedBytes.Arena ch (608+data.scratchBytes budget)
  aligned : ch.toNat%8=0

theorem Description.scratch_bound (data : Description) (lower upper budget : Nat) (layout : data.Layout lower upper budget) :
    data.scratchBytes budget≤30*budget+4192 := by
  have tx:=layout.transactionCountBound
  have wd:=layout.withdrawalCountBound
  unfold Description.scratchBytes PackBytes.chunks
  omega

theorem Description.static_geometry (data : Description) (lower upper budget : Nat) (ch : BitVec 64)
    (layout : data.Layout lower upper budget) (geometry : data.RuntimeGeometry budget ch) :
    StaticFields.Geometry data.raw ch (chunksCursor ch) ∧ AllocatedBytes.Arena (chunksCursor ch) (data.scratchBytes budget) ∧
      (chunksCursor ch).toNat=ch.toNat+608 := by
  have upperBound:=geometry.arena.upper
  have number : (chunksCursor ch).toNat=ch.toNat+608 := BitVec.toNat_add_of_lt (by change ch.toNat+608<2^64; unfold Description.scratchBytes at upperBound; omega)
  have scratch : AllocatedBytes.Arena (chunksCursor ch) (data.scratchBytes budget) :=
    AllocatedBytes.Arena.subrange ch (608+data.scratchBytes budget) 608 (data.scratchBytes budget) geometry.arena (by omega)
  refine ⟨⟨layout.rawArena,AllocatedBytes.Arena.weaken ch _ 608 geometry.arena (by omega),geometry.aligned,by rw [number],?_,?_⟩,scratch,number⟩
  · exact AllocatedBytes.Arena.weaken _ (data.scratchBytes budget) 1600 scratch (by unfold Description.scratchBytes; omega)
  · rw [number]; have h:=geometry.aligned; omega

/-- A real aligned roots allocation leaves both byte-hash and progressive
list arenas available from the same fixed scratch interval. -/
theorem roots_geometry (cursor : BitVec 64) (count scratch packed : Nat)
    (arena : AllocatedBytes.Arena cursor scratch) (aligned : cursor.toNat%8=0)
    (fits : rootsBytes count+max packed (832+64*count)≤scratch) :
    AllocatedBytes.Arena cursor (32*count) ∧ AllocatedBytes.Arena (afterRoots cursor count) packed ∧
    AllocatedBytes.Arena (afterRoots cursor count) (832+64*count) ∧
    (afterRoots cursor count).toNat=cursor.toNat+rootsBytes count ∧ (afterRoots cursor count).toNat%8=0 ∧
    PersistentAlloc.rounded cursor (BitVec.ofNat 64 (rootsBytes count))=afterRoots cursor count := by
  have upper:=arena.upper
  have rootBound : rootsBytes count≤scratch := by omega
  have number : (afterRoots cursor count).toNat=cursor.toNat+rootsBytes count := byteAddress_toNat cursor (rootsBytes count) (by omega)
  have amount : (BitVec.ofNat 64 (rootsBytes count)).toNat=rootsBytes count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have multiple : rootsBytes count%8=0 := by unfold rootsBytes; omega
  have nextAligned : (afterRoots cursor count).toNat%8=0 := by rw [number]; omega
  have rounded : PersistentAlloc.rounded cursor (BitVec.ofNat 64 (rootsBytes count))=afterRoots cursor count := by
    apply BitVec.eq_of_toNat_eq
    rw [PersistentAlloc.rounded_nat cursor (BitVec.ofNat 64 (rootsBytes count)) (by rw [amount]; omega),amount,number]
    omega
  exact ⟨AllocatedBytes.Arena.weaken cursor scratch (32*count) arena (by unfold rootsBytes at rootBound; omega),
    AllocatedBytes.Arena.subrange cursor scratch (rootsBytes count) packed arena (by omega),
    AllocatedBytes.Arena.subrange cursor scratch (rootsBytes count) (832+64*count) arena (by omega),number,nextAligned,rounded⟩

/-- The actual transaction row loop's physical geometry is derived from
decoded extents and the shared scratch arena, not future hash outcomes. -/
theorem Description.transaction_geometry (data : Description) (lower upper budget : Nat) (ch stp accel chunk : BitVec 64)
    (layout : data.Layout lower upper budget) (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (before : upper≤ch.toNat) :
    Transactions.Geometry data.transactions (chunksCursor ch) (afterRoots (chunksCursor ch) data.transactionCount) stp accel chunk
      data.transactionPointer data.transactionLength data.transactionCount budget ∧
    AllocatedBytes.Arena (afterRoots (chunksCursor ch) data.transactionCount) (832+64*data.transactionCount) := by
  obtain ⟨fixed,scratch,cursorNumber⟩ := data.static_geometry lower upper budget ch layout geometry
  have cursorAligned:=fixed.aligned
  have fits : rootsBytes data.transactionCount+max (832+96*PackBytes.chunks budget) (832+64*data.transactionCount)≤data.scratchBytes budget := by
    unfold rootsBytes Description.scratchBytes
    omega
  obtain ⟨rootsArena,packedArena,listArena,number,nextAligned,rounded⟩ := roots_geometry (chunksCursor ch) data.transactionCount (data.scratchBytes budget) (832+96*PackBytes.chunks budget) scratch cursorAligned fits
  refine ⟨⟨?_,layout.budgetBound,layout.transactionLengths,layout.transactionArena,layout.transactionAligned,?_,?_,?_,?_,rootsArena,cursorAligned,?_,packedArena,nextAligned,layout.transactionInputs⟩,listArena⟩
  · have a:=layout.transactionCountBound; have b:=layout.budgetBound; omega
  · intro positive; have h:=layout.transactionBefore positive; rw [cursorNumber]; omega
  · intro positive; have h:=layout.transactionLower positive; have s:=separation.state; omega
  · intro positive; have h:=layout.transactionLower positive; have s:=separation.accelerator; omega
  · intro positive; have h:=layout.transactionLower positive; have s:=separation.lengthChunk; omega
  · rw [number]; unfold rootsBytes; omega

/-- The withdrawal loop reuses that same original released scratch cursor. -/
theorem Description.withdrawal_geometry (data : Description) (lower upper budget : Nat) (ch : BitVec 64)
    (layout : data.Layout lower upper budget) (geometry : data.RuntimeGeometry budget ch) :
    Withdrawals.Geometry data.withdrawals (chunksCursor ch) (afterRoots (chunksCursor ch) data.withdrawalCount) data.withdrawalCount ∧
    AllocatedBytes.Arena (afterRoots (chunksCursor ch) data.withdrawalCount) (832+64*data.withdrawalCount) := by
  obtain ⟨fixed,scratch,cursorNumber⟩ := data.static_geometry lower upper budget ch layout geometry
  have fits : rootsBytes data.withdrawalCount+max 1248 (832+64*data.withdrawalCount)≤data.scratchBytes budget := by
    unfold rootsBytes Description.scratchBytes
    omega
  obtain ⟨rootsArena,temporary,listArena,number,nextAligned,rounded⟩ := roots_geometry (chunksCursor ch) data.withdrawalCount (data.scratchBytes budget) 1248 scratch fixed.aligned fits
  refine ⟨⟨?_,layout.withdrawalArena,rootsArena,fixed.aligned,?_,temporary,nextAligned⟩,listArena⟩
  · have a:=layout.withdrawalCountBound; have b:=layout.budgetBound; omega
  · rw [number]; unfold rootsBytes; omega

end InitECandidate.Solver.Input.PayloadHash

#print axioms InitECandidate.Solver.Input.PayloadHash.Description.scratch_bound
#print axioms InitECandidate.Solver.Input.PayloadHash.Description.static_geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.roots_geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.Description.transaction_geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.Description.withdrawal_geometry
