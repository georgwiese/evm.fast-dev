import InitECandidate.Solver.Input.CurrentHash.MerkleSuffixMemory
import InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost

namespace InitECandidate.Solver.Input.CurrentHash.MerkleBufferMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open MerkleBufferCost

theorem copy_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) copyArguments =
      some (CopyGeneral.values buffer p (32*n)) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,copyArguments,localVar,data.buf,data.pointer,data.count,
    CopyGeneral.values,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

theorem zero_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) (inside : n≤capacity) (small : capacity<2^64) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) zeroArguments =
      some (Zero.values (buffer+BitVec.ofNat 64 (32*n)) (32*(capacity-n))) := by
  have difference := BitVec.ofNat_sub_ofNat_of_le (w:=64) capacity n (by omega) inside
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,zeroArguments,localVar,data.buf,data.count,data.size,
    Zero.values,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,difference,BitVec.ofNat_mul,Nat.mul_comm]

theorem after_clear_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer out query : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) (pointers : MerkleSuffixMemory.Pointers source buffer out)
    (positive : 1≤capacity) (small : capacity<2^63) (targetSmall : target<2^63) (depths : depth≤target)
    (bufferArena : AllocatedBytes.Arena buffer (32*capacity)) (outArena : AllocatedBytes.Arena out 32)
    (bufferAway : CopyGeneral.Away buffer query (32*capacity)) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterClear = (some (.returned value),post)) :
    post.memory query = source.memory query := by
  have read : eval source (localVar "size") = some (.val (.word (BitVec.ofNat 64 capacity))) := by
    simpa [eval,evalHOLExact,toExact,localVar] using data.size
  rw [source_shape.2.2] at actual
  apply MemoryAt.declaration_returned source post "cur" (localVar "size") (BitVec.ofNat 64 capacity) query MerkleSuffixCost.denseContinuation value read _ actual
  intro inner normal
  let entry := bind source "cur" (BitVec.ofNat 64 capacity)
  have kept (name : String) (different : ofString "cur" ≠ ofString name) := bind_lookup_other source "cur" name (BitVec.ofNat 64 capacity) different
  have ready : MerkleSuffixMemory.Pointers entry buffer out := ⟨pointers.installed,pointers.domain,
    (kept "buf" (by decide)).trans pointers.buffer,(kept "out" (by decide)).trans pointers.output⟩
  exact MerkleSuffixMemory.memory entry inner buffer out query capacity capacity depth target small positive (Nat.le_refl _) targetSmall depths ready
    (bind_lookup_same _ _ _) ((kept "dn" (by decide)).trans data.dn) ((kept "target" (by decide)).trans data.maximum)
    bufferArena outArena bufferAway outAway value normal

theorem after_copy_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer out query : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) (pointers : MerkleSuffixMemory.Pointers source buffer out)
    (positive : 1≤capacity) (inside : n≤capacity) (small : capacity<2^63) (targetSmall : target<2^63) (depths : depth≤target)
    (bufferArena : AllocatedBytes.Arena buffer (32*capacity)) (outArena : AllocatedBytes.Arena out 32)
    (aligned : buffer.toNat%8=0) (bufferAway : CopyGeneral.Away buffer query (32*capacity)) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterCopy = (some (.returned value),post)) :
    post.memory query = source.memory query := by
  rw [source_shape.2.1] at actual
  have safe (key : MlS) : LocalPrefix key (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((safe (ofString "buf")).summary_full source).2.1 actual
  have args := zero_arguments source p buffer n capacity depth target data inside (by omega)
  have upper := bufferArena.upper
  have tailArena : AllocatedBytes.Arena (buffer+BitVec.ofNat 64 (32*n)) (32*(capacity-n)) :=
    AllocatedBytes.Arena.subrange buffer (32*capacity) (32*n) (32*(capacity-n)) bufferArena (by omega)
  have number : (buffer+BitVec.ofNat 64 (32*n)).toNat = buffer.toNat+32*n := byteAddress_toNat buffer (32*n) (by omega)
  have tailAligned : (buffer+BitVec.ofNat 64 (32*n)).toNat%8=0 := by rw [number]; omega
  have tailAway := CopyGeneral.Away.subrange buffer query (32*capacity) (32*n) (32*(capacity-n)) bufferAway (by omega)
  have cleared := MemoryAt.zero_normal source middle zeroArguments (buffer+BitVec.ofNat 64 (32*n)) query (32*(capacity-n)) args
    pointers.installed pointers.domain tailArena tailAligned (by omega) (by intro offset bound; exact (tailAway offset bound).1) normal
  have next := pointers.after_prefix _ (safe _) (safe _) normal
  exact (after_clear_memory middle post p buffer out query n capacity depth target (data.after_call _ _ normal) next positive small targetSmall depths
    bufferArena outArena bufferAway outAway value remaining).trans cleared

/-- Actual copy, padding clear, halving, extension and output suffix preserve
the same protected metadata word outside both written regions. -/
theorem memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer out query : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) (pointers : MerkleSuffixMemory.Pointers source buffer out)
    (positive : 1≤capacity) (inside : n≤capacity) (small : capacity<2^63) (targetSmall : target<2^63) (depths : depth≤target)
    (inputArena : AllocatedBytes.Arena p (32*n)) (bufferArena : AllocatedBytes.Arena buffer (32*capacity)) (outArena : AllocatedBytes.Arena out 32)
    (aligned : buffer.toNat%8=0) (bufferAway : CopyGeneral.Away buffer query (32*capacity)) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterBuffer = (some (.returned value),post)) :
    post.memory query = source.memory query := by
  rw [source_shape.1] at actual
  have safe (key : MlS) : LocalPrefix key (.call (some (none,none)) (ofString "memcpy") copyArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((safe (ofString "buf")).summary_full source).2.1 actual
  have copied := MemoryAt.copy_normal source middle copyArguments p buffer query (32*n) (copy_arguments source p buffer n capacity depth target data)
    pointers.installed pointers.domain inputArena (AllocatedBytes.Arena.weaken buffer (32*capacity) (32*n) bufferArena (by omega))
    (by intro offset bound; exact bufferAway offset (by omega)) normal
  have next := pointers.after_prefix _ (safe _) (safe _) normal
  exact (after_copy_memory middle post p buffer out query n capacity depth target (data.after_call _ _ normal) next positive inside small targetSmall depths
    bufferArena outArena aligned bufferAway outAway value remaining).trans copied

end InitECandidate.Solver.Input.CurrentHash.MerkleBufferMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferMemory.copy_arguments
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferMemory.zero_arguments
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferMemory.after_clear_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferMemory.after_copy_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferMemory.memory
