import InitECandidate.Solver.Input.CurrentHash.MerkleDenseMemory
import InitECandidate.Solver.Input.CurrentHash.MerkleSuffixCost
import InitECandidate.Solver.Input.CopyReturnMemory

namespace InitECandidate.Solver.Input.CurrentHash.MerkleSuffixMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open MerkleSuffixCost

structure Pointers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer out : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs = InitE.ordinaryDomain
  buffer : source.locals.lookup (ofString "buf") = some (.val (.word buffer))
  output : source.locals.lookup (ofString "out") = some (.val (.word out))

theorem Pointers.after_prefix {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {buffer out : BitVec 64}
    (data : Pointers source buffer out) (program : ProgHOL 64)
    (bufSafe : LocalPrefix (ofString "buf") program) (outSafe : LocalPrefix (ofString "out") program)
    (actual : evaluateHOLFiniteState source program = (none,post)) : Pointers post buffer out := by
  have fields := evaluation_fields source post program none actual
  have code : OriginalCode.Installed post.code := by rw [fields.2.2.2]; exact data.installed
  have bufSummary := bufSafe.summary_full source
  have outSummary := outSafe.summary_full source
  unfold LocalSummary at bufSummary outSummary
  rw [actual] at bufSummary outSummary
  exact ⟨code,fields.1.trans data.domain,(bufSummary.1 rfl).trans data.buffer,(outSummary.1 rfl).trans data.output⟩

theorem output_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer out query : BitVec 64)
    (data : Pointers source buffer out) (bufferArena : AllocatedBytes.Arena buffer 32) (outArena : AllocatedBytes.Arena out 32)
    (away : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterExtension = (some (.returned value),post)) : post.memory query = source.memory query := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "out",localVar "buf",.const 32#64] = some (CopyGeneral.values out buffer 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,data.buffer,data.output,CopyGeneral.values]
  rw [source_shape.2.2.2] at actual
  exact MemoryAt.copy_release_returned source post _ _ buffer out query 32 data.installed data.domain args bufferArena outArena away value actual

theorem extension_continuation_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer out query : BitVec 64) (depth target : Nat)
    (small : target<2^63) (inside : depth≤target) (data : Pointers source buffer out)
    (position : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 depth))))
    (maximum : source.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 target))))
    (bufferArena : AllocatedBytes.Arena buffer 32) (outArena : AllocatedBytes.Arena out 32)
    (bufferAway : CopyGeneral.Away buffer query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source extensionContinuation = (some (.returned value),post)) :
    post.memory query = source.memory query := by
  have localLoop (key : MlS) (different : key ≠ ofString "d") : LocalPrefix key (MerklePairLoops.loop .extension) := by
    rw [(MerklePairLoops.source_shape .extension).1]
    exact .loop _ (MerklePairLoops.other .extension key different)
  rw [source_shape.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((localLoop (ofString "buf") (by decide)).summary_full source).2.1 actual
  have loopFrame := MerklePairMemory.loop_memory .extension source middle buffer query depth target small inside data.installed
    data.buffer position maximum (by intro index active; exact bufferAway) normal
  have next := data.after_prefix _ (localLoop _ (by decide)) (localLoop _ (by decide)) normal
  exact (output_memory middle post buffer out query next bufferArena outArena outAway value remaining).trans loopFrame

theorem after_dense_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer out query : BitVec 64) (depth target : Nat)
    (small : target<2^63) (inside : depth≤target) (data : Pointers source buffer out)
    (dn : source.locals.lookup (ofString "dn") = some (.val (.word (BitVec.ofNat 64 depth))))
    (maximum : source.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 target))))
    (bufferArena : AllocatedBytes.Arena buffer 32) (outArena : AllocatedBytes.Arena out 32)
    (bufferAway : CopyGeneral.Away buffer query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterDense = (some (.returned value),post)) :
    post.memory query = source.memory query := by
  have read : eval source (localVar "dn") = some (.val (.word (BitVec.ofNat 64 depth))) := by
    simpa [eval,evalHOLExact,toExact,localVar] using dn
  rw [source_shape.2.1] at actual
  apply MemoryAt.declaration_returned source post "d" (localVar "dn") (BitVec.ofNat 64 depth) query extensionContinuation value read _ actual
  intro inner normal
  let entry := bind source "d" (BitVec.ofNat 64 depth)
  have kept (name : String) (different : ofString "d" ≠ ofString name) := bind_lookup_other source "d" name (BitVec.ofNat 64 depth) different
  have ready : Pointers entry buffer out := ⟨data.installed,data.domain,(kept "buf" (by decide)).trans data.buffer,
    (kept "out" (by decide)).trans data.output⟩
  exact extension_continuation_memory entry inner buffer out query depth target small inside ready (bind_lookup_same _ _ _)
    ((kept "target" (by decide)).trans maximum) bufferArena outArena bufferAway outAway value normal

/-- Whole actual dense/extension/output/release suffix. Protected metadata
is outside the real temporary buffer and final32-byte caller output. -/
theorem memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer out query : BitVec 64) (cur capacity depth target : Nat)
    (small : capacity<2^63) (positive : 1≤cur) (inside : cur≤capacity) (depthSmall : target<2^63) (depthInside : depth≤target)
    (data : Pointers source buffer out)
    (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur))))
    (dn : source.locals.lookup (ofString "dn") = some (.val (.word (BitVec.ofNat 64 depth))))
    (maximum : source.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 target))))
    (bufferArena : AllocatedBytes.Arena buffer (32*capacity)) (outArena : AllocatedBytes.Arena out 32)
    (bufferAway : CopyGeneral.Away buffer query (32*capacity)) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source denseContinuation = (some (.returned value),post)) :
    post.memory query = source.memory query := by
  have localLoop (key : MlS) (notCur : key ≠ ofString "cur") (notHalf : key ≠ ofString "half") (notJ : key ≠ ofString "j") :
      LocalPrefix key MerkleDenseCost.loop := by
    rw [MerkleDenseCost.source_shape.1]
    exact .loop _ (MerkleDenseCost.other key notCur notHalf notJ)
  rw [source_shape.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((localLoop (ofString "buf") (by decide) (by decide) (by decide)).summary_full source).2.1 actual
  have denseFrame := MerkleDenseMemory.loop_memory source middle buffer query cur capacity small positive inside data.installed data.buffer current bufferAway normal
  have next := data.after_prefix _ (localLoop _ (by decide) (by decide) (by decide)) (localLoop _ (by decide) (by decide) (by decide)) normal
  have kept (name : String) (notCur : ofString name ≠ ofString "cur") (notHalf : ofString name ≠ ofString "half") (notJ : ofString name ≠ ofString "j") :
      middle.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    have summary := (localLoop (ofString name) notCur notHalf notJ).summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  have suffixFrame := after_dense_memory middle post buffer out query depth target depthSmall depthInside next
    ((kept "dn" (by decide) (by decide) (by decide)).trans dn)
    ((kept "target" (by decide) (by decide) (by decide)).trans maximum)
    (AllocatedBytes.Arena.weaken buffer (32*capacity) 32 bufferArena (by omega)) outArena
    (by intro offset bound; exact bufferAway offset (by omega)) outAway value remaining
  exact suffixFrame.trans denseFrame

end InitECandidate.Solver.Input.CurrentHash.MerkleSuffixMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixMemory.Pointers.after_prefix
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixMemory.output_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixMemory.extension_continuation_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixMemory.after_dense_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixMemory.memory
