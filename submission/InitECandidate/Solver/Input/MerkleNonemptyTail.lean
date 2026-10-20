import InitECandidate.Solver.Input.MerkleDenseCost
import InitECandidate.Solver.Input.MerkleBufferFill

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original nonempty allocation/copy/dense/extension/release execution.
All operands and SHA workspace are current-state facts. Funding comes from
this same non-timeout run, including arbitrary later failure outcomes. -/
theorem nonempty_tail_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p cursor out zeros stp accel : BitVec 64) (n dn target : Nat)
    (positive : 0<n) (small : target<64) (depths : dn≤target) (countBound : n≤2^dn)
    (workspace : ShaPair.Workspace source stp accel)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (targetLocal : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (bufferArena : AllocatedBytes.Arena cursor (32*2^dn))
    (aligned : cursor.toNat%8=0) (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterDepth=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤3*n+2^dn+55*(2^dn-1)+54*(target-dn)+10 := by
  have nSmall : n<2^64 := by have upper:=inputArena.upper; omega
  have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nSmall]
  have nNonzero : BitVec.ofNat 64 n≠0#64 := by intro zero; have h:=congrArg BitVec.toNat zero; simp only [nNumber,BitVec.toNat_ofNat] at h; omega
  rw [after_depth_nonzero source (BitVec.ofNat 64 n) count nNonzero,allocation_shape.1] at run
  obtain ⟨markPaid,markedFinal,markedRun,markEndpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.installed) result run notTimeout
  let marked := bind {source with clock:=source.clock-1} "mark" cursor
  have markedOther (name : String) (different : ofString "mark"≠ofString name) : marked.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have markedDepth := (markedOther "dn" (by decide)).trans depth
  obtain ⟨allocPaid,bufferFinal,bufferRun,bufferEndpoint⟩ := allocation_prefix marked markedFinal cursor dn (by omega) markedDepth workspace.installed heap bufferArena result markedRun notTimeout
  let buffered := bufferEntry marked cursor dn
  have bufferedOther (name : String) (notBuf : ofString "buf"≠ofString name) (notSize : ofString "size"≠ofString name) :
      buffered.locals.lookup (ofString name)=marked.locals.lookup (ofString name) := by
    change (bind (PersistentAlloc.post {sized marked dn with clock:=marked.clock-1} cursor (BitVec.ofNat 64 (32*2^dn))) "buf" cursor).locals.lookup _=_
    rw [bind_lookup_other _ "buf" name cursor notBuf]
    exact bind_lookup_other marked "size" name (BitVec.ofNat 64 (2^dn)) notSize
  have bufferedGlobals (name : String) (different : ofString "heap_ptr"≠ofString name) : buffered.globals.lookup (ofString name)=source.globals.lookup (ofString name) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (32*2^dn)))))).lookup _=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,different]
  have bufferedWorkspace := ShaPair.Workspace.of_fields source buffered stp accel workspace rfl rfl (bufferedGlobals "sha_st" (by decide)) (bufferedGlobals "sha_accel" (by decide))
  have bufferFacts := buffer_fields marked cursor dn
  have bufferedPointer := (bufferedOther "p" (by decide) (by decide)).trans ((markedOther "p" (by decide)).trans pointer)
  have bufferedCount := (bufferedOther "n" (by decide) (by decide)).trans ((markedOther "n" (by decide)).trans count)
  obtain ⟨fillPaid,fillCost,denseFinal,denseRun,fillEndpoint⟩ := fill_prefix buffered bufferFinal p cursor n (2^dn) countBound bufferedWorkspace.installed bufferedWorkspace.domain
    bufferedPointer bufferFacts.1 bufferedCount bufferFacts.2.1 inputArena bufferArena aligned result bufferRun notTimeout
  let dense := denseEntry buffered p cursor n (2^dn)
  have denseFacts := fill_fields buffered p cursor n (2^dn)
  have denseOther (name : String) (notCur : ofString "cur"≠ofString name) (notBuf : ofString "buf"≠ofString name)
      (notSize : ofString "size"≠ofString name) (notMark : ofString "mark"≠ofString name) :
      dense.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    change (denseEntry buffered p cursor n (2^dn)).locals.lookup _=_
    rw [denseFacts.1]
    simp only [HolFiniteMapExact.lookup_update,FUPDATE,beq_iff_eq,if_neg notCur]
    exact (bufferedOther name notBuf notSize).trans (markedOther name notMark)
  have denseGlobals (name : String) (different : ofString "heap_ptr"≠ofString name) : dense.globals.lookup (ofString name)=source.globals.lookup (ofString name) :=
    bufferedGlobals name different
  have denseWorkspace := ShaPair.Workspace.of_fields source dense stp accel workspace rfl rfl (denseGlobals "sha_st" (by decide)) (denseGlobals "sha_accel" (by decide))
  have denseCurrent : dense.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 (2^dn)))) := bind_lookup_same _ _ _
  have denseBuffer : dense.locals.lookup (ofString "buf")=some (.val (.word cursor)) := by
    rw [show dense.locals=(denseEntry buffered p cursor n (2^dn)).locals from rfl,denseFacts.1]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cur"≠ofString "buf" from by decide] using bufferFacts.1
  have denseCost := dense_cost dense cursor out zeros stp accel (2^dn) (2^dn) dn target (by have h:=Nat.two_pow_pos dn; omega) (Nat.le_refl _) small depths denseWorkspace denseCurrent denseBuffer
    ((denseOther "out" (by decide) (by decide) (by decide) (by decide)).trans output)
    ((denseOther "dn" (by decide) (by decide) (by decide) (by decide)).trans depth)
    ((denseOther "target" (by decide) (by decide) (by decide) (by decide)).trans targetLocal)
    ((denseGlobals "zero_hashes" (by decide)).trans table) bufferArena outputArena tableArena
  rw [denseRun] at denseCost
  change dense.clock-denseFinal.clock≤55*(2^dn-1)+54*(target-dn)+6 at denseCost
  have monotone := evaluateHOLFiniteState_clock_le dense denseContinuation
  rw [denseRun] at monotone
  change denseFinal.clock≤dense.clock at monotone
  have finalClock : post.clock=denseFinal.clock := by rw [markEndpoint,bufferEndpoint,fillEndpoint]; rfl
  change buffered.clock-dense.clock≤3*n+2^dn+2 at fillCost
  have denseClock := fill_clock buffered p cursor n (2^dn)
  change dense.clock=buffered.clock-fillPrice p cursor n (2^dn) at denseClock
  have markedClock : marked.clock=source.clock-1 := rfl
  have bufferedClock : buffered.clock=marked.clock-1 := rfl
  rw [finalClock]
  omega

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.nonempty_tail_cost
