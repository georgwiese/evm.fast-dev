import InitECandidate.Solver.Input.PListChunksProgram
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.PListChunks
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_root_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out len stp accel chunk zeros : BitVec 64)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word len)))
    (outArena : AllocatedBytes.Arena out 32) : source.clock-(evaluateHOLFiniteState source afterRoot).2.clock≤59 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) mixArguments=some (MixLength.values out len out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,mixArguments,localVar,output,lengthLocal,MixLength.values]
  have mixPrice := MixLength.call_cost source out len out chunk stp accel workspace.sha workspace.chunkLocal outArena workspace.chunkArena workspace.chunkAligned (some none) mixArguments args
  exact ClockCost.sequence_current source _ _ 59 0 mixPrice (ClockCost.returned source.code _)

/-- Whole original progressive list-chunk hash, including the actual length
mix. The caller's current n/len/output are retained only on reached normal
prefixes; all actual non-timeout failing prefixes are included. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots cursor out len stp accel chunk zeros : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word len)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena roots (32*n)) (temporaryArena : AllocatedBytes.Arena cursor (832+64*n)) (aligned : cursor.toNat%8=0)
    (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*n+24206 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) progressiveArguments=some (Progressive.values roots (BitVec.ofNat 64 n) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,progressiveArguments,localVar,root,count,output,Progressive.values]
  have front : ∀ result target,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments)=(result,target) →
      result≠some .timeOut → source.clock-target.clock≤115*n+24147 := by
    intro result target actual notTimeout
    exact Progressive.call_cost source target roots cursor out zeros stp accel n bounded workspace.sha heap workspace.zerosLocal inputArena temporaryArena aligned outArena workspace.zeroArena
      (some none) progressiveArguments args result actual notTimeout
  rw [body_shape] at run
  have price := ClockCost.sequence_terminating source post _ afterRoot (115*n+24147) 59 front (by
    intro middle normal result target continued notTimeout
    have next := SszHash.Workspace.after source middle stp accel chunk zeros workspace _ none normal
      (fun key different=>progressive_globals key source.code workspace.sha.installed different)
    have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
      have safe : LocalPrefix (ofString name) (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) := .call none _ _ (by intro key impossible; cases impossible)
      have summary := safe.summary_full source
      unfold LocalSummary at summary
      rw [normal] at summary
      exact summary.1 rfl
    have tailPrice := after_root_cost middle out len stp accel chunk zeros next ((other "out").trans output) ((other "len").trans lengthLocal) outArena
    rw [continued] at tailPrice
    exact tailPrice) result run notTimeout
  omega

end InitECandidate.Solver.Input.PListChunks

#print axioms InitECandidate.Solver.Input.PListChunks.after_root_cost
#print axioms InitECandidate.Solver.Input.PListChunks.body_cost
