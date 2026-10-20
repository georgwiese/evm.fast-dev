import InitECandidate.Solver.Input.MerkleOuterLoop
import InitECandidate.Solver.Input.MerkleExtensionLoop
import InitECandidate.Solver.Input.HeapScopeCost

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual root output copy and original heap_release, including failure
outcomes. No future successful release or return is assumed. -/
theorem output_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (bufferArena : AllocatedBytes.Arena cursor 32) (outputArena : AllocatedBytes.Arena out 32) :
    source.clock-(evaluateHOLFiniteState source afterExtension).2.clock≤6 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) outputArguments=some (CopyGeneral.values out cursor 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,outputArguments,localVar,buffer,output,CopyGeneral.values]
  have copyCost := CopyGeneral.call_cost_arena source outputArguments cursor out 32 args (CopyGeneral.original_code source.code installed) domain bufferArena outputArena
  have blocks := CopyGeneral.cost_word_multiple cursor out 32 (by decide)
  have tailPrice : ClockCost.Bound source.code (.seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))) 1 :=
    ClockCost.sequence source.code _ _ 1 0 (HeapScope.release_call_cost source.code installed (some none) _) (ClockCost.returned source.code _)
  rw [extension_shape.2.2.2]
  exact ClockCost.sequence_current source _ _ 5 1 (by omega) tailPrice

/-- The actual d declaration, depth-extension pairs and output/release
suffix, retaining current-state premises only. -/
theorem after_dense_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out zeros stp accel : BitVec 64) (dn target : Nat)
    (small : target<64) (inside : dn≤target) (workspace : ShaPair.Workspace source stp accel)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (targetLocal : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (bufferArena : AllocatedBytes.Arena cursor 32) (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048) :
    source.clock-(evaluateHOLFiniteState source afterDense).2.clock≤54*(target-dn)+6 := by
  let entry := bind source "d" (BitVec.ofNat 64 dn)
  have entryWorkspace := ShaPair.Workspace.of_fields source entry stp accel workspace rfl rfl rfl rfl
  have entryD : entry.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 dn))) := bind_lookup_same _ _ _
  have entryTarget := (bind_lookup_other source "d" "target" (BitVec.ofNat 64 dn) (by decide)).trans targetLocal
  have entryBuffer := (bind_lookup_other source "d" "buf" (BitVec.ofNat 64 dn) (by decide)).trans buffer
  have entryOutput := (bind_lookup_other source "d" "out" (BitVec.ofNat 64 dn) (by decide)).trans output
  have extensionCost := extension_loop_cost entry cursor zeros stp accel dn target small inside bufferArena tableArena entryWorkspace entryD entryTarget entryBuffer table
  have read : eval source (localVar "dn")=some (.val (.word (BitVec.ofNat 64 dn))) := by simpa [eval,localVar,evalHOLExact,toExact] using depth
  rw [extension_shape.1]
  apply ClockCost.declared_current source "d" (localVar "dn") (BitVec.ofNat 64 dn) _ (54*(target-dn)+6) read
  apply ClockCost.sequence_reached_current entry extensionLoop afterExtension (54*(target-dn)) 6 extensionCost
  intro middle normal
  have nextWorkspace := extension_loop_workspace entry middle stp accel entryWorkspace none normal
  have preserved (name : String) (different : ofString name≠ofString "d") : middle.locals.lookup (ofString name)=entry.locals.lookup (ofString name) := by
    have summary := (extension_loop_other (ofString name) different).summary_full entry
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  exact output_cost middle cursor out nextWorkspace.installed nextWorkspace.domain
    ((preserved "buf" (by decide)).trans entryBuffer) ((preserved "out" (by decide)).trans entryOutput) bufferArena outputArena

/-- Complete actual dense/extension/output phase. Dense rounds telescope;
the declared limit contributes only the difference in actual tree depths. -/
theorem dense_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out zeros stp accel : BitVec 64) (cur capacity dn target : Nat)
    (positive : 1≤cur) (inside : cur≤capacity) (small : target<64) (depths : dn≤target)
    (workspace : ShaPair.Workspace source stp accel)
    (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur))))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (targetLocal : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (bufferArena : AllocatedBytes.Arena cursor (32*capacity)) (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048) :
    source.clock-(evaluateHOLFiniteState source denseContinuation).2.clock≤55*(cur-1)+54*(target-dn)+6 := by
  have outerCost := outer_loop_cost source cursor stp accel cur capacity positive inside bufferArena workspace current buffer
  have buffer32 := AllocatedBytes.Arena.weaken cursor (32*capacity) 32 bufferArena (by omega)
  have tailCost : ∀ middle,evaluateHOLFiniteState source outerLoop=(none,middle) →
      middle.clock-(evaluateHOLFiniteState middle afterDense).2.clock≤54*(target-dn)+6 := by
    intro middle normal
    have nextWorkspace := outer_loop_workspace source middle stp accel workspace none normal
    have preserved (name : String) (notCur : ofString name≠ofString "cur") (notHalf : ofString name≠ofString "half") (notJ : ofString name≠ofString "j") :
        middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
      have summary := (outer_loop_other (ofString name) notCur notHalf notJ).summary_full source
      unfold LocalSummary at summary
      rw [normal] at summary
      exact summary.1 rfl
    have tableFrame := outer_loop_globals (ofString "zero_hashes") source.code workspace.installed source rfl
    rw [normal] at tableFrame
    have nextTable := (congrArg Prod.snd tableFrame).trans table
    exact after_dense_cost middle cursor out zeros stp accel dn target small depths nextWorkspace
      ((preserved "buf" (by decide) (by decide) (by decide)).trans buffer)
      ((preserved "out" (by decide) (by decide) (by decide)).trans output)
      ((preserved "dn" (by decide) (by decide) (by decide)).trans depth)
      ((preserved "target" (by decide) (by decide) (by decide)).trans targetLocal)
      nextTable buffer32 outputArena tableArena
  have cost := ClockCost.sequence_reached_current source outerLoop afterDense (55*(cur-1)) (54*(target-dn)+6) outerCost tailCost
  rw [outer_shape.2.2]
  simpa only [Nat.add_assoc] using cost

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.output_cost
#print axioms InitECandidate.Solver.Input.Merkle.after_dense_cost
#print axioms InitECandidate.Solver.Input.Merkle.dense_cost
