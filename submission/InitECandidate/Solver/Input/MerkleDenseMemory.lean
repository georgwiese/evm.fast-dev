import InitECandidate.Solver.Input.MerkleOuterMemory
import InitECandidate.Solver.Input.MerkleExtensionMemory
import InitECandidate.Solver.Input.CopyReturnMemory

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem output_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor))) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (bufferArena : AllocatedBytes.Arena cursor 32) (outputArena : AllocatedBytes.Arena out 32) (away : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterExtension=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) outputArguments=some (CopyGeneral.values out cursor 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,outputArguments,localVar,buffer,output,CopyGeneral.values]
  rw [extension_shape.2.2.2] at run
  exact MemoryAt.copy_release_returned source post outputArguments [localVar "mark"] cursor out query 32 installed domain args bufferArena outputArena away value run

theorem after_dense_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out zeros stp accel query : BitVec 64) (dn target : Nat)
    (small : target<64) (inside : dn≤target) (workspace : ShaPair.Workspace source stp accel)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor))) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (targetLocal : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (bufferArena : AllocatedBytes.Arena cursor 32) (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (bufferAway : CopyGeneral.Away cursor query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterDense=(some (.returned value),post)) : post.memory query=source.memory query := by
  have read : eval source (localVar "dn")=some (.val (.word (BitVec.ofNat 64 dn))) := by simpa [eval,localVar,evalHOLExact,toExact] using depth
  rw [extension_shape.1] at run
  obtain ⟨inner,remaining,endpoint⟩ := declaration_return_word source post "d" (localVar "dn") (BitVec.ofNat 64 dn) _ value read run
  let entry := bind source "d" (BitVec.ofNat 64 dn)
  have entryWorkspace := ShaPair.Workspace.of_fields source entry stp accel workspace rfl rfl rfl rfl
  have other (name : String) (different : ofString "d"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other source "d" name _ different
  have entryBuffer := (other "buf" (by decide)).trans buffer
  have entryTarget := (other "target" (by decide)).trans targetLocal
  have entryOutput := (other "out" (by decide)).trans output
  obtain ⟨middle,normal,outputRun⟩ := Input.sequence_returned entry inner extensionLoop afterExtension value ((extension_loop_other (ofString "out") (by decide)).summary_full entry).2.1 remaining
  have front := extension_loop_memory entry middle cursor zeros stp accel query dn target small inside entryWorkspace bufferArena tableArena entryBuffer (bind_lookup_same _ _ _) entryTarget table stateAway accelAway bufferAway normal
  have nextWorkspace := extension_loop_workspace entry middle stp accel entryWorkspace none normal
  have preserved (name : String) (different : ofString name≠ofString "d") : middle.locals.lookup (ofString name)=entry.locals.lookup (ofString name) := by
    have summary := (extension_loop_other (ofString name) different).summary_full entry
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  have tail := output_memory middle inner cursor out query nextWorkspace.installed nextWorkspace.domain ((preserved "buf" (by decide)).trans entryBuffer)
    ((preserved "out" (by decide)).trans entryOutput) bufferArena outputArena outAway value outputRun
  rw [endpoint]
  exact tail.trans front

/-- Complete actual normal dense/extension/output/release phase changes
only the real buffer/output and known mutable SHA workspace. -/
theorem dense_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out zeros stp accel query : BitVec 64) (cur capacity dn target : Nat)
    (positive : 1≤cur) (inside : cur≤capacity) (small : target<64) (depths : dn≤target) (workspace : ShaPair.Workspace source stp accel)
    (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur))))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor))) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (targetLocal : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (bufferArena : AllocatedBytes.Arena cursor (32*capacity)) (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (bufferAway : CopyGeneral.Away cursor query (32*capacity)) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source denseContinuation=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [outer_shape.2.2] at run
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post outerLoop afterDense value ((outer_loop_other (ofString "out") (by decide) (by decide) (by decide)).summary_full source).2.1 run
  have front := outer_loop_memory source middle cursor stp accel query cur capacity positive inside bufferArena workspace current buffer stateAway accelAway bufferAway normal
  have nextWorkspace := outer_loop_workspace source middle stp accel workspace none normal
  have preserved (name : String) (a : ofString name≠ofString "cur") (b : ofString name≠ofString "half") (c : ofString name≠ofString "j") : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (outer_loop_other (ofString name) a b c).summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  have tableFrame := outer_loop_globals (ofString "zero_hashes") source.code workspace.installed source rfl
  rw [normal] at tableFrame
  have nextTable := (congrArg Prod.snd tableFrame).trans table
  have buffer32 := AllocatedBytes.Arena.weaken cursor (32*capacity) 32 bufferArena (by omega)
  have away32 : CopyGeneral.Away cursor query 32 := by simpa only [BitVec.add_zero] using CopyGeneral.Away.subrange cursor query (32*capacity) 0 32 bufferAway (by omega)
  have tail := after_dense_memory middle post cursor out zeros stp accel query dn target small depths nextWorkspace
    ((preserved "buf" (by decide) (by decide) (by decide)).trans buffer) ((preserved "out" (by decide) (by decide) (by decide)).trans output)
    ((preserved "dn" (by decide) (by decide) (by decide)).trans depth) ((preserved "target" (by decide) (by decide) (by decide)).trans targetLocal)
    nextTable buffer32 outputArena tableArena stateAway accelAway away32 outAway value remaining
  exact tail.trans front

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.output_memory
#print axioms InitECandidate.Solver.Input.Merkle.after_dense_memory
#print axioms InitECandidate.Solver.Input.Merkle.dense_memory
