import InitECandidate.Solver.Mpt.WitnessRootCacheNormal
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessMaterialize

theorem cache_prefix : Input.LocalPrefix (ofString "nd") cacheGuard := by
  apply Input.LocalPrefix.ite
  · apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
    exact .seq (.call none _ _ (by simp)) (.store _ _)
  · exact .skip

theorem cache_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (cell : source.locals.lookup (ofString "nd")=some (.val (.word node))) :
    evaluateHOLFiniteState source cacheGuard =
      if node=0#64 then (none,source) else evaluateHOLFiniteState source cacheAllocated := by
  rw [cacheGuard,evaluateHOLFiniteState_ite]
  by_cases zero : node=0#64 <;>
    simp [evalHOLExact,localVar,toExact,cell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]

/-- A genuine root footer returns the very node produced by the materializer,
with its database and earlier memory retained through the real cache allocation. -/
theorem suffix_normal_prefix (data : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db hashPtr node : BitVec 64) (returned : ValueHOL 64)
    (output : Output data frontier db source (.val (.word node)))
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterMaterialize=(some (.returned returned),post)) :
    returned=.val (.word node) ∧ Output data frontier db post returned ∧ WitnessCore.Stack.StablePrefix source post frontier ∧
      (∀ key,key≠ofString "heap_ptr"→post.globals.lookup key=source.globals.lookup key) := by
  rw [suffix_shape] at normal
  obtain ⟨middle,guardRun,footerRun,nodeFrame⟩:=cache_prefix.normal_continue source post (.return (localVar "nd")) returned normal
  have guarded : Output data frontier db middle (.val (.word node)) ∧ WitnessCore.Stack.StablePrefix source middle frontier ∧
      (∀ key,key≠ofString "heap_ptr"→middle.globals.lookup key=source.globals.lookup key) := by
    rw [cache_choice source node nodeCell] at guardRun
    by_cases zero : node=0#64
    · rw [if_pos zero] at guardRun
      have same : source=middle:=congrArg Prod.snd guardRun
      rw [←same]; exact ⟨output,fun _ _=>rfl,fun _ _=>rfl⟩
    · rw [if_neg zero] at guardRun
      have savedOutput:=output
      obtain ⟨heap,child,valueEq,heapCell,rest⟩:=savedOutput
      exact cache_allocated_normal_prefix data source middle frontier db heap hashPtr node output heapCell zero hashCell nodeCell installed guardRun
  have middleNode : middle.locals.lookup (ofString "nd")=some (.val (.word node)):=nodeFrame.trans nodeCell
  obtain ⟨read,postEq⟩:=Input.return_normal middle post (localVar "nd") returned footerRun
  have actualRead : eval middle (localVar "nd")=some (.val (.word node)):=by simp [eval,localVar,evalHOLExact,toExact,middleNode]
  have returnedEq : returned=.val (.word node):=Option.some.inj (read.symm.trans actualRead)
  refine ⟨returnedEq,?_,?_,?_⟩
  · rw [returnedEq]
    apply guarded.1.of_erase data frontier db middle post (.val (.word node))
    rw [postEq]; rfl
  · intro query upper
    rw [postEq]
    exact guarded.2.1 query upper
  · intro key notHeap
    rw [postEq]
    exact guarded.2.2 key notHeap

theorem suffix_normal (data : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db hashPtr node : BitVec 64) (returned : ValueHOL 64)
    (output : Output data frontier db source (.val (.word node)))
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterMaterialize=(some (.returned returned),post)) :
    returned=.val (.word node) ∧ Output data frontier db post returned := by
  have result:=suffix_normal_prefix data source post frontier db hashPtr node returned output hashCell nodeCell installed normal
  exact ⟨result.1,result.2.1⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.cache_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.cache_choice
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.suffix_normal

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.suffix_normal_prefix
