import InitECandidate.Solver.Mpt.WitnessRootSuffixNormal
import InitECandidate.Solver.Mpt.WitnessRootCachePathNormal

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessMaterialize

/-- A genuine root footer returns the very node produced by the materializer,
with its closed graph retained through the optional real cache allocation. -/
theorem suffix_path_normal_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db hashPtr node : BitVec 64) (returned : ValueHOL 64)
    (output : PathOutput input frontier db source (.val (.word node))) (frontierLower : 2713731432≤frontier)
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterMaterialize=(some (.returned returned),post)) :
    returned=.val (.word node) ∧ PathOutput input frontier db post returned ∧ WitnessCore.Stack.StablePrefix source post frontier := by
  rw [suffix_shape] at normal
  obtain ⟨middle,guardRun,footerRun,nodeFrame⟩:=cache_prefix.normal_continue source post (.return (localVar "nd")) returned normal
  have guarded : PathOutput input frontier db middle (.val (.word node)) ∧ WitnessCore.Stack.StablePrefix source middle frontier := by
    rw [cache_choice source node nodeCell] at guardRun
    by_cases zero : node=0#64
    · rw [if_pos zero] at guardRun
      have same : source=middle:=congrArg Prod.snd guardRun
      rw [←same]; exact ⟨output,fun _ _ _=>rfl⟩
    · rw [if_neg zero] at guardRun
      obtain ⟨heap,child,valueEq,heapCell,rest⟩:=output.1
      exact cache_allocated_path_normal_prefix input source middle frontier db heap hashPtr node output frontierLower heapCell zero hashCell nodeCell installed guardRun
  have middleNode : middle.locals.lookup (ofString "nd")=some (.val (.word node)):=nodeFrame.trans nodeCell
  obtain ⟨read,postEq⟩:=Input.return_normal middle post (localVar "nd") returned footerRun
  have actualRead : eval middle (localVar "nd")=some (.val (.word node)):=by simp [eval,localVar,evalHOLExact,toExact,middleNode]
  have returnedEq : returned=.val (.word node):=Option.some.inj (read.symm.trans actualRead)
  refine ⟨returnedEq,?_,?_⟩
  · rw [returnedEq]
    apply guarded.1.of_erase input frontier db middle post (.val (.word node))
    rw [postEq]; rfl
  · intro query lower upper
    rw [postEq]
    exact guarded.2 query lower upper

theorem suffix_path_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db hashPtr node : BitVec 64) (returned : ValueHOL 64)
    (output : PathOutput input frontier db source (.val (.word node))) (frontierLower : 2713731432≤frontier)
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterMaterialize=(some (.returned returned),post)) :
    returned=.val (.word node) ∧ PathOutput input frontier db post returned := by
  have result:=suffix_path_normal_prefix input source post frontier db hashPtr node returned output frontierLower hashCell nodeCell installed normal
  exact ⟨result.1,result.2.1⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.suffix_path_normal

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.suffix_path_normal_prefix
