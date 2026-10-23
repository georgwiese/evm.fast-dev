import InitECandidate.Solver.Mpt.DeleteExtensionProgram
import InitECandidate.Solver.Mpt.TrieChildStoreNormal
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node child : BitVec 64) :=
  {source with memory:=StoreWord.put source.memory (node+48#64) child}

theorem null_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cell : source.locals.lookup (ofString "nc")=some (.val (.word 0#64))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ target=emptyLocalsHOLFinite source := by
  have guard : evaluateHOLFiniteState source nullGuard=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source):=by
    rw [entry_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,shapeOfHOLExact]
  rw [entry_shapes.1,StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ (.returned (.val (.word 0#64))) guard (Nat.le_refl _)] at normal
  have result:=congrArg Prod.fst normal
  have endpoint:=congrArg Prod.snd normal
  exact ⟨by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using result.symm,endpoint.symm⟩

/-- A nonnull child reaches the real tag declaration without changing
the state or paying a source clock. -/
theorem nonnull_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (child : BitVec 64)
    (cell : source.locals.lookup (ofString "nc")=some (.val (.word child))) (nonnull : child≠0#64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    evaluateHOLFiniteState source tagScope=(some (.returned value),target) := by
  have guard : evaluateHOLFiniteState source nullGuard=(none,source):=by
    rw [entry_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonnull,evaluateHOLFiniteState_skip]
  rw [entry_shapes.1,StateSteps.next_sequence source source _ _ guard (Nat.le_refl _)] at normal
  exact normal

/-- The actual branch-child finish replaces the original extension's
child48 and returns that extension, preserving all full graph/path facts. -/
theorem branch_finish_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower upper pathLower : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (values : TrieWalk.Values graph limit property)
    (regions : graph.Regions nodeLower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64) (childMember : graph.valid child)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source branchFinish=(some (.returned value),target)) :
    value=.val (.word node) ∧ target=emptyLocalsHOLFinite (branchPost source node child) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower upper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower upper ∧ next.PathSeparated := by
  let address : ExpHOL 64:=.op .add [localVar "node",.const 48#64]
  have safe : Input.LocalPrefix (ofString "node") (.store address (localVar "nc")):=.store _ _
  rw [branchFinish] at normal
  obtain ⟨middle,stored,continued⟩:=Input.sequence_returned source target (.store address (localVar "nc")) (.return (localVar "node")) value
    (fun returned=>(safe.summary_full source).2.1 returned) normal
  have addressRead : eval source address=some (.val (.word (node+48#64))):=by
    simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have childRead : eval source (localVar "nc")=some (.val (.word child)):=by simp [eval,localVar,evalHOLExact,toExact,childCell]
  obtain ⟨mapped,middleEq⟩:=Input.word_store_normal source middle address (localVar "nc") (node+48#64) child addressRead childRead stored
  subst middle
  obtain ⟨read,endpoint⟩:=Input.return_normal (branchPost source node child) target (localVar "node") value continued
  have expected : eval (branchPost source node child) (localVar "node")=some (.val (.word node)):=by
    simp [eval,localVar,evalHOLExact,toExact,branchPost,nodeCell]
  have answer : value=.val (.word node):=Option.some.inj (read.symm.trans expected)
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    graph.after_child_store source limit nodeLower upper pathLower upper property values regions disjoint paths pathRegions separated node child 48
      (.extension tag) member active childMember
  refine ⟨answer,endpoint,?_⟩
  rw [endpoint]
  exact ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.null_normal
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.nonnull_entry
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.branch_finish_paths
