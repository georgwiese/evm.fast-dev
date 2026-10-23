import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The genuine value declaration reads the branch's actual168 field and
reaches the original collapse choices with its lexical restoration. -/
theorem value_entry_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterScan=(some (.returned value),post)) :
    ∃ inner,evaluateHOLFiniteState (QueryBranch.bind source "vl" (wordAt source.memory (node+168#64))) afterValue=(some (.returned value),inner) ∧
      post=restore source "vl" inner := by
  let data:=values.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide)
  have stored : source.memory (node+168#64)=.word (wordAt source.memory (node+168#64)):=by simp only [wordAt,data.lengthStored,MemoryBytes.wordBits]
  have read : eval source (field "node" 168#64)=some (.val (.word (wordAt source.memory (node+168#64)))):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read source "node" node 168#64 _ nodeCell data.lengthMapped stored
  rw [value_shapes.1] at normal
  exact Input.declaration_return_word source post "vl" (field "node" 168#64) _ afterValue value read normal

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.value_entry_normal
