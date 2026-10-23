import InitECandidate.Solver.Mpt.SetAfterRootNormal
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Load the actual map root and follow the complete normal setter
suffix, retaining its final graph and header frame through lexical exit. -/
theorem after_key_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (heap cursor frame root m key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid root)
    (small : length.toNat≤64) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m))) (mapped : source.memaddrs m) (stored : source.memory m=.word root)
    (headerSafe : graph.ProtectedWord m) (headerAbove : DeleteFrame.ceiling≤m.toNat) (headerBefore : m.toNat<heap.toNat)
    (headerAway : TrieWalk.PathWordAway key length.toNat m)
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterKey=(some (.returned value),target)) :
    Nonempty (Output source target value m graph heap key length limit nodeLower pathLower property (mutationAllowance pathLower)) := by
  have read : WitnessRadix.QueryBranch.eval source rootExpression=some (.val (.word root)):=by
    simp [WitnessRadix.QueryBranch.eval,rootExpression,WitnessRadix.QueryBranch.addConst,WitnessRadix.QueryBranch.localVar,evalHOLExact,evalListHOLExact,toExact,mCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]
  rw [mutation_shapes.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source target "root" rootExpression root afterRoot value read normal
  let ready:=WitnessRadix.QueryBranch.bind source "root" root
  have current (name : String) (different : ofString "root"≠ofString name) : ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    WitnessRadix.QueryBranch.bind_lookup_other source "root" name root different
  have currentScratch:=scratch.of_fields source ready cursor frame rfl rfl
  obtain ⟨output⟩:=after_root_normal ready inner value heap cursor frame root m key length pointer size graph limit nodeLower pathLower property
    valuesModel regions disjoint paths pathRegions separated query member small empty owned
    (WitnessRadix.QueryBranch.bind_lookup_same _ _ _) ((current _ (by decide)).trans mCell) mapped headerSafe headerAbove headerBefore headerAway
    ((current _ (by decide)).trans nkCell) ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell)
    heapCell heapArena heapAligned currentScratch scratchBefore floor pathFloor nodeFloor little installed continued
  rw [endpoint]
  exact ⟨{output with}⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.after_key_normal
