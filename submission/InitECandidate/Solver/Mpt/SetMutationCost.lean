import InitECandidate.Solver.Mpt.SetMutationDispatch
import InitECandidate.Solver.Mpt.InsertGeneralCallCost

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def mutationAllowance (pathLower : Nat) : Nat:=max 36791 (DeleteBody.bodyAllowance pathLower+5)

/-- Every outcome of the actual original mutation choice. Payload facts
are needed only for a currently nonzero pointer AND length; deletion
does not presume a mapped nonempty payload at address zero. -/
theorem mutation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame root key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid root)
    (small : length.toNat≤64) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source mutationChoice).2.clock≤mutationAllowance pathLower := by
  rw [mutation_dispatch source pointer size pointerCell sizeCell]
  by_cases absent : pointer=0#64 ∨ size=0#64
  · rw [if_pos absent,deletion_shape]
    exact (DeleteNode.assigned_cost source heap cursor frame root key length 0#64 graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member
      small (by simp) empty heapCell heapArena heapAligned scratch scratchBefore floor pathFloor nodeFloor little installed (ofString "root") deleteArguments
        (delete_arguments source root key length rootCell nkCell)).trans (Nat.le_max_right _ _)
  · rw [if_neg absent]
    obtain ⟨payload,extra⟩:=owned (fun zero=>absent (Or.inl zero)) (fun zero=>absent (Or.inr zero))
    exact (Insert.general_call_cost source heap root key 0#64 length pointer size graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member
      (by simp) small payload extra empty nodeFloor scratch.domain installed heapCell heapArena heapAligned (some (some (ofString "root"))) insertArguments
        (insert_arguments source root key length pointer size rootCell nkCell pointerCell sizeCell)).trans (Nat.le_max_left _ _)

theorem after_root_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame root key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid root)
    (small : length.toNat≤64) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterRoot).2.clock≤mutationAllowance pathLower := by
  have priced:=mutation_cost source heap cursor frame root key length pointer size graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member small empty owned
    rootCell nkCell pointerCell sizeCell heapCell heapArena heapAligned scratch scratchBefore floor pathFloor nodeFloor little installed
  rw [mutation_shapes.2.1]
  exact Input.ClockCost.sequence_current source mutationChoice footer (mutationAllowance pathLower) 0 priced
    (Input.ClockCost.of_quiet source.code footer (footer_quiet source.code))

/-- Price the genuine root declaration and whole mutation/footer suffix
at the current post-key graph. Reading or storing a bad header aborts
without adding source call/loop ticks. -/
theorem after_key_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame root m key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid root)
    (small : length.toNat≤64) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m))) (mapped : source.memaddrs m) (stored : source.memory m=.word root)
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterKey).2.clock≤mutationAllowance pathLower := by
  have read : eval source rootExpression=some (.val (.word root)):=by
    simp [eval,rootExpression,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,mCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]
  let ready:=QueryBranch.bind source "root" root
  have currentNk : ready.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]):=
    (bind_lookup_other source "root" "nk" root (by decide)).trans nkCell
  have currentPointer : ready.locals.lookup (ofString "vptr")=some (.val (.word pointer)):=
    (bind_lookup_other source "root" "vptr" root (by decide)).trans pointerCell
  have currentSize : ready.locals.lookup (ofString "vlen")=some (.val (.word size)):=
    (bind_lookup_other source "root" "vlen" root (by decide)).trans sizeCell
  have currentScratch:=scratch.of_fields source ready cursor frame rfl rfl
  rw [mutation_shapes.1]
  exact Input.ClockCost.declared_current source "root" rootExpression root afterRoot _ read
    (after_root_cost ready heap cursor frame root key length pointer size graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member small empty owned
      (bind_lookup_same _ _ _) currentNk currentPointer currentSize heapCell heapArena heapAligned currentScratch scratchBefore floor pathFloor nodeFloor little installed)

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.mutation_cost
#print axioms InitECandidate.Solver.Mpt.SetTrie.after_root_cost
#print axioms InitECandidate.Solver.Mpt.SetTrie.after_key_cost
