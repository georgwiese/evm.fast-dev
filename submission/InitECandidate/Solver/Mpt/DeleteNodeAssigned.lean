import InitECandidate.Solver.Mpt.DeleteNodeNormal
import InitECandidate.Solver.Mpt.DeleteNodeCost
import InitECandidate.Solver.Input.AssignedCallKnown
import InitECandidate.Solver.Input.ClockCostAssignedCurrent

namespace InitECandidate.Solver.Mpt.DeleteNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

def values (node key length level : BitVec 64) : List (ValueHOL 64):=[.val (.word node),.val (.word key),.val (.word length),.val (.word level)]

theorem environment (code) (installed : Input.OriginalCode.Installed code) (node key length level : BitVec 64) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite code.lookup (ofString "_mpt_delete_node") (values node key length level)=some (body,callee,.one) ∧
      callee.lookup (ofString "node")=some (.val (.word node)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) ∧
      callee.lookup (ofString "klen")=some (.val (.word length)) ∧ callee.lookup (ofString "level")=some (.val (.word level)) :=
  Input.word_quad_environment code.lookup (ofString "_mpt_delete_node") (ofString "node") (ofString "key") (ofString "klen") (ofString "level") body .one
    node key length level (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (original_code code installed)

/-- Real assigned original255 caller: derive its actual callee run,
restored root binding and complete physical result, including the true
restored scratch mark. Argument expressions may be the setter tuple. -/
theorem assigned_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame node key length level : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (small : length.toNat≤64) (within : level.toNat≤length.toNat) (empty : property 0#64 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values node key length level))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_mpt_delete_node") arguments)=(none,target)) :
    ∃ returned : ValueHOL 64,target.locals=source.locals.update (name,returned) ∧
      Nonempty (Output source target returned graph heap cursor frame limit nodeLower pathLower property) := by
  obtain ⟨callee,called,nodeCell,keyCell,lengthCell,levelCell⟩:=environment source.code installed node key length level
  obtain ⟨_funded,childTarget,returned,run,endpoint⟩:=Input.CallNormal.local_known source target name (ofString "_mpt_delete_node") arguments _ body callee .one args called normal
  let entry:=callEntryStateHOLFinite source callee
  have entryScratch:=scratch.of_fields source entry cursor frame rfl rfl
  obtain ⟨output⟩:=body_path_normal entry childTarget returned heap cursor frame node key length level graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member
    nodeCell keyCell lengthCell levelCell small within empty heapCell heapArena heapAligned entryScratch scratchBefore floor pathFloor nodeFloor little installed run
  rw [endpoint]
  exact ⟨returned,rfl,⟨{output with scratch:=output.scratch.of_fields childTarget _ output.finalCursor frame rfl rfl}⟩⟩

/-- Every outcome of the actual assigned deletion caller has only its
one caller tick in addition to the checked full wrapper allowance. -/
theorem assigned_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame node key length level : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (small : length.toNat≤64) (within : level.toNat≤length.toNat) (empty : property 0#64 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values node key length level)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_mpt_delete_node") arguments)).2.clock≤DeleteBody.bodyAllowance pathLower+5 := by
  obtain ⟨callee,called,nodeCell,keyCell,lengthCell,levelCell⟩:=environment source.code installed node key length level
  let entry:=callEntryStateHOLFinite source callee
  have entryScratch:=scratch.of_fields source entry cursor frame rfl rfl
  have priced:=body_cost entry heap cursor frame node key length level graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member
    nodeCell keyCell lengthCell levelCell small within empty heapCell heapArena heapAligned entryScratch scratchBefore floor pathFloor nodeFloor little installed
  exact Input.ClockCost.assigned_current source (some (.local,name)) (ofString "_mpt_delete_node") arguments _ body callee .one (DeleteBody.bodyAllowance pathLower+4) args called priced

end InitECandidate.Solver.Mpt.DeleteNode

#print axioms InitECandidate.Solver.Mpt.DeleteNode.environment
#print axioms InitECandidate.Solver.Mpt.DeleteNode.assigned_normal
#print axioms InitECandidate.Solver.Mpt.DeleteNode.assigned_cost
