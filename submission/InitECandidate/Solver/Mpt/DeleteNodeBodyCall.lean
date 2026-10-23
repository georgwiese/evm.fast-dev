import InitECandidate.Solver.Mpt.DeleteNodeHandler
import InitECandidate.Solver.Mpt.DeleteNormal
import InitECandidate.Solver.Mpt.DeleteCost
import InitECandidate.Solver.Input.CaughtAssignedStops
import InitECandidate.Solver.Input.ClockCostCaughtAssigned
import InitECandidate.Solver.Input.WordQuadEnvironment

namespace InitECandidate.Solver.Mpt.DeleteNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem body_environment (code) (installed : Input.OriginalCode.Installed code) (node key length level : BitVec 64) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite code.lookup (ofString "_mpt_delete_node_body") [.val (.word node),.val (.word key),.val (.word length),.val (.word level)]=some (DeleteBody.body,callee,.one) ∧
      callee.lookup (ofString "node")=some (.val (.word node)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) ∧
      callee.lookup (ofString "klen")=some (.val (.word length)) ∧ callee.lookup (ofString "level")=some (.val (.word level)) :=
  Input.word_quad_environment code.lookup (ofString "_mpt_delete_node_body") (ofString "node") (ofString "key") (ofString "klen") (ofString "level") DeleteBody.body .one
    node key length level (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (DeleteBody.original_code code installed)

theorem body_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node key length level : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word node),.val (.word key),.val (.word length),.val (.word level)] := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,nodeCell,keyCell,lengthCell,levelCell]

/-- A genuine normal caught assigned call must receive the real body
return: release/rethrow cannot fall through. Its actual callee supplies
the full physical deletion output before caller locals are restored. -/
theorem caught_body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame node key length level : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (small : length.toNat≤64) (within : level.toNat≤length.toNat) (empty : property 0#64 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source caughtCall=(none,target)) :
    ∃ returned : ValueHOL 64,target.locals=source.locals.update (ofString "res",returned) ∧
      Nonempty (DeleteBody.BodyOutput source target returned graph heap cursor frame limit nodeLower pathLower property) := by
  obtain ⟨callee,called,calleeNode,calleeKey,calleeLength,calleeLevel⟩:=body_environment source.code installed node key length level
  have args:=body_arguments_read source node key length level nodeCell keyCell lengthCell levelCell
  rw [shapes.2.2.2.2.2] at normal
  obtain ⟨_funded,childTarget,returned,run,_checked,endpoint⟩:=Input.CallNormal.assigned_caught_stops source target (ofString "res") (ofString "_mpt_delete_node_body") arguments _ DeleteBody.body callee .one
    (ofString "MptErr") (ofString "e") handler args called (fun current _code=>handler_stops current) normal
  let entry:=callEntryStateHOLFinite source callee
  have entryScratch:=scratch.of_fields source entry cursor frame rfl rfl
  obtain ⟨output⟩:=DeleteBody.body_path_normal entry childTarget returned heap cursor frame node key length level graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member
    calleeNode calleeKey calleeLength calleeLevel small within empty heapCell heapArena heapAligned entryScratch scratchBefore floor pathFloor nodeFloor little installed run
  rw [endpoint]
  exact ⟨returned,rfl,⟨{output with scratch:=output.scratch.of_fields childTarget _ output.finalCursor frame rfl rfl}⟩⟩

/-- Every outcome of the real caught call, including its release/rethrow
handler, bounded from the current original four-word callee entry. -/
theorem caught_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame node key length level : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (small : length.toNat≤64) (within : level.toNat≤length.toNat) (empty : property 0#64 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source caughtCall).2.clock≤DeleteBody.bodyAllowance pathLower+2 := by
  obtain ⟨callee,called,calleeNode,calleeKey,calleeLength,calleeLevel⟩:=body_environment source.code installed node key length level
  have args:=body_arguments_read source node key length level nodeCell keyCell lengthCell levelCell
  let entry:=callEntryStateHOLFinite source callee
  have entryScratch:=scratch.of_fields source entry cursor frame rfl rfl
  have priced:=DeleteBody.body_cost entry heap cursor frame node key length level graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member
    calleeNode calleeKey calleeLength calleeLevel small within empty heapCell heapArena heapAligned entryScratch scratchBefore floor pathFloor nodeFloor little installed
  rw [shapes.2.2.2.2.2]
  exact Input.ClockCost.caught_destination_current source (some (.local,ofString "res")) (ofString "_mpt_delete_node_body") arguments _ DeleteBody.body callee .one
    (ofString "MptErr") (ofString "e") handler (DeleteBody.bodyAllowance pathLower) 1 args called priced (handler_price source.code installed)

end InitECandidate.Solver.Mpt.DeleteNode

#print axioms InitECandidate.Solver.Mpt.DeleteNode.body_environment
#print axioms InitECandidate.Solver.Mpt.DeleteNode.body_arguments_read
#print axioms InitECandidate.Solver.Mpt.DeleteNode.caught_body_normal
#print axioms InitECandidate.Solver.Mpt.DeleteNode.caught_body_cost
