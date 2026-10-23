import InitECandidate.Solver.Mpt.DeleteDescentInitial
import InitECandidate.Solver.Mpt.DeleteDescentNormal
import InitECandidate.Solver.Mpt.DeleteDescentCost
import InitECandidate.Solver.Mpt.DeleteUnwindCost
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual setup declarations reach their genuine initialized
remainder without spending source call/loop clocks. -/
theorem setup_execution (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Input.CallPrefix.Execution source actions (setup source) := by
  exact .step (.declare source (ofString "top") .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact]))
    (.step (.declare _ (ofString "res") .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact]))
      (.step (.declare _ (ofString "go") .one (.const 1#64) (.val (.word 1#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact])) (.done _)))

/-- Intermediate physical-path allowance. It counts source calls and
loop ticks; final target accounting must still amortize actual copying. -/
def bodyAllowance (pathLower : Nat) : Nat:=(descentAllowance pathLower+1)*65+(unwindAllowance pathLower+1)*64

theorem after_go_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source afterGo).2.clock≤bodyAllowance pathLower := by
  have front:=descent_cost source key length limit nodeLower pathLower property model empty
  have back (middle : PanSemStateFiniteExact 64 Guest.HostMemory) (normal : evaluateHOLFiniteState source descent=(none,middle)) :
      middle.clock-(evaluateHOLFiniteState middle afterDescent).2.clock≤(unwindAllowance pathLower+1)*64:=by
    obtain ⟨⟨output,_stopped⟩⟩:=descent_path_normal source middle key length limit nodeLower pathLower property model empty normal
    have priced:=unwind_cost middle limit nodeLower pathLower property output.next.pending
    have returned : Input.ClockCost.Bound middle.code footer 0:=by
      rw [setup_shapes.2.2.2.2.2]
      exact Input.ClockCost.returned middle.code (localVar "res")
    have combined:=Input.ClockCost.sequence_current middle unwind footer ((unwindAllowance pathLower+1)*64) 0 priced returned
    rw [setup_shapes.2.2.2.2.1]
    exact combined
  rw [setup_shapes.2.2.2.1]
  exact Input.ClockCost.sequence_reached_current source descent afterDescent ((descentAllowance pathLower+1)*65) ((unwindAllowance pathLower+1)*64) front back

/-- All outcomes of the entire unchanged254 body. Both true loop bounds
are joined only at an actually reached continuing descent state; setup
and lexical restoration add no source clocks. No future success is an
entry condition, including on allocation failure, error or timeout. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyAllowance pathLower := by
  obtain ⟨initial,_heap,_members,_frames,_go,_cursor,_frame,_node,_level,_graph⟩:=initial_descent_model source heap cursor frame node key length level graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated query member nodeCell keyCell lengthCell levelCell small within heapCell heapArena heapAligned scratch scratchBefore floor pathFloor nodeFloor little installed
  have priced:=after_go_cost (setup source) key length limit nodeLower pathLower property initial empty
  have clocks:=congrArg Prod.snd ((setup_execution source).project afterGo)
  change (evaluateHOLFiniteState source (Input.CallPrefix.program actions afterGo)).2.clock=(evaluateHOLFiniteState (setup source) afterGo).2.clock at clocks
  rw [←body_setup_shape] at clocks
  rw [clocks]
  exact priced

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.setup_execution
#print axioms InitECandidate.Solver.Mpt.DeleteBody.after_go_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.body_cost
