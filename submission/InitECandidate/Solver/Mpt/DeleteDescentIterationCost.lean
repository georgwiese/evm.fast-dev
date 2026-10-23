import InitECandidate.Solver.Mpt.DeleteDescentKindCost
import InitECandidate.Solver.Mpt.DeleteDescentInvalidate
import InitECandidate.Solver.Mpt.DeleteDescentPure
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_hash_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length tag : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (tagEq : wordAt source.memory model.node=tag) (notHash : tag≠0#64) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source afterHash).2.clock≤descentChoiceAllowance model.pending.heap pathLower+1 := by
  let invalidation : ProgHOL 64:=.call (some (none,none)) (ofString "node_invalidate") [localVar "node"]
  have front : source.clock-(evaluateHOLFiniteState source invalidation).2.clock≤1:=
    Input.ClockCost.call_body source.code (some none) (ofString "node_invalidate") [localVar "node"] NodeInvalidate.formals NodeInvalidate.body .one 0
      (NodeInvalidate.original_code source.code model.pending.installed) (Input.ClockCost.of_quiet source.code NodeInvalidate.body (NodeInvalidate.quiet source.code)) source rfl
  have back (middle : PanSemStateFiniteExact 64 Guest.HostMemory) (normal : evaluateHOLFiniteState source invalidation=(none,middle)) :
      middle.clock-(evaluateHOLFiniteState middle kindChoice).2.clock≤descentChoiceAllowance model.pending.heap pathLower:=by
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "node"]=some [.val (.word model.node)]:=by
      simp [evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,model.nodeCell]
    have bounds:=model.pending.regions model.node model.nodeMember active
    have middleEq:=NodeInvalidate.call_normal source middle model.node [localVar "node"] args model.pending.installed model.pending.scratch.domain
      (AllocatedBytes.Arena.weaken model.node _ 32 bounds.2.1 (TrieWalk.nodeBytes_bounds (wordAt source.memory model.node)).1) bounds.2.2.1 normal
    obtain ⟨current,heapEq,_cursorEq,_frameEq,_framesEq,_validEq,nodeEq,_levelEq,_goEq,fields,_memory,_price⟩:=
      invalidate_descent_normal source middle key length limit nodeLower pathLower property model active normal
    have currentActive : current.node≠0#64:=by rw [nodeEq]; exact active
    have currentTag : wordAt middle.memory current.node=tag:=by rw [nodeEq]; exact (fields.tags model.node model.nodeMember active).trans tagEq
    have currentCell : middle.locals.lookup (ofString "k")=some (.val (.word tag)):=by rw [middleEq]; exact tagCell
    have priced:=kind_cost middle key length tag limit nodeLower pathLower property current currentActive currentCell currentTag notHash empty
    rwa [heapEq] at priced
  rw [descent_shapes.2.2.2.2.2.2.1]
  have priced:=Input.ClockCost.sequence_reached_current source invalidation kindChoice 1 (descentChoiceAllowance model.pending.heap pathLower) front back
  exact priced.trans (by omega)

theorem after_kind_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length tag : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (tagEq : wordAt source.memory model.node=tag) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source afterKind).2.clock≤descentChoiceAllowance model.pending.heap pathLower+2 := by
  have guardPrice : Input.ClockCost.Bound source.code hashGuard 1:=by
    rw [descent_shapes.2.2.2.2.2.1]
    exact Input.ClockCost.conditional source.code _ _ _ 1 0 (Fail.call_price source.code model.pending.installed [.const 2#64]) (Input.ClockCost.skip source.code)
  have back (middle : PanSemStateFiniteExact 64 Guest.HostMemory) (normal : evaluateHOLFiniteState source hashGuard=(none,middle)) :
      middle.clock-(evaluateHOLFiniteState middle afterHash).2.clock≤descentChoiceAllowance model.pending.heap pathLower+1:=by
    obtain ⟨middleEq,notHash⟩:=delete_hash_guard_normal source middle tag tagCell model.pending.installed normal
    subst middle
    exact after_hash_cost source key length tag limit nodeLower pathLower property model active tagCell tagEq notHash empty
  rw [descent_shapes.2.2.2.2.1]
  have priced:=Input.ClockCost.sequence_reached_current source hashGuard afterHash 1 (descentChoiceAllowance model.pending.heap pathLower+1) (guardPrice source rfl) back
  omega

theorem node_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source nodeChoice).2.clock≤descentChoiceAllowance model.pending.heap pathLower+2 := by
  by_cases null : model.node=0#64
  · have chosen : evaluateHOLFiniteState source nodeChoice=evaluateHOLFiniteState source (.assign .local (ofString "res") (.const 0#64)):=by
      rw [descent_shapes.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,model.nodeCell,null,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [chosen]
    exact (Input.ClockCost.assign source.code (ofString "res") (.const 0#64) source rfl).trans (Nat.zero_le _)
  · have chosen : evaluateHOLFiniteState source nodeChoice=evaluateHOLFiniteState source nonempty:=by
      rw [descent_shapes.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,model.nodeCell,null,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    obtain ⟨mapped,stored⟩:=model.pending.graph.header model.node model.nodeMember null
    have read : eval source (field "node" 0#64)=some (.val (.word (wordAt source.memory model.node))):=
      DeleteExtension.field_read source "node" model.node 0#64 _ model.nodeCell (by simpa only [BitVec.add_zero] using mapped) (by simpa only [BitVec.add_zero] using stored)
    let tag:=wordAt source.memory model.node
    let enteredState:=QueryBranch.bind source "k" tag
    let entered:=model.bind_auxiliary source key length limit nodeLower pathLower property "k" tag (by decide)
    have tagCell : enteredState.locals.lookup (ofString "k")=some (.val (.word tag)):=bind_lookup_same _ _ _
    rw [chosen,descent_shapes.2.2.2.1]
    exact Input.ClockCost.declared_current source "k" (field "node" 0#64) tag afterKind _ read
      (after_kind_cost enteredState key length tag limit nodeLower pathLower property entered null tagCell rfl empty)

theorem descent_iteration_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source descentBody).2.clock≤descentChoiceAllowance model.pending.heap pathLower+2 := by
  have cleared:=clear_go_execute source key length limit nodeLower pathLower property model
  rw [descent_shapes.2.1,StateSteps.next_sequence source (QueryBranch.bind source "go" 0#64) _ nodeChoice cleared (Nat.le_refl _)]
  exact node_choice_cost (QueryBranch.bind source "go" 0#64) key length limit nodeLower pathLower property
    (model.clear_go source key length limit nodeLower pathLower property) empty

/-- Intermediate uniform physical-heap allowance; the final bound must
still amortize actual path copying across mutations. -/
def descentAllowance (pathLower : Nat) : Nat:=max 68 ((33806089496-pathLower)/8+40)+2

theorem descent_iteration_uniform_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source descentBody).2.clock≤descentAllowance pathLower := by
  have priced:=descent_iteration_cost source key length limit nodeLower pathLower property model empty
  have heapBound : model.pending.heap.toNat≤33806089496:=model.pending.heapArena.upper
  have difference:=Nat.sub_le_sub_right heapBound pathLower
  have quotient : (model.pending.heap.toNat-pathLower)/8≤(33806089496-pathLower)/8:=Nat.div_le_div_right difference
  unfold descentChoiceAllowance at priced
  unfold descentAllowance
  omega

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.after_hash_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.after_kind_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.node_choice_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_iteration_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_iteration_uniform_cost
