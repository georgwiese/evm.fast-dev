import InitECandidate.Solver.Mpt.DeleteDescentModel
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def UnwindModel.bind_result (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (root : BitVec 64) (member : model.graph.valid root) :
    UnwindModel (QueryBranch.bind source "res" root) limit nodeLower pathLower property :=
  {model with
    result:=root
    topCell:=(bind_lookup_other source "res" "top" root (by decide)).trans model.topCell
    resultCell:=bind_lookup_same _ _ _
    resultMember:=member
    scratch:=model.scratch.of_fields source _ model.cursor model.frame rfl rfl
    stack:=model.stack.of_memory source _ model.cursor.toNat model.top model.frames (by intros; rfl)}

/-- Assigning a genuinely registered result changes no key bytes,
saved record, parent descriptor or allocator cursor. -/
def DescentModel.bind_result (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (root : BitVec 64) (member : model.pending.graph.valid root) :
    DescentModel (QueryBranch.bind source "res" root) key length limit nodeLower pathLower property :=
  {model with
    pending:=model.pending.bind_result source limit nodeLower pathLower property root member
    keyCell:=(bind_lookup_other source "res" "key" root (by decide)).trans model.keyCell
    lengthCell:=(bind_lookup_other source "res" "klen" root (by decide)).trans model.lengthCell
    nodeCell:=(bind_lookup_other source "res" "node" root (by decide)).trans model.nodeCell
    levelCell:=(bind_lookup_other source "res" "level" root (by decide)).trans model.levelCell
    goCell:=(bind_lookup_other source "res" "go" root (by decide)).trans model.goCell}

def DescentModel.clear_go (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) :
    DescentModel (QueryBranch.bind source "go" 0#64) key length limit nodeLower pathLower property :=
  {model with
    pending:=model.pending.bind_other source limit nodeLower pathLower property "go" 0#64 (by decide) (by decide)
    go:=0#64
    keyCell:=(bind_lookup_other source "go" "key" 0#64 (by decide)).trans model.keyCell
    lengthCell:=(bind_lookup_other source "go" "klen" 0#64 (by decide)).trans model.lengthCell
    nodeCell:=(bind_lookup_other source "go" "node" 0#64 (by decide)).trans model.nodeCell
    levelCell:=(bind_lookup_other source "go" "level" 0#64 (by decide)).trans model.levelCell
    goCell:=bind_lookup_same _ _ _
    goTyped:=Or.inl rfl}

theorem clear_go_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) :
    evaluateHOLFiniteState source (.assign .local (ofString "go") (.const 0#64))=(none,QueryBranch.bind source "go" 0#64) :=
  StateSteps.assign_execute source "go" (.const 0#64) model.go 0#64 model.goCell rfl

theorem assign_result_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (expression : ExpHOL 64) (root : BitVec 64)
    (read : eval source expression=some (.val (.word root))) :
    evaluateHOLFiniteState source (.assign .local (ofString "res") expression)=(none,QueryBranch.bind source "res" root) :=
  StateSteps.assign_execute source "res" expression model.pending.result root model.pending.resultCell read

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.clear_go_execute
#print axioms InitECandidate.Solver.Mpt.DeleteBody.assign_result_execute
