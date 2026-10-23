import InitECandidate.Solver.Mpt.DeleteUnwindModel

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Current original descent state. The pending stack already satisfies
the unwind invariant, while actual query progress limits further pushes.
The whole query remains protected through the terminal descent choice. -/
structure DescentModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop) where
  pending : UnwindModel source limit nodeLower pathLower property
  node : BitVec 64
  level : BitVec 64
  go : BitVec 64
  keyCell : source.locals.lookup (ofString "key")=some (.val (.word key))
  lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length))
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  levelCell : source.locals.lookup (ofString "level")=some (.val (.word level))
  goCell : source.locals.lookup (ofString "go")=some (.val (.word go))
  goTyped : go=0#64 ∨ go=1#64
  bounded : length.toNat≤64
  levelBound : level.toNat≤length.toNat
  depthBound : pending.frames.length≤level.toNat
  nodeMember : pending.graph.valid node
  query : pending.graph.PathBuffer source.be pathLower pending.heap.toNat key length.toNat

def descentLocals : List MlS:=[ofString "top",ofString "res",ofString "node",ofString "key",ofString "klen",ofString "level",ofString "go"]

theorem auxiliary_other (name : String) (fresh : ofString name∉descentLocals) (key : String) (member : ofString key∈descentLocals) :
    ofString name≠ofString key := by
  intro same
  apply fresh
  rw [same]
  exact member

def DescentModel.with_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (clock : Nat) :
    DescentModel {source with clock:=clock} key length limit nodeLower pathLower property :=
  {model with pending:=model.pending.with_clock source limit nodeLower pathLower property clock}

def DescentModel.bind_auxiliary (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (name : String) (word : BitVec 64)
    (fresh : ofString name∉descentLocals) :
    DescentModel (QueryBranch.bind source name word) key length limit nodeLower pathLower property := by
  have other (key : String) (member : ofString key∈descentLocals) := auxiliary_other name fresh key member
  exact {model with
    pending:=model.pending.bind_other source limit nodeLower pathLower property name word (other "top" (by simp [descentLocals])) (other "res" (by simp [descentLocals]))
    keyCell:=(bind_lookup_other source name "key" word (other "key" (by simp [descentLocals]))).trans model.keyCell
    lengthCell:=(bind_lookup_other source name "klen" word (other "klen" (by simp [descentLocals]))).trans model.lengthCell
    nodeCell:=(bind_lookup_other source name "node" word (other "node" (by simp [descentLocals]))).trans model.nodeCell
    levelCell:=(bind_lookup_other source name "level" word (other "level" (by simp [descentLocals]))).trans model.levelCell
    goCell:=(bind_lookup_other source name "go" word (other "go" (by simp [descentLocals]))).trans model.goCell }

def DescentModel.restore_auxiliary (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (name : String)
    (fresh : ofString name∉descentLocals) :
    DescentModel (QueryBranch.restore origin name source) key length limit nodeLower pathLower property := by
  have other (key : String) (member : ofString key∈descentLocals) := (auxiliary_other name fresh key member).symm
  exact {model with
    pending:=model.pending.restore_other origin source limit nodeLower pathLower property name (other "top" (by simp [descentLocals])) (other "res" (by simp [descentLocals]))
    keyCell:=(restore_lookup_other origin source name "key" (other "key" (by simp [descentLocals]))).trans model.keyCell
    lengthCell:=(restore_lookup_other origin source name "klen" (other "klen" (by simp [descentLocals]))).trans model.lengthCell
    nodeCell:=(restore_lookup_other origin source name "node" (other "node" (by simp [descentLocals]))).trans model.nodeCell
    levelCell:=(restore_lookup_other origin source name "level" (other "level" (by simp [descentLocals]))).trans model.levelCell
    goCell:=(restore_lookup_other origin source name "go" (other "go" (by simp [descentLocals]))).trans model.goCell }

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.auxiliary_other
