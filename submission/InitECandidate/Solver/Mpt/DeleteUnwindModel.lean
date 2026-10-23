import InitECandidate.Solver.Mpt.DeleteUnwindOutput
import InitECandidate.Solver.Mpt.DeleteFramePop
import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Current physical state of the original return-unwind loop. Its rank
is the number of genuinely pushed records, independent of trie edges. -/
structure UnwindModel (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop) where
  heap : BitVec 64
  cursor : BitVec 64
  frame : BitVec 64
  top : BitVec 64
  result : BitVec 64
  frames : List DeleteFrame.Saved
  topCell : source.locals.lookup (ofString "top")=some (.val (.word top))
  resultCell : source.locals.lookup (ofString "res")=some (.val (.word result))
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  scratch : Rlp.Validation.Arena source cursor frame
  scratchBefore : cursor.toNat≤DeleteFrame.ceiling
  floor : DeleteFrame.ceiling≤pathLower
  pathFloor : pathLower≤nodeLower
  nodeFloor : nodeLower≤heap.toNat
  little : source.be=false
  installed : Input.OriginalCode.Installed source.code
  graph : TrieWalk.Graph source.memory source.memaddrs
  resultMember : graph.valid result
  values : TrieWalk.Values graph limit property
  regions : graph.Regions nodeLower heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes source.be
  pathRegions : graph.PathRegions pathLower heap.toNat
  separated : graph.PathSeparated
  stack : DeleteFrame.Stack source cursor.toNat top frames
  parents : DeleteFrame.Parents graph frames
  bounded : frames.length≤64

def UnwindModel.with_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (clock : Nat) :
    UnwindModel {source with clock:=clock} limit nodeLower pathLower property :=
  {model with
    scratch:=model.scratch.of_fields source _ model.cursor model.frame rfl rfl
    stack:=model.stack.of_memory source _ model.cursor.toNat model.top model.frames (by intros; rfl)}

def UnwindModel.bind_other (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (name : String) (word : BitVec 64)
    (notTop : ofString name≠ofString "top") (notResult : ofString name≠ofString "res") :
    UnwindModel (QueryBranch.bind source name word) limit nodeLower pathLower property :=
  {model with
    topCell:=(bind_lookup_other source name "top" word notTop).trans model.topCell
    resultCell:=(bind_lookup_other source name "res" word notResult).trans model.resultCell
    scratch:=model.scratch.of_fields source _ model.cursor model.frame rfl rfl
    stack:=model.stack.of_memory source _ model.cursor.toNat model.top model.frames (by intros; rfl)}

def UnwindModel.restore_other (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (name : String)
    (notTop : ofString "top"≠ofString name) (notResult : ofString "res"≠ofString name) :
    UnwindModel (QueryBranch.restore origin name source) limit nodeLower pathLower property :=
  {model with
    topCell:=(restore_lookup_other origin source name "top" notTop).trans model.topCell
    resultCell:=(restore_lookup_other origin source name "res" notResult).trans model.resultCell
    scratch:=model.scratch.of_fields source _ model.cursor model.frame rfl rfl
    stack:=model.stack.of_memory source _ model.cursor.toNat model.top model.frames (by intros; rfl)}

theorem UnwindModel.empty_iff (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) : model.frames=[] ↔ model.top=0#64 := by
  constructor
  · intro empty
    have stack:=model.stack
    rw [empty] at stack
    exact stack
  · intro zero
    have stack:=model.stack
    cases framesEq : model.frames with
    | nil=>rfl
    | cons saved tail=>
      rw [framesEq] at stack
      exact False.elim ((stack.2.2.1.nonzero source saved) (stack.1.symm.trans zero))

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.UnwindModel.empty_iff
