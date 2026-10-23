import InitECandidate.Solver.Mpt.DeleteDescentModel
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem descent_path_reads (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64 ∨ wordAt source.memory model.node=2#64) :
    eval source (field "node" 32#64)=some (.val (.word (wordAt source.memory (model.node+32#64)))) ∧
      eval source (field "node" 40#64)=some (.val (.word (wordAt source.memory (model.node+40#64)))) := by
  let view:=model.pending.graph.path model.node model.nodeMember active tag
  have pointer : wordAt source.memory (model.node+32#64)=view.pointer:=by simp [wordAt,view.pointerStored,MemoryBytes.wordBits]
  have size : wordAt source.memory (model.node+40#64)=view.size:=by simp [wordAt,view.sizeStored,MemoryBytes.wordBits]
  constructor
  · rw [pointer]
    exact DeleteExtension.field_read source "node" model.node 32#64 view.pointer model.nodeCell view.pointerMapped view.pointerStored
  · rw [size]
    exact DeleteExtension.field_read source "node" model.node 40#64 view.size model.nodeCell view.sizeMapped view.sizeStored

theorem descent_query_reads (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) :
    eval source keySuffix=some (.val (.word (key+model.level))) ∧
      eval source remaining=some (.val (.word (length-model.level))) := by
  constructor <;>
    simp [eval,keySuffix,remaining,localVar,evalHOLExact,evalListHOLExact,toExact,model.keyCell,model.lengthCell,model.levelCell,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem descent_remaining_number (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) :
    (length-model.level).toNat=length.toNat-model.level.toNat :=
  BitVec.toNat_sub_of_le (by change model.level.toNat≤length.toNat; exact model.levelBound)

/-- The real remaining query is a protected window of the original full
key; its backing-word mapping is valid even at an unaligned position. -/
theorem descent_query_suffix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) :
    model.pending.graph.PathBuffer source.be pathLower model.pending.heap.toNat (key+model.level) (length-model.level).toNat := by
  have number:=descent_remaining_number source key length limit nodeLower pathLower property model
  exact model.query.window model.pending.graph source.be pathLower model.pending.heap.toNat key model.level length.toNat (length-model.level).toNat model.levelBound (by rw [number])

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_path_reads
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_query_reads
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_remaining_number
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_query_suffix
