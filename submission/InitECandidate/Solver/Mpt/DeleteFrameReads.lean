import InitECandidate.Solver.Mpt.DeleteFrameOwnership
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every initialized physical saved word can be read by the original
unwind expressions, using its actual mapping and current top binding. -/
theorem Saved.View.field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved)
    (view : saved.View source) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)))
    (field : LocalFields.Field) (member : field∈saved.kind.fields saved.words) :
    eval source (DeleteBody.field "top" (BitVec.ofNat 64 field.offset))=some (.val (.word field.value.word)) := by
  have geometry:=saved.kind.geometry saved.words field member
  exact DeleteExtension.field_read source "top" saved.pointer (BitVec.ofNat 64 field.offset) field.value.word topCell
    (field_mapped source saved.pointer view.arena view.aligned domain field.offset (by omega) geometry.2) (view.cells field member)

theorem Saved.View.node_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved)
    (view : saved.View source) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer))) :
    eval source (DeleteBody.field "top" 8#64)=some (.val (.word saved.node)) := by
  have member : (⟨8,.saved "node" (saved.words "node")⟩ : LocalFields.Field)∈saved.kind.fields saved.words:=by
    cases saved.kind <;> simp [Kind.fields]
  simpa only [Saved.node,LocalFields.Operand.word] using view.field_read source saved domain topCell _ member

theorem Saved.View.tag_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved)
    (view : saved.View source) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer))) :
    eval source (DeleteBody.field "top" 16#64)=some (.val (.word saved.kind.tag)) := by
  have member : (⟨16,.literal saved.kind.tag⟩ : LocalFields.Field)∈saved.kind.fields saved.words:=by
    cases saved.kind <;> simp [Kind.fields,Kind.tag]
  simpa only [LocalFields.Operand.word] using view.field_read source saved domain topCell _ member

/-- The saved extension operands still designate its genuine protected
full stored path after mutations. The caller supplies the actual current
registry and path facts, not a future successful helper run. -/
theorem Saved.Owned.extension_buffer (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (lower upper : Nat)
    (owned : saved.Owned graph) (extensionKind : saved.kind=.extension)
    (paths : graph.PathBytes source.be) (regions : graph.PathRegions lower upper) (separated : graph.PathSeparated) :
    graph.PathBuffer source.be lower upper (saved.words "seg") (saved.words "sl").toNat ∧ 0<(saved.words "sl").toNat := by
  obtain ⟨member,active,tag,data⟩:=owned
  have actualTag : wordAt source.memory saved.node=2#64:=by simpa only [extensionKind,Kind.tag] using tag
  have actualFields : wordAt source.memory (saved.node+32#64)=saved.words "seg" ∧
      wordAt source.memory (saved.node+40#64)=saved.words "sl":=by simpa only [extensionKind] using data
  have buffer:=TrieWalk.Graph.PathBuffer.stored graph source.be lower upper paths regions separated saved.node member active (Or.inr actualTag)
  have positive:=paths.positive saved.node member active actualTag
  rw [actualFields.1,actualFields.2] at buffer
  rw [actualFields.2] at positive
  exact ⟨buffer,positive⟩

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.View.field_read
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.View.node_read
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.View.tag_read
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.Owned.extension_buffer
