import InitECandidate.Solver.Mpt.DeleteDescentPushNormal

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original matched-extension allocation and push, using the real
current segment fields and only the already consumed comparison bound.
No successful allocator return or future child model is assumed. -/
theorem extension_matched_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length segment size : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=2#64)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (sizeCell : source.locals.lookup (ofString "sl")=some (.val (.word size)))
    (segmentEq : wordAt source.memory (model.node+32#64)=segment)
    (sizeEq : wordAt source.memory (model.node+40#64)=size)
    (matched : size.toNat≤length.toNat-model.level.toNat)
    (normal : evaluateHOLFiniteState source extensionFrameScope=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  let words : String→BitVec 64:=fun name=>if name="top" then model.pending.top else if name="node" then model.node else if name="seg" then segment else if name="sl" then size else 0#64
  let record:=Arenas.resultWord .down model.pending.cursor 40#64
  have ready : ∀ field∈DeleteFrame.Kind.extension.fields words,field.value.Ready (QueryBranch.bind source "fr" record):=by
    intro field member
    simp only [DeleteFrame.Kind.fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl
    · exact (bind_lookup_other source "fr" "top" record (by decide)).trans model.pending.topCell
    · exact (bind_lookup_other source "fr" "node" record (by decide)).trans model.nodeCell
    · trivial
    · exact (bind_lookup_other source "fr" "seg" record (by decide)).trans segmentCell
    · exact (bind_lookup_other source "fr" "sl" record (by decide)).trans sizeCell
  have owned : DeleteFrame.Saved.Owned ⟨record,.extension,words⟩ model.pending.graph:=
    ⟨model.nodeMember,active,tag,segmentEq,sizeEq⟩
  exact descent_push_normal source target key length limit nodeLower pathLower property model .extension words rfl rfl ready owned
    (fun _=>matched) (by intro impossible; contradiction) normal

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_matched_output
