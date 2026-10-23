import InitECandidate.Solver.Mpt.DeleteDescentPushNormal

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original branch push saves its true parent and bounded index,
then follows the actual child and consumes precisely one key nibble. -/
theorem branch_push_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (index : Nat) (small : index<16)
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word (BitVec.ofNat 64 index))))
    (before : model.level.toNat<length.toNat)
    (normal : evaluateHOLFiniteState source branchFrameScope=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  let words : String→BitVec 64:=fun name=>if name="top" then model.pending.top else if name="node" then model.node else if name="idx" then BitVec.ofNat 64 index else 0#64
  let record:=Arenas.resultWord .down model.pending.cursor 40#64
  have ready : ∀ field∈DeleteFrame.Kind.branch.fields words,field.value.Ready (QueryBranch.bind source "fr2" record):=by
    intro field member
    simp only [DeleteFrame.Kind.fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact (bind_lookup_other source "fr2" "top" record (by decide)).trans model.pending.topCell
    · exact (bind_lookup_other source "fr2" "node" record (by decide)).trans model.nodeCell
    · trivial
    · exact (bind_lookup_other source "fr2" "idx" record (by decide)).trans indexCell
  have owned : DeleteFrame.Saved.Owned ⟨record,.branch,words⟩ model.pending.graph:=by
    refine ⟨model.nodeMember,active,tag,?_⟩
    change (BitVec.ofNat 64 index).toNat<16
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact small
  exact descent_push_normal source target key length limit nodeLower pathLower property model .branch words rfl rfl ready owned
    (by intro impossible; contradiction) (fun _=>before) normal

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_push_output
