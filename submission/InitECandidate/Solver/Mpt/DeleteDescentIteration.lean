import InitECandidate.Solver.Mpt.DeleteDescentAfterHash
import InitECandidate.Solver.Mpt.DeleteDescentNull

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real node choice either stops at null or enters its genuine k
declaration, skips the hash failure only on an actual normal run, and
joins invalidation and the selected original case before restoring k. -/
theorem node_choice_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (empty : property 0#64 0#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source nodeChoice=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  by_cases null : model.node=0#64
  · exact null_node_output source target key length limit nodeLower pathLower property model null stopped normal
  · let tag:=wordAt source.memory model.node
    obtain ⟨inner,continued,endpoint⟩:=nonnull_entry source target key length limit nodeLower pathLower property model null normal
    let enteredState:=QueryBranch.bind source "k" tag
    let entered:=model.bind_auxiliary source key length limit nodeLower pathLower property "k" tag (by decide)
    have tagCell : enteredState.locals.lookup (ofString "k")=some (.val (.word tag)):=bind_lookup_same _ _ _
    obtain ⟨notHash,afterGuard⟩:=after_kind_entry enteredState inner tag tagCell entered.pending.installed continued
    obtain ⟨output⟩:=after_hash_output enteredState inner key length tag limit nodeLower pathLower property entered null tagCell rfl notHash empty stopped afterGuard
    rw [endpoint]
    exact DescentOutput.restore_auxiliary source inner key length limit nodeLower pathLower property model "k" tag (by decide) output

/-- A whole actual descent iteration first clears go, then derives the
complete selected-case result. Every continuing iteration either stops
or strictly consumes key nibbles, while preserving its physical stack. -/
theorem descent_iteration_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (empty : property 0#64 0#64)
    (normal : evaluateHOLFiniteState source descentBody=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  rw [descent_shapes.2.1] at normal
  obtain ⟨middle,cleared,continued⟩:=Input.sequence_none source target _ _ normal
  have actual:=clear_go_execute source key length limit nodeLower pathLower property model
  have middleEq : middle=QueryBranch.bind source "go" 0#64:=congrArg Prod.snd (cleared.symm.trans actual)
  subst middle
  let current:=model.clear_go source key length limit nodeLower pathLower property
  obtain ⟨output⟩:=node_choice_output (QueryBranch.bind source "go" 0#64) target key length limit nodeLower pathLower property current empty rfl continued
  exact ⟨{output with next:=output.next}⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.node_choice_output
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_iteration_normal
