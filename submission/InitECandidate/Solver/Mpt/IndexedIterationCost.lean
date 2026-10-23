import InitECandidate.Solver.Mpt.IndexedKeyModel
import InitECandidate.Solver.Mpt.IndexedSetModel
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every outcome of the unchanged indexed iteration: derive the key
model only after a genuine encoder return, price the actual selected-row
setter, then account for the real local increment. -/
theorem iteration_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property) (inside : model.index.toNat<count) :
    source.clock-(evaluateHOLFiniteState source loopBody).2.clock≤SetTrie.bodyAllowance cutoff+20 := by
  by_cases zero : source.clock=0
  · simp only [zero,Nat.zero_sub,Nat.zero_le]
  · have args:=key_arguments source model.index model.bindings model.indexCell
    obtain ⟨callee,called,d,w⟩:=Input.RlpWrite.WordWrite.environment source.code.lookup 2713717624#64 model.index (Input.OriginalRlp.rlp_encode_word source.code model.installed)
    have childPrice:=Input.RlpWrite.WordWrite.body_cost (callEntryStateHOLFinite source callee) 2713717624#64 model.index d w
      (Input.OriginalRlp.rlp_be_len source.code model.installed) (Input.OriginalRlp.rlp_put_be source.code model.installed) (key_buffer_mapped source model.domain)
    have suffix (childTarget : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
        (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) Input.RlpWrite.WordWrite.body=(some (.returned returned),childTarget))
        (checked : (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true) :
        childTarget.clock-(evaluateHOLFiniteState (Input.CallNormal.continuationEntry source childTarget "klen" returned) (.seq setCall advance)).2.clock≤SetTrie.bodyAllowance cutoff+1:=by
      let current:=Input.CallNormal.continuationEntry source childTarget "klen" returned
      have reached : Input.CallPrefix.Reaches source (.scoped (ofString "klen") .one (ofString "rlp_encode_word") keyArguments) current:=
        .scoped source _ _ _ _ _ Input.RlpWrite.WordWrite.body callee .one returned childTarget args called zero run checked
      obtain ⟨encoded,next,_positive,small,lengthCell,indexEq,_heapEq,_price,_frame⟩:=key_model source current m array count cutoff limit slices property model reached
      have active : next.index.toNat<count:=by rw [indexEq]; exact inside
      have setPrice:=set_cost current m array count cutoff limit slices property next active encoded small lengthCell
      have joined:=Input.ClockCost.sequence_reached_current current setCall advance (SetTrie.bodyAllowance cutoff+1) 0 setPrice (by
        intro middle continued
        exact Input.ClockCost.assign middle.code (ofString "i") (.op .add [localVar "i",.const 1#64]) middle rfl)
      exact joined
    rw [loop_body_shape]
    have price:=Input.ClockCost.scoped_reached_current source "klen" .one (ofString "rlp_encode_word") keyArguments _ Input.RlpWrite.WordWrite.body (.seq setCall advance) callee .one
      18 (SetTrie.bodyAllowance cutoff+1) args called childPrice suffix
    exact price.trans (by omega)

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.iteration_cost
