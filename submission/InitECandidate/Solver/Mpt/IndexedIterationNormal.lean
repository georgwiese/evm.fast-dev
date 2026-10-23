import InitECandidate.Solver.Mpt.IndexedIterationCost
import InitECandidate.Solver.Mpt.IndexedModelErase
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_body_saved (name : MlS) (notKey : name≠ofString "klen") (notIndex : name≠ofString "i") :
    Input.LocalPrefix name loopBody := by
  rw [loop_body_shape]
  exact .decCall _ _ _ _ notKey (.seq (.call none _ _ (by intro other equal; cases equal)) (.assign _ _ notIndex))

/-- The complete real iteration derives its bounded next counter and
full grown trie/map/row model from the actual encoder, setter, local
increment and lexical restoration. -/
theorem iteration_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property) (inside : model.index.toNat<count)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ next : LoopModel target m array count cutoff limit slices property,
      next.index=model.index+1#64 ∧ model.heap.toNat≤next.heap.toNat ∧
      (∀ query : BitVec 64,2713731432≤query.toNat→query.toNat<cutoff→target.memory query=source.memory query) := by
  have args:=key_arguments source model.index model.bindings model.indexCell
  obtain ⟨callee,called,d,w⟩:=Input.RlpWrite.WordWrite.environment source.code.lookup 2713717624#64 model.index (Input.OriginalRlp.rlp_encode_word source.code model.installed)
  have shaped:=normal
  rw [loop_body_shape] at shaped
  obtain ⟨funded,childTarget,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none source target "klen" .one (ofString "rlp_encode_word") keyArguments _
    Input.RlpWrite.WordWrite.body (.seq setCall advance) callee .one args called shaped
  let current:=Input.CallNormal.continuationEntry source childTarget "klen" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "klen") .one (ofString "rlp_encode_word") keyArguments) current:=
    .scoped source _ _ _ _ _ Input.RlpWrite.WordWrite.body callee .one returned childTarget args called (by omega) run checked
  obtain ⟨encoded,keyModel,_positive,small,lengthCell,indexEq,heapEq,_price,keyFrame⟩:=key_model source current m array count cutoff limit slices property model reached
  obtain ⟨afterSet,setRun,advanceRun⟩:=Input.sequence_none current inner setCall advance continued
  obtain ⟨setModel,setIndex,grows,_setPrice,setFrame⟩:=set_model current afterSet m array count cutoff limit slices property keyModel (by rw [indexEq]; exact inside) encoded small lengthCell setRun
  have assignment:=Input.LocalEffects.assign afterSet.code (ofString "i") (.op .add [localVar "i",.const 1#64]) afterSet rfl
  change Input.LocalEffects.erase (evaluateHOLFiniteState afterSet advance).2=Input.LocalEffects.erase afterSet at assignment
  rw [advanceRun] at assignment
  have frame : Input.LocalEffects.erase target=Input.LocalEffects.erase afterSet:=by rw [endpoint]; exact assignment
  have nextIndex:=loop_body_advance source target model.index model.indexCell normal
  have number : (model.index+1#64).toNat=model.index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change model.index.toNat+1<2^64; have bounded:=model.countBound; omega)]; rfl
  have saved (name : MlS) (notKey : name≠ofString "klen") (notIndex : name≠ofString "i") : target.locals.lookup name=source.locals.lookup name:=by
    have summary:=(loop_body_saved name notKey notIndex).summary_full source
    unfold Input.LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  obtain ⟨next,nextEq,nextHeap⟩:=setModel.of_erase afterSet target m array (model.index+1#64) count cutoff limit slices property frame nextIndex (by rw [number]; omega)
    ((saved (ofString "n") (by decide) (by decide)).trans model.countCell)
    ((saved (ofString "m") (by decide) (by decide)).trans model.mCell)
    ((saved (ofString "slice_arr") (by decide) (by decide)).trans model.arrayCell)
  exact ⟨next,nextEq,(by rw [nextHeap,←heapEq]; exact grows),by
    intro query above before
    exact (congrFun (Input.LocalEffects.memory_of_erase afterSet target frame) query).trans ((setFrame query above before).trans (keyFrame query above before))⟩

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.loop_body_saved
#print axioms InitECandidate.Solver.Mpt.Indexed.iteration_normal
