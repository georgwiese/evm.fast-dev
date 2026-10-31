import InitECandidate.Solver.Mpt.IndexedSetEntry
import InitECandidate.Solver.Mpt.SetEmptyDispatch
import InitECandidate.Solver.Mpt.InsertGeneralCallCost
import InitECandidate.Solver.Mpt.NibbleKeyCost
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Mpt.IndexedSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The genuine post-key suffix uses the actual owned query and selected
nonempty row. Its root load/store add no source call/loop clocks. -/
theorem Converted.suffix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {m pointer size : BitVec 64} {cutoff limit : Nat} {property : BitVec 64→BitVec 64→Prop}
    (data : Converted source m pointer size cutoff limit property) :
    source.clock-(evaluateHOLFiniteState source SetTrie.afterKey).2.clock≤36791 := by
  have mapped : source.memaddrs m:=by
    simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source m 16 0 data.domain data.headerArena (by decide) data.headerAligned (by decide)
  have read : eval source SetTrie.rootExpression=some (.val (.word data.root)):=by
    simp [eval,SetTrie.rootExpression,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,data.mCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,data.rootStored]
  rw [SetTrie.mutation_shapes.1]
  apply Input.ClockCost.declared_current source "root" SetTrie.rootExpression data.root SetTrie.afterRoot 36791 read
  let ready:=bind source "root" data.root
  have rootCell : ready.locals.lookup (ofString "root")=some (.val (.word data.root)):=bind_lookup_same _ _ _
  have nkCell : ready.locals.lookup (ofString "nk")=some (.rStruct [.val (.word data.key),.val (.word data.length)]):=
    (bind_lookup_other _ "root" "nk" data.root (by decide)).trans data.nkCell
  have pointerCell : ready.locals.lookup (ofString "vptr")=some (.val (.word pointer)):=
    (bind_lookup_other _ "root" "vptr" data.root (by decide)).trans data.pointerCell
  have sizeCell : ready.locals.lookup (ofString "vlen")=some (.val (.word size)):=
    (bind_lookup_other _ "root" "vlen" data.root (by decide)).trans data.sizeCell
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) SetTrie.insertArguments=
      some (Insert.values data.root data.key data.length 0#64 pointer size):=by
    simp [SetTrie.insertArguments,Insert.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootCell,nkCell,pointerCell,sizeCell]
  have price:=Insert.general_call_cost ready data.heap data.root data.key 0#64 data.length pointer size data.graph limit cutoff cutoff property
    data.values data.regions data.disjoint data.paths data.pathRegions data.separated data.query data.member
    (by simp) data.small data.payload data.extra data.empty data.floor data.domain data.installed data.heapCell data.heapArena data.heapAligned
    (some (some (ofString "root"))) SetTrie.insertArguments args
  rw [SetTrie.mutation_shapes.2.1]
  exact Input.ClockCost.sequence_current ready SetTrie.mutationChoice SetTrie.footer 36791 0
    (by rw [SetTrie.insert_selected ready pointer size pointerCell sizeCell data.pointerActive data.sizeActive]; exact price)
    (Input.ClockCost.of_quiet source.code _ (SetTrie.footer_quiet source.code))

/-- All outcomes of the current actual unsecured setter on a nonempty
indexed row, including failed allocations and short clocks. Only the actual
normal key call establishes the query used to price its reached suffix. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {m rawKey pointer size : BitVec 64} {byteLength cutoff limit : Nat} {property : BitVec 64→BitVec 64→Prop}
    (data : Entry source m rawKey byteLength pointer size cutoff limit property) :
    source.clock-(evaluateHOLFiniteState source SetTrie.body).2.clock≤36806 := by
  by_cases zero : source.clock=0
  · simp only [zero,Nat.zero_sub,Nat.zero_le]
  · obtain ⟨callee,called,mLocal,keyLocal,lengthLocal⟩:=NibbleKey.environment source.code.lookup m rawKey (BitVec.ofNat 64 byteLength)
      (NibbleKey.original_code source.code data.installed)
    have args:=SetTrie.key_arguments source m rawKey byteLength data.mCell data.keyCell data.lengthCell
    let entry:=callEntryStateHOLFinite source callee
    have mapped : entry.memaddrs (m+8#64):=by
      simpa only [byteAddress] using AllocatedBytes.word_mapped entry m 16 8 data.domain data.headerArena (by decide) data.headerAligned (by decide)
    have price:=NibbleKey.unsecured_cost entry m rawKey byteLength (by have small:=data.small; omega) data.installed
      mLocal keyLocal lengthLocal mapped data.flagStored
    have keyPrice : entry.clock-(evaluateHOLFiniteState entry NibbleKey.body).2.clock≤14:=by
      have small:=data.small
      omega
    have suffix (child : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
        (normal : evaluateHOLFiniteState entry NibbleKey.body=(some (.returned returned),child))
        (checked : (shapeEqHOL (shapeOfHOLExact returned) NibbleKey.returnShape && shapeEqHOL (shapeOfHOLExact returned) NibbleKey.returnShape)=true) :
        child.clock-(evaluateHOLFiniteState (Input.CallNormal.continuationEntry source child "nk" returned) SetTrie.afterKey).2.clock≤36791:=by
      let current:=Input.CallNormal.continuationEntry source child "nk" returned
      have reached : Input.CallPrefix.Reaches source (.scoped (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") SetTrie.keyArguments) current:=
        .scoped source (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") SetTrie.keyArguments _ NibbleKey.body callee NibbleKey.returnShape
          returned child args called zero normal checked
      obtain ⟨converted⟩:=data.after_key reached
      exact converted.suffix_cost
    rw [SetTrie.body_shape]
    exact Input.ClockCost.scoped_reached_current source "nk" NibbleKey.returnShape (ofString "mpt_nibble_key") SetTrie.keyArguments _ NibbleKey.body SetTrie.afterKey callee
      NibbleKey.returnShape 14 36791 args called keyPrice suffix

end InitECandidate.Solver.Mpt.IndexedSet

#print axioms InitECandidate.Solver.Mpt.IndexedSet.Converted.suffix_cost
#print axioms InitECandidate.Solver.Mpt.IndexedSet.body_cost
