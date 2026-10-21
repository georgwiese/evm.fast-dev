import InitECandidate.Solver.Mpt.WitnessCoreBranchValueStores
import InitECandidate.Solver.Mpt.WitnessCoreMetadata
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every genuine normal final-value suffix passes the original unsigned
occupancy guard and performs the actual parent stores and record pop.
The parser's four returned words are current inputs, not assumed future
callee results. Its real caller derives them separately. -/
theorem after_branch_value_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node previous child pointer header bytes flag : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (valueCell : source.locals.lookup (ofString "bv")=some (Rlp.Item.result pointer header bytes flag))
    (previousCell : source.memory record=.word previous) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterBranchValue=(none,post)) :
    let entered:=QueryBranch.bind source "occ" (BitVec.ofNat 64 occupied.val)
    let ready:=branchValueState entered node pointer header bytes flag occupied
    2≤branchValueOccupied bytes flag occupied ∧
      post=restore source "occ" (metadataState ready node data.pointer data.length previous) := by
  have mapped : source.memaddrs (record+40#64):=by simpa only [byteAddress] using view.mapped source record db data 40 (by decide) (by decide)
  have stored : source.memory (record+40#64)=.word (BitVec.ofNat 64 occupied.val):=
    view.cells (40,BitVec.ofNat 64 occupied.val) (by simp [WitnessRecord.Description.cells,payload])
  have read : eval source (readAt "top" 40#64)=some (.val (.word (BitVec.ofNat 64 occupied.val))):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]
  rw [after_branch_value_shape] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.ScalarScope.declare_trace source post "occ" (readAt "top" 40#64)
    (BitVec.ofNat 64 occupied.val) branchValueBody none read normal
  let entered:=QueryBranch.bind source "occ" (BitVec.ofNat 64 occupied.val)
  let ready:=branchValueState entered node pointer header bytes flag occupied
  have enteredView:=view.of_fields source entered record db data rfl rfl
  have owned:=view.owned
  simp only [payload,WitnessRecord.Payload.Owned] at owned
  have enteredBranch : entered.locals.lookup (ofString "br")=some (.val (.word node)):=
    (bind_lookup_other source "occ" "br" _ (by decide)).trans branchCell
  have enteredValue : entered.locals.lookup (ofString "bv")=some (Rlp.Item.result pointer header bytes flag):=
    (bind_lookup_other source "occ" "bv" _ (by decide)).trans valueCell
  have writeRun:=branch_value_writes_execute entered node pointer header bytes flag occupied view.rows.domain owned.1 owned.2.1
    enteredBranch enteredValue (bind_lookup_same _ _ _)
  have clock : ready.clock≤entered.clock:=by unfold ready branchValueState; split; split <;> exact Nat.le_refl _; exact Nat.le_refl _
  rw [branch_value_body_shape,StateSteps.next_sequence entered ready _ _ writeRun clock] at continued
  have readyView:=branch_value_state_view entered record db node pointer header bytes flag data index occupied enteredView payload
  have readyCode : ready.code=source.code:=by unfold ready branchValueState; split; split <;> rfl; rfl
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by rw [readyCode]; exact installed
  rw [branch_finish_tail_shape] at continued
  obtain ⟨guardPost,guardRun,metadataRun⟩:=Input.sequence_none ready inner _ branchMetadata continued
  have same:=(Fail.guard_normal ready guardPost (.cmp .lower (localVar "occ") (.const 2#64)) [.const 9#64] readyInstalled guardRun).2
  subst guardPost
  have readyOccupied:=(branch_value_state_fields entered node pointer header bytes flag occupied (bind_lookup_same _ _ _)).1
  change ready.locals.lookup (ofString "occ")=some (.val (.word (BitVec.ofNat 64 (branchValueOccupied bytes flag occupied)))) at readyOccupied
  have occupiedRead : eval ready (localVar "occ")=some (.val (.word (BitVec.ofNat 64 (branchValueOccupied bytes flag occupied)))):=by
    simp [eval,evalHOLExact,localVar,toExact,readyOccupied]
  have twoRead : eval ready (.const 2#64)=some (.val (.word 2#64)):=rfl
  have lower:=Fail.lower_guard_bound ready ready (localVar "occ") (.const 2#64) _ 2#64 [.const 9#64]
    occupiedRead twoRead readyInstalled guardRun
  have upper:=branch_value_occupied_bound bytes flag occupied
  have number : (BitVec.ofNat 64 (branchValueOccupied bytes flag occupied)).toNat=branchValueOccupied bytes flag occupied:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have enough : 2≤branchValueOccupied bytes flag occupied:=by change 2≤(BitVec.ofNat 64 (branchValueOccupied bytes flag occupied)).toNat at lower; omega
  have readyTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=
    (branch_value_state_other entered node pointer header bytes flag occupied "top" (by decide)).trans
      ((bind_lookup_other source "occ" "top" _ (by decide)).trans topCell)
  have readyBranch : ready.locals.lookup (ofString "br")=some (.val (.word node)):=
    (branch_value_state_other entered node pointer header bytes flag occupied "br" (by decide)).trans enteredBranch
  have readyResult : ready.locals.lookup (ofString "result")=some (.val (.word child)):=
    (branch_value_state_other entered node pointer header bytes flag occupied "result" (by decide)).trans
      ((bind_lookup_other source "occ" "result" _ (by decide)).trans resultCell)
  have nodeLower : 2713731432≤node.toNat:=by simpa only [payload,WitnessRecord.Payload.startAddress] using view.payloadFloor
  have recordUpper:=view.ceiling
  have nodeUpper:=owned.1.upper
  have number160 : (node+160#64).toNat=node.toNat+160:=byteAddress_toNat node 160 (by omega)
  have number168 : (node+168#64).toNat=node.toNat+168:=byteAddress_toNat node 168 (by omega)
  have away160 : record≠node+160#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number160] at number; omega
  have away168 : record≠node+168#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number168] at number; omega
  have readyPrevious : ready.memory record=.word previous:=
    (branch_value_state_memory entered node pointer header bytes flag occupied record away160 away168).trans previousCell
  have executed:=parent_metadata_execute ready record db node previous child data 176 "br" readyView owned.1 (by decide) owned.2.1 nodeLower
    (by decide) readyTop readyBranch readyResult readyPrevious
  rw [branch_metadata_shape,executed] at metadataRun
  have innerEq : inner=metadataState ready node data.pointer data.length previous:=(congrArg Prod.snd metadataRun).symm
  exact ⟨enough,by rw [endpoint,innerEq]⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_branch_value_normal
